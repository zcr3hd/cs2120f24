import «Cs2120f24».Lectures.«02_prop_logic».formal.syntax
import «Cs2120f24».Lectures.«02_prop_logic».formal.semantics
import «Cs2120f24».Lectures.«02_prop_logic».formal.model_theory.properties

/-!
CS 2120-002 F24 Homework #1: Propositional Logic
-/

namespace cs2120f24.lecture.prop_logic

open PLExpr


/-!
First, we define three propositional variables: Wet, Rain, and
Sprink, following the exmaple presented in class, with shorter
but still suggestive variable names, for ease of reading and
writing propositional logic expressions -- aka "propositions."

Your first task is to be sure you understand the notation we're
using. Consider the first line below:

def wet : PLExpr := {⟨0⟩}.

We break that down here. *Study this material.* It's not very
difficult, and you really do need to understand this notation
easily going forward.

def       -- keyword to bind name (wet) to a value (here {⟨0⟩})
: PLExpr  -- defines the type of value to be bound (here, PLExpr)
:=        -- separates "variable type declaration" from value
⟨ 0 ⟩     -- Lean-defined shorthand for (BoolExpr.mk 0)
{ ... }   -- our concrete syntax for PLExpr.var_expr.mk

The parts here that might cause some conflusion are ⟨ _ ⟩ and
{ _ }. First, the funny angle brackets are not on your keyboard;
they are special characters you need to enter in VSCode using
\< and \>. Enter these strings then a space to get these
characters. Second, a "structure" type in Lean is an inductive
type with *just one constructor* that defaults in name to "mk".
An example is BoolVar.mk. Rather than typing that constructor
expression each time you want a new value *of *any* structure
type), you can use this this angle bracket notation instead.
Lean just has to be able to figure out from context what type
of object is needed so that it can translate ⟨ ⟩ into a call
to the "mk" constructor for the right structure type.

Next, the {...} notation is a concrete syntax notation that we
ourselves have defined (in syntax.lean) for PLExpr.var_expr. It
in turn expects a BoolVar argument, which is how Lean know what
constructor to use for the ⟨_⟩ notation: namely BoolVar.mk.

The reading should help with the ⟨_⟩ notation. And you should be
able to understand how we've defined { } as a concrete syntax in
syntax.lean.
-/


def wet : PLExpr := {⟨0⟩}
def rain : PLExpr := {⟨1⟩}
def sprink : PLExpr := {⟨2⟩}


/-!
ENGLISH TO FORMAL PROPOSITIONAL LOGIC

Problem #1: 50 points. Using the variable names, wet, rain,
and sprink, write propositional logic expressions for each of
the given propositions (expressions) written in natural language.
For example, "it's raining and the springler is running" would be
(rain ∧ sprink). Wtite your expressions in place of the sorrys.

Once you've written your expression, add a line of "code" to
check your expressions for *validity*. Then, if the expression
is *not* valid, in English explain very briefly a situation in
which the proposition is not true. For example, you know that
raining ∧ sprinking is not valid, and in this case it would be
ok to write "if it's not raining then this proposition is false"
-/

/-!
A. It's raining and the sprinkler is running.
-/
def formal_0 : PLExpr := rain ∧ sprink
#eval! is_valid formal_0
/- If either is false than the proposition is false-/


/-!
B. If it's raining then it's raining or the sprinkler's running.
Rememver to use \=> for the implies "connective" (expression
builder).
-/
def formal_1  : PLExpr := rain ⇒ rain ∨ sprink
#eval! is_valid formal_1

/- Since rain is already true, rain or sprink must be true, making the expression valid-/

/-!
C. If the sprinkler's running then it's raining or it's sprinkling.
-/
def formal_2  : PLExpr := sprink ⇒ rain ∨ sprink
#eval! is_valid formal_2

/- This expresion is valid for the same reason previous, expect with sprink-/



/-!
D. Whenever it's raining the streets are wet. You can express the same
idea as "if it's raining then the streets are wet." Be sure you see that
these two English-language phrases mean the same thing. You will want to
use the "whenever" form sometimes and the "if then" form sometimes when
writing logic in English.
-/
def formal_3  : PLExpr := rain ⇒ wet
#eval! is_valid formal_3

/- This expression is not valid because the street being wet does not imply that it is raining -/


/-!
E. Whenever the sprinkler's running the streets are wet.
-/
def formal_4 : PLExpr := sprink ⇒ wet
/- This expression is not valid because the street being wet does not imply that it is raining -/
#eval! is_valid formal_4

/- This expression is not valid because the street being wet does not imply that it is sprinkling -/


/-!
Here's an example, from class, of a proposition built up in
part from several smaller *implies* propositions. This is a
reminder to help you with any similar cases that follow.

If it's raining or the sprinkler's running, then if whenever
it's raining then the streets are wet, then if whenever the
sprinkler's running then the streets are wet, then the streets
are wet.

Add a check for the validity of this expression. The *example*
keyword in Lean asks Lean to check a term without binding a
name to it.
-/
def formal_x : PLExpr :=
  (rain ∨ sprink) ⇒
  (rain ⇒ wet) ⇒
  (sprink ⇒ wet) ⇒
  wet


-- Write your validity check here


/-!
If (whenever it's raining, the streets are wet), then (whenever the
streets are wet it's raining.)
-/
def formal_5 : PLExpr := (rain ⇒ wet) ⇒ (wet ⇒ rain)
#eval! is_valid formal_5

-- This statement is invalid because it is a combination of formal3 and formal4, two invalid statements cannot make a valid statement. Same reasoning as above.


/-!
If (whever it's raining then bottom)/false, then (it's not raining).
-/
def formal_7  : PLExpr := (rain ⇒ ⊥) ⇒ ¬rain
#eval! is_valid formal_7

--This statment is valid because of it is basically saying that if False than False, and if Not False (True), than True. Making it a valid statement.


/-!
If whenever it's raining the streets are wet, then whenever it's not
raining the streets are not wet.
-/
def formal_8 : PLExpr := (rain ⇒ wet) ⇒ ((¬rain) ⇒ (¬wet))
#eval! is_valid formal_8

--This statement is invalid because the streets not being wet does not logically imply that it is not raining.


/-!
If whenever it's raining the streets are wet, then whenever the
streets are not wet, it's not be raining.
-/
def formal_9 : PLExpr := (rain ⇒ wet) ⇒ (¬wet ⇒ ¬rain)
#eval! is_valid formal_9

--This statment is valid because we know that because raining always makes the streets wet, whenever the streets are not wet, than its not raining.



/-!
PROPOSITIONAL LOGIC TO ENGLISH: 50 points

For each of the following propositions in propositional logic,
open up some space after the proposition, in a comment block
give a corresponding English-language form of that proposition;
then *think* about whether the proposition is valid or not; and
add a validity check using our validity checker (this is already done for me so I didnt do it). Finally, if
a proposition is not valid, in English describe a case where
the proposition is not true. Notice but don't worry (yet) about
the funny names we assign to these propositions.
-/

def and_intro := sprink ⇒ rain ⇒ sprink ∧ rain
--Whenever the sprinklers are on then it is raining if the sprinklers are on and its raining.
-- This argument is valid because of the propositions are implied if the sprinklers are on and its raining
def and_elim_left := sprink ∧ rain ⇒ sprink
--If it is sprinkling and raining than it must be sprinking
-- If both expressions are true, than the conclusion must be true (and)
def and_elim_right := sprink ∧ rain ⇒ rain
--If it is raining and sprinkling, than it must be raining
-- If both expressions are true, than the conclusion must be true (and)


def or_intro_left := sprink ⇒ sprink ∨ rain
--If it is sprinkling, than it must be sprinkling or raining
--Is valid because if it is sprinkling than it must be sprinkling or raining

def or_intro_right :=  rain ⇒ sprink ∨ rain
--If it is raining, than it must be sprinkling or raining
--Is valid because if it is raining than it must be sprinkling or raining (T = T or F)


def or_elim := rain ∨ sprink ⇒ (rain ⇒ wet) ⇒ (sprink ⇒ wet) ⇒ wet
--If it is sprinkling or raining, then it must be (raining therefore the street is wet) then it must be (sprinking therefore the street is wet) therefore the street is wet.
-- The street will be wet if it is sprinkling or raining, therefore the street will always be wet given the implications. Making the argument valid.

def not_intro := (sprink ⇒ ⊥) ⇒ ¬sprink
--If (whever it's sprinkling then bottom)/false, then (it's not sprinkling).
--Because both sides are equivalent, the argument will always be valid.

def not_elim := ¬¬sprink ⇒ sprink
-- If the sprinklers are not(not sprinkling) than it will be sprinking
-- Because of double negation, the argument is if (!F=T), being True


def imp_intro := sprink ⇒ wet ⇒ (sprink ⇒ wet)
--If the sprinklers are on, than the street is wet, than (sprinklers on, therefore street wet)
-- This is valid because it is a restatemnt of the implication

def imp_elim := (sprink ⇒ wet) ⇒ sprink ⇒ wet
-- If the sprinklers being on implies the street is wet, and the sprinklers are on, then the street is wet.
--This is valid because if the implication (sprinklers ⇒ wet) holds and sprinklers are on, the conclusion (wet) must also hold.

def equiv_intro := (sprink ⇒ wet) ⇒ (wet ⇒ sprink) ⇒ (sprink ↔ wet)
-- If the (sprinklers on than its wet), then (the street is wet when the sprinklers are on), therefore (sprinklers are on and only on if the street is wet)
-- This is valid because if both implications are true than the bi-conditional is correct
def equiv_elim_left := (sprink ↔ wet) ⇒ (sprink ⇒ wet)
-- If the (sprinklers are on and only on when the street is wet) than the sprinklers are on if the street is wet.
-- This is valid because the sprinklers being on must mean that the street is wet.

def equiv_elim_right := (sprink ↔ wet) ⇒ (wet ⇒ sprink)
-- If the (sprinklers are on and only on when the street is wet), then when the street is wet it must be sprinkling
-- This is invalid because it assumes that the street can only be wet if the sprinklers are on, which is false.

def affirm_disjunct := (wet ∨ sprink) ⇒ wet ⇒ ¬sprink
-- If it is (wet or sprinkling) than it must be wet therefore it is not sprinkling.
-- This statement is invalid because it could be sprinkling and still be wet therefore (¬ sprinkling) is invalid.

def affirm_consequent := (sprink ⇒ wet) ⇒ wet ⇒ sprink
-- If it is (sprinkling than it is wet) then it is wet therefore it is sprinkling
-- This statement is invaid because it is a reverse implication, which is False

def deny_antecedent := (sprink ⇒ wet) ⇒ ¬sprink ⇒ ¬wet
-- If it is (sprinkling therefore it is wet), then it is not sprinkling, therefore it is not wet
-- This statement is invalid for the same reason as above, but negated.



/-
Are they valid?
-/

#eval! is_valid  and_intro
#eval! is_valid  and_elim_left
#eval! is_valid  and_elim_right

#eval! is_valid  or_intro_left
#eval! is_valid  or_intro_right
#eval! is_valid  or_elim

#eval! is_valid  not_intro
#eval! is_valid  not_elim

#eval! is_valid  imp_intro
#eval! is_valid  imp_elim

#eval! is_valid  equiv_intro
#eval! is_valid  equiv_elim_left
#eval! is_valid  equiv_elim_right

#eval! is_valid  affirm_disjunct
#eval! is_valid  affirm_consequent
#eval! is_valid  deny_antecedent

end cs2120f24.lecture.prop_logic
