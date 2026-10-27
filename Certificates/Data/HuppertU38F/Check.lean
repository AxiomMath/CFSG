module

public import CFSG.LieType.SeitzGeneration.HeisSmallCheck
public import CFSG.LieType.SeitzGeneration.HeisSmallModel

public section

namespace HuppertU38F

open CFSG.LieType.SeitzGeneration.HeisSmall

@[expose] def w0 : Q8 := QExt.omega

@[expose] def l4 : List Q8 := [0, 1, w0, w0 * w0]

@[expose] def f4nz : List Q8 := [1, w0, w0 * w0]

@[expose] def entriesL4 (A : M3 Q8) : Bool :=
  decide (A.a00 ∈ l4 ∧ A.a01 ∈ l4 ∧ A.a02 ∈ l4 ∧ A.a10 ∈ l4 ∧ A.a11 ∈ l4 ∧ A.a12 ∈ l4 ∧
    A.a20 ∈ l4 ∧ A.a21 ∈ l4 ∧ A.a22 ∈ l4)

@[expose] def unitaryOk (A : M3 Q8) : Bool := decide ((A.map (· ^ 8)).transpose * A = 1)

@[expose] def sgOk (A : M3 Q8) : Bool := decide (A.det = 1) && unitaryOk A

@[expose] def commutes (A B : M3 Q8) : Bool := decide (A * B = B * A)

@[expose] def isScalar (A : M3 Q8) : Bool :=
  decide (A.a01 = 0 ∧ A.a02 = 0 ∧ A.a10 = 0 ∧ A.a12 = 0 ∧ A.a20 = 0 ∧ A.a21 = 0 ∧
    A.a11 = A.a00 ∧ A.a22 = A.a00)

@[expose] def gstar (A : M3 Q8) : M3 Q8 := (A.map (· ^ 8)).transpose

abbrev Col : Type := Q8 × Q8 × Q8

@[expose] def ofCols (c₀ c₁ c₂ : Col) : M3 Q8 :=
  ⟨c₀.1, c₁.1, c₂.1, c₀.2.1, c₁.2.1, c₂.2.1, c₀.2.2, c₁.2.2, c₂.2.2⟩

@[expose] def ip (c d : Col) : Q8 := c.1 ^ 8 * d.1 + c.2.1 ^ 8 * d.2.1 + c.2.2 ^ 8 * d.2.2

@[expose] def cols4 : List Col :=
  l4.flatMap fun a => l4.flatMap fun b => l4.map fun c => (a, b, c)

@[expose] def stage1 (c₀ : Col) : Bool := decide (ip c₀ c₀ = 1)

@[expose] def stage2 (c₀ c₁ : Col) : Bool := decide (ip c₁ c₁ = 1 ∧ ip c₀ c₁ = 0)

@[expose] def stage3 (c₀ c₁ c₂ : Col) : Bool :=
  decide (ip c₂ c₂ = 1 ∧ ip c₀ c₂ = 0 ∧ ip c₁ c₂ = 0)

@[expose] def forallUnitary (P : M3 Q8 → Bool) : Bool :=
  cols4.all fun c₀ => !(stage1 c₀) || cols4.all fun c₁ => !(stage2 c₀ c₁) ||
    cols4.all fun c₂ => !(stage3 c₀ c₁ c₂) || P (ofCols c₀ c₁ c₂)

@[expose] def guList : List (M3 Q8) :=
  cols4.flatMap fun c₀ => if stage1 c₀ then
    cols4.flatMap fun c₁ => if stage2 c₀ c₁ then
      cols4.filterMap fun c₂ => if stage3 c₀ c₁ c₂ then some (ofCols c₀ c₁ c₂) else none
    else [] else []

@[expose] def orbitOf (gu : List (M3 Q8)) (Y : M3 Q8) : List (M3 Q8) :=
  gu.flatMap fun g => f4nz.map fun l => M3.smul l (g * Y * gstar g)

@[expose] def classOk (orbs : List (List (M3 Q8))) (A : M3 Q8) : Bool :=
  isScalar A || !(isScalar (A * A * A)) || orbs.any fun o => decide (A ∈ o)

structure U38Entry where
  Y : M3 Q8
  gens : List (M3 Q8)
  words : List (List ℕ)

@[expose] def u38EntryOk (letters : List (M3 Q8)) (e : U38Entry) : Bool :=
  e.gens.all (fun G => sgOk G && (entriesL4 G || commutes G e.Y)) &&
    decide (e.words.map (evalW e.gens) = letters)

@[expose] def u38Check (letters : List (M3 Q8)) (words2 : List (List ℕ))
    (table : List U38Entry) : Bool :=
  let gu := guList
  gu.all (fun g => unitaryOk g && entriesL4 g) &&
    coverBool 8 (words2.map (evalW letters)) && table.all (u38EntryOk letters) &&
      forallUnitary (classOk (table.map fun e => orbitOf gu e.Y))

end HuppertU38F
