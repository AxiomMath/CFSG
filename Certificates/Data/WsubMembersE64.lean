module

public import Certificates.Data.GH74.AE117

public section

namespace Certificates.WsubMembersE64

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr Certificates.AE117

@[expose] def blockOf : Fin 6 → ℕ := ![0, 0, 1, 2, 2, 1]

@[expose] def blk (k : ℕ) : Wr 6 :=
  ⟨fun i => if k.testBit (blockOf i) then 1 else 0,
    (if k.testBit 3 then Equiv.swap 0 1 else 1) * (if k.testBit 4 then Equiv.swap 2 5 else 1) *
      (if k.testBit 5 then Equiv.swap 3 4 else 1)⟩

@[expose] def a0List (_ : Unit := ()) : List (Wr 6) := (List.range 64).map blk

@[expose] def e64B (A : List (Wr 6)) : Bool :=
  decide (A.length = 64) && decide A.Nodup &&
    A.all (fun a => A.all fun b => decide (a * b ∈ A) && decide (a * b = b * a)) &&
    A.all fun a => decide (a * a = 1) && decide (wsum a = 0)

@[expose] def conjToB (s : Wr 6) (L L' : Finset (Fin 6) × Bool) : Bool :=
  (memAtL L'.1 L'.2).all (fun x => decide (s * x * s⁻¹ ∈ memAtL L.1 L.2)) &&
    (memAtL L.1 L.2).all fun y => decide (s⁻¹ * y * s ∈ memAtL L'.1 L'.2)

@[expose] def permB (s : Wr 6) : Bool :=
  decide (∀ L : Finset (Fin 6) × Bool, L.1.card = 4 →
    ∃ L' : Finset (Fin 6) × Bool, L'.1.card = 4 ∧ conjToB s L L' = true)

@[expose] def distinctB (_ : Unit := ()) : Bool :=
  decide (∀ L₁ L₂ : Finset (Fin 6) × Bool, L₁.1.card = 4 → L₂.1.card = 4 →
    (memAtL L₁.1 L₁.2).all (fun x => decide (x ∈ memAtL L₂.1 L₂.2)) = true → L₁ = L₂)

@[expose] def normB (A : List (Wr 6)) (L : Finset (Fin 6) × Bool) : Bool :=
  (memAtL L.1 L.2).all fun x => A.all fun a => decide (x * a * x⁻¹ ∈ A) && decide (x⁻¹ * a * x ∈ A)

@[expose] def countB (A : List (Wr 6)) : Bool :=
  decide ((Finset.univ.filter fun L : Finset (Fin 6) × Bool =>
    L.1.card = 4 ∧ normB A L = true).card = 6)

@[expose, noinline] def checkWith (A : List (Wr 6)) : Bool :=
  e64B A && decide (∀ v : Fin 6 → ZMod 2, wsum (⟨v, 1⟩ : Wr 6) = 0 → permB ⟨v, 1⟩ = true) &&
    decide (∀ i : Fin 5, permB ⟨0, Equiv.swap i.castSucc i.succ⟩ = true) && distinctB () &&
    countB A

@[expose] def wsubCheck (_ : Unit := ()) : Bool := checkWith (a0List ())

end Certificates.WsubMembersE64
