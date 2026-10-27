module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallModel
public import Certificates.Data.CFSGNative.TwoNodeSmall.CorePos

public section

namespace CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def ModelledIn (L : List SPt) (s p : ℕ) {V : Type} [AddCommGroup V] [Module (ZMod p) V] {n : ℕ}
    (h : Fin n → V) (α : Fin n → Module.Dual (ZMod p) V) (x : V) (ha : V)
    (αa : Module.Dual (ZMod p) V) : Prop :=
  ∃ (D nF : ℕ) (gens : List Refl) (x' : Vec) (b : ℕ), (⟨⟨p, D, nF, gens, x', b⟩, s⟩ : SPt) ∈ L ∧
    ∃ c : ZMod p, c ≠ 0 ∧ ∃ e : V ≃ₗ[ZMod p] (Fin D → ZMod p),
      (⟨p, D, nF, gens, x', b⟩ : Pt).Models e h α (c • x) ha αa

theorem natFact_eq (n : ℕ) : natFact n = Nat.factorial n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [natFact, ih, Nat.factorial_succ]

theorem posBound_eq (p N : ℕ) : posBound p N = p ^ N * (6 * (p - 1) * Nat.factorial N) := by
  rw [posBound, natFact_eq]

end CFSG.TwoNodeSmall
