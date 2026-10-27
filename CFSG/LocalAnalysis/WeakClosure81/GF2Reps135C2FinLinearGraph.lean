module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinLinearLabel

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar CFSG.LieType.SpecialLinear

theorem false_of_borelStd_one_intertwiner {K : Type} [Field K] [Fintype K] [CharP K 2]
    (hK : Fintype.card K = 2) {n : ℕ} (hn : 6 ≤ n) {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin n) K) W)
    (hirr : ρ.IsIrreducible) (hne : ∃ x, ρ x ≠ 1) {D : ℕ} (hcard : Nat.card W = 2 ^ D)
    (horb : ∀ S : Finset (Fin n), (⟨0, by omega⟩ : Fin n) ∉ S → S ≠ ∅ →
      (∀ (j : Fin n) (hj : 1 ≤ j.val), (j ∈ S ↔ (⟨n - j.val, by omega⟩ : Fin n) ∈ S)) →
        D < orbitSize S)
    {d : W ≃ₗ[ZMod 2] W} {B : Matrix.GeneralLinearGroup (Fin n) K} (hB : IsUpperGL B)
    {τ : K ≃+* K} (hd2 : d * d = 1)
    (hd : ∀ (x : Matrix.SpecialLinearGroup (Fin n) K) (w : W),
      d (ρ x w) = ρ (borelStd n K B τ 1 x) (d w)) : False := by
  obtain ⟨S, h0, hS, hcardS, -, -, hsym⟩ :=
    exists_label_of_irreducible_specialLinear hK (by omega) ρ hirr hne
  have hsymS := hsym ⟨d, B, τ, hB, hd2, hd⟩
  have h1 := horb S h0 hS hsymS
  rw [hcard] at hcardS
  have h2 : orbitSize S ≤ D := (Nat.pow_le_pow_iff_right (by norm_num)).1 hcardS
  omega

end CFSG.LocalAnalysis.WeakClosure81
