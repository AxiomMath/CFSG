module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusData
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusMinor
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusCoeff
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusSeventeen
import CFSG.LocalAnalysis.SectionRank.QTK.EvenMinus8

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open scoped Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
  (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

private theorem o8mSI_seventeen_le_of_single {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK : Nat.card K = 2)
    {k : Type} [Field k] [CharP k 2] {V : Type} [AddCommGroup V] [Module k V]
    [Module.Finite k V] {ρ : Representation k (spinGroup (quadMinus 4 K b c)) V}
    (hρ : IsSimpleRep ρ) {y : V} {χ : spinGroup (quadMinus 4 K b c) → k} {μ : Fin 3 → k}
    (ht : (o8mDatum hirrQ).IsCurtisType ρ y χ μ) (hχ : ∀ h ∈ (o8mDatum hirrQ).H, χ h = 1)
    {i : Fin 3} (hi : i ≠ 0)
    (hμi : ∀ j, μ j = if j ∈ ({i} : Finset (Fin 3)) then 1 else 0) :
    17 ≤ Module.finrank k V := by
  obtain ⟨rfl, rfl⟩ := CFSG.SectionRank.QTK.eq_one_of_irreducible_of_card_two hK hirrQ
  let φ : K →+* k := (ZMod.castHom (dvd_refl 2) k).comp
    (CFSG.Monster.Existence.Compat.ringEquivZMod2 hK).toRingHom
  obtain ⟨f, hf, hfy⟩ := (o8mDatum hirrQ).exists_form hρ ht.1 ht.2.1
  obtain ⟨a, h, hdet⟩ := o8m_seventeen_det_ne_zero (k := k) φ (i := i) hi
  have hentry : ∀ r c : Fin 17, f (ρ (a r) (ρ (h c) y)) =
      φ (o8mMinor i (mat 4 (a r * h c))) := by
    intro r c
    rw [show ρ (a r) (ρ (h c) y) = ρ (a r * h c) y by
      rw [map_mul, Module.End.mul_apply]]
    rw [o8mDatum_form_eq_minorProd hirrQ hK φ ht hχ hμi hf hfy (a r * h c), o8mMinorProd,
      Finset.prod_singleton]
  have hmat : (Matrix.of fun r c => (f.comp (ρ (a r))) (ρ (h c) y)) =
      Matrix.of fun r c => φ (o8mMinor i (mat 4 (a r * h c))) := by
    ext r c
    exact hentry r c
  rw [← hmat] at hdet
  exact o8m_card_le_finrank_of_det_ne_zero (fun c => ρ (h c) y)
    (fun r => f.comp (ρ (a r))) hdet

theorem omMinus_two_seventeen_le_finrank_of_single (hK : Nat.card K = 2) {k : Type} [Field k]
    [CharP k 2] {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    {ρ : Representation k (spinGroup (quadMinus 4 K b c)) V} (hρ : IsSimpleRep ρ) {y : V}
    {χ : spinGroup (quadMinus 4 K b c) → k} {μ : Fin 3 → k}
    (ht : (o8mDatum hirrQ).IsCurtisType ρ y χ μ) (hχ : ∀ h ∈ (o8mDatum hirrQ).H, χ h = 1)
    (hμ : μ = Pi.single 1 1 ∨ μ = Pi.single 2 1) :
    17 ≤ Module.finrank k V := by
  rcases hμ with hμ | hμ
  · refine o8mSI_seventeen_le_of_single hirrQ hK hρ ht hχ (i := 1) (by decide +kernel) ?_
    rw [hμ]
    intro j
    simp [Pi.single_apply]
  · refine o8mSI_seventeen_le_of_single hirrQ hK hρ ht hχ (i := 2) (by decide +kernel) ?_
    rw [hμ]
    intro j
    simp [Pi.single_apply]

end CFSG.LocalAnalysis.WeakClosure81
