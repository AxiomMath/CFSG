module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bOmega4
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.Perfect
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.PlusTwoNotPerfect
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatParMax.Transport
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatParMax.ProdOvergroups
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatParMax.ProdFactors
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatParMax.ProdComponents

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatParMax

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.GroupTheory
open scoped commutatorElement

theorem two_le_of_natOmegaPlusFour {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {n : ℕ}
    (h : NatOmegaPlus H ⊤ ⊥ 4 n) (hperf : ⁅H, H⁆ = H) : 2 ≤ n := by
  obtain ⟨-, K, hField, hFinite, hK, hR⟩ := h
  letI : Field K := hField
  letI : Finite K := hFinite
  rw [show 4 / 2 = 2 by norm_num] at hR
  rcases n with _ | _ | k
  · rw [pow_zero] at hK
    have := Finite.one_lt_card (α := K)
    omega
  · rw [pow_one] at hK
    have htop : commutator ↥(StatedOmega (StatedQuadPlus 2 K)) = ⊤ :=
      KTabA.commutator_eq_top_of_realizes hR hperf
    exact absurd htop (KTabA.commutator_statedOmega_plus_two_ne_top hK)
  · omega

private lemma normalizer_sylow_le_subgroupOf_M09 {W : Type} [CommGroup W]
    {H S X : Subgroup (MulAut W)} (hS : IsSylowIn 2 S H)
    (hXge : H ⊓ stabSub (fixV S) ≤ X) :
    Subgroup.normalizer ((hS.toSylow : Sylow 2 ↥H) : Set ↥H) ≤ X.subgroupOf H := by
  intro y hy
  show (y : MulAut W) ∈ X
  refine hXge ((inf_normalizer_le_inf_stabSub H S) ?_)
  refine Subgroup.mem_inf.2 ⟨y.2, ?_⟩
  have hy' : y ∈ Subgroup.normalizer ((S.subgroupOf H : Subgroup ↥H) : Set ↥H) := hy
  have h1 : y ∈ (Subgroup.normalizer (S : Set (MulAut W))).subgroupOf H := by
    rwa [← normalizer_subgroupOf_eq hS.le]
  exact Subgroup.mem_subgroupOf.1 h1

private lemma not_factor_le_prod_M09 {W : Type} [CommGroup W] [Finite W]
    {H R K X : Subgroup (MulAut W)} {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    (e : ↥H ≃* A × B) (hA : CFSG.Open.IsQuasisimple A) (hB : CFSG.Open.IsQuasisimple B)
    (hK : IsComponentOf K H) (hR : R ≤ Subgroup.normalizer (H : Set (MulAut W)))
    (hgen : H = ⨆ r ∈ R, K.map (MulAut.conj r).toMonoidHom)
    (hRX : R ≤ Subgroup.normalizer (X : Set (MulAut W))) (hXlt : X < H) :
    ¬ (prodFirstFactor e).map H.subtype ≤ X ∧
      ¬ (prodSecondFactor e).map H.subtype ≤ X :=
  not_factor_le_of_swap
    (map_prodFirstFactor_sup_map_prodSecondFactor e)
    (disjoint_map_prodFirstFactor_map_prodSecondFactor e)
    (isComponentOf_map_prodFirstFactor e hA)
    (isComponentOf_map_prodSecondFactor e hB)
    hK hR hgen hRX hXlt

theorem natParMax_omegaPlusFour {W : Type} [CommGroup W] [Finite W]
    {H R K S X : Subgroup (MulAut W)} {n : ℕ} (hΩ : IsOmegaPlus ↥H 4 n)
    (hN : NatOmegaPlus H ⊤ ⊥ 4 n) (hperf : ⁅H, H⁆ = H)
    (hR : R ≤ Subgroup.normalizer (H : Set (MulAut W))) (hK : IsComponentOf K H)
    (hgen : H = ⨆ r ∈ R, K.map (MulAut.conj r).toMonoidHom) (hS : IsSylowIn 2 S H)
    (hRX : R ≤ Subgroup.normalizer (X : Set (MulAut W)))
    (hXge : H ⊓ stabSub (fixV S) ≤ X) (hXlt : X < H) : X = H ⊓ stabSub (fixV S) := by
  haveI : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  haveI : Finite ↥H :=
    Finite.of_injective (fun x : ↥H => (x : MulAut W)) Subtype.coe_injective
  have hn2 : 2 ≤ n := two_le_of_natOmegaPlusFour hN hperf
  obtain ⟨A, B, hAg, hBg, ⟨eAB⟩, hLA, hLB⟩ := isL2Square_of_isOmegaPlus hn2 hΩ
  letI : Group A := hAg
  letI : Group B := hBg
  haveI : Finite (A × B) :=
    Finite.of_injective (eAB.symm : A × B → ↥H) eAB.symm.injective
  haveI : Finite A := Finite.of_surjective (MonoidHom.fst A B) (fun a => ⟨(a, 1), rfl⟩)
  haveI : Finite B := Finite.of_surjective (MonoidHom.snd A B) (fun b => ⟨(1, b), rfl⟩)
  have hA : ∀ (T : Sylow 2 A) (Q : Subgroup A), (T : Subgroup A) ≤ Q → Q ≠ ⊤ →
      Q ≤ Subgroup.normalizer (T : Set A) :=
    fun T Q h1 h2 => l2_sylow_le_normalizer hn2 hLA T Q h1 h2
  have hB : ∀ (T : Sylow 2 B) (Q : Subgroup B), (T : Subgroup B) ≤ Q → Q ≠ ⊤ →
      Q ≤ Subgroup.normalizer (T : Set B) :=
    fun T Q h1 h2 => l2_sylow_le_normalizer hn2 hLB T Q h1 h2
  have hcA : ∀ T : Sylow 2 A, ⁅(⊤ : Subgroup A), Subgroup.normalizer (T : Set A)⁆ = ⊤ :=
    fun T => commutator_top_normalizer_eq_top hn2 hLA T
  let S' : Sylow 2 ↥H := hS.toSylow
  let Y : Subgroup ↥H := X.subgroupOf H
  have hY : Subgroup.normalizer (S' : Set ↥H) ≤ Y :=
    normalizer_sylow_le_subgroupOf_M09 (S := S) (X := X) hS hXge
  have hnot := not_factor_le_prod_M09 eAB (isQuasisimple_of_isL2 hLA)
    (isQuasisimple_of_isL2 hLB) hK hR hgen hRX hXlt
  obtain hYle | hF1 | hF2 := le_normalizer_or_prodFactor_le eAB hA hB hcA S' hY
  · refine le_antisymm ?_ hXge
    have hXN : X ≤ Subgroup.normalizer (S : Set (MulAut W)) :=
      le_normalizer_of_subgroupOf_le hS.le hXlt.le hYle
    exact (le_inf hXlt.le hXN).trans (inf_normalizer_le_inf_stabSub H S)
  · exfalso
    exact hnot.1 (map_prodFirstFactor_le_of_le_subgroupOf eAB (by simpa [Y] using hF1))
  · exfalso
    exact hnot.2 (map_prodSecondFactor_le_of_le_subgroupOf eAB (by simpa [Y] using hF2))

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatParMax
