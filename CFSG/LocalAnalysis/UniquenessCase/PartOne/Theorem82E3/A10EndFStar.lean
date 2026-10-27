module

public import CFSG.Open.LocalVocabulary
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.LocalAnalysis.RankThreeEvenClassification.LocalCore
import CFSG.GroupTheory.PCore.NormalPCoreOf
import CFSG.Walter.Bender1970.S38.JR
import CFSG.Walter.Transitivity.Family

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Gen

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_centralizer_of_pCoreOf_eq_bot {p : ℕ} [Fact p.Prime] {H X V W : Subgroup G}
    (hXH : X ≤ H) (hXn : (X.subgroupOf H).Normal) (hXV : X ≤ Subgroup.normalizer (V : Set G))
    (hV : IsPGroup p V) (hWV : W ≤ V) (hWH : W ≤ H) (hO : CFSG.Open.pCoreOf p H = ⊥) :
    W ≤ Subgroup.centralizer (X : Set G) := by
  intro w hw
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hHX : H ≤ Subgroup.normalizer (X : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXH).mp hXn
  have hcommV : ⁅w, x⁆ ∈ V := by
    have hxw : x * w⁻¹ * x⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 (hXV hx) w⁻¹).1 (V.inv_mem (hWV hw))
    simpa [commutatorElement_def, mul_assoc] using V.mul_mem (hWV hw) hxw
  have hcommX : ⁅w, x⁆ ∈ X := by
    have hwx : w * x * w⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.1 (hHX (hWH hw)) x).1 hx
    simpa [commutatorElement_def] using X.mul_mem hwx (X.inv_mem hx)
  have hNX : X ≤ Subgroup.normalizer ((V ⊓ X : Subgroup G) : Set G) :=
    CFSG.Walter.Transitivity.le_normalizer_inf hXV Subgroup.le_normalizer
  have hVXn : ((V ⊓ X).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hNX
  have hVXp : IsPGroup p ↥(V ⊓ X) :=
    IsPGroup.to_le (p := p) (K := V) (H := V ⊓ X) hV inf_le_left
  have hcore : V ⊓ X ≤ CFSG.Open.pCoreOf p X :=
    CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf p (V ⊓ X) X
      inf_le_right hVXn hVXp
  have hcoreH : CFSG.Open.pCoreOf p X ≤ CFSG.Open.pCoreOf p H :=
    CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer p hXH hHX
  have hmem : ⁅w, x⁆ ∈ CFSG.Open.pCoreOf p H := hcoreH (hcore ⟨hcommV, hcommX⟩)
  rw [hO, Subgroup.mem_bot] at hmem
  exact (commutatorElement_eq_one_iff_mul_comm.mp hmem).symm

theorem eq_bot_of_le_centralizer_pCoreOf {H W : Subgroup G} (hW : IsPGroup 2 W) (hWH : W ≤ H)
    (hO : CFSG.Open.pCoreOf 2 H = ⊥)
    (hF : ∀ p : ℕ, p.Prime → W ≤ Subgroup.centralizer (CFSG.Open.pCoreOf p H : Set G))
    (hE : W ≤ Subgroup.centralizer (CFSG.GorensteinWalter.componentLayerOf H : Set G)) :
    W = ⊥ := by
  have hFit : W ≤ Subgroup.centralizer (CFSG.fittingSubgroupOf H : Set G) := by
    have hEq : CFSG.fittingSubgroupOf H =
        ⨆ q : (Nat.card (↥H)).primeFactors.attach, CFSG.Open.pCoreOf q.1.1 H := by
      rw [show CFSG.fittingSubgroupOf H = CFSG.GorensteinWalter.fittingSubgroupOf H from rfl,
        CFSG.GorensteinWalter.fittingSubgroupOf_eq_iSup_qCoreOf H]
      rfl
    rw [hEq]
    exact CFSG.subgroup_le_centralizer_iSup_of_le_centralizer
      (fun q : (Nat.card (↥H)).primeFactors.attach => CFSG.Open.pCoreOf q.1.1 H)
      (fun q => hF q.1.1 (Nat.prime_of_mem_primeFactors q.1.2))
  have hFC : CFSG.GorensteinWalter.generalizedFittingSubgroupOf H ≤
      Subgroup.centralizer (W : Set G) := by
    rw [CFSG.GorensteinWalter.generalizedFittingSubgroupOf]
    exact sup_le (Subgroup.le_centralizer_iff.mp hFit) (Subgroup.le_centralizer_iff.mp hE)
  have hWC : W ≤ Subgroup.centralizer
      (CFSG.GorensteinWalter.generalizedFittingSubgroupOf H : Set G) :=
    Subgroup.le_centralizer_iff.mpr hFC
  have hWF : W ≤ CFSG.GorensteinWalter.generalizedFittingSubgroupOf H := by
    intro w hw
    exact CFSG.Walter.inf_centralizer_generalizedFitting_le H ⟨hWH hw, hWC hw⟩
  have hWn : (W.subgroupOf (CFSG.GorensteinWalter.generalizedFittingSubgroupOf H)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWF).mpr fun f hf =>
      Subgroup.centralizer_le_normalizer (W : Set G) (hFC hf)
  have hcore : W ≤ CFSG.Open.pCoreOf 2
      (CFSG.GorensteinWalter.generalizedFittingSubgroupOf H) :=
    CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 W _ hWF hWn hW
  have hle : CFSG.Open.pCoreOf 2 (CFSG.GorensteinWalter.generalizedFittingSubgroupOf H) ≤
      CFSG.Open.pCoreOf 2 H :=
    CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2
      (CFSG.GorensteinWalter.generalizedFittingSubgroupOf_le H)
      (CFSG.GorensteinWalter.le_normalizer_of_isNormalIn
        (CFSG.GorensteinWalter.generalizedFittingSubgroupOf_isNormalIn H))
  rw [hO] at hle
  exact le_bot_iff.mp (hcore.trans hle)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Gen
