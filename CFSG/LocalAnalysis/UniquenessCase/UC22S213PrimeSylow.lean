module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SylowCentralOuter
import TauCeti.GroupTheory.PGroup
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms
  (Outer equivalence centerQuotient_outer_injective)
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

theorem uc22s213_isMulCommutative_sylow_bar2 {L : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (Bar2 L)) {r : ℕ} (hr : r.Prime)
    (hZ : ¬ r ∣ Nat.card (center (Bar2 L)))
    (hab : ∀ P : Sylow r (BarInf L), IsMulCommutative (P : Subgroup (BarInf L)))
    (P : Sylow r (Bar2 L)) : IsMulCommutative (P : Subgroup (Bar2 L)) := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨e⟩ := uc22p21k_barInf_equiv hq
  let φ : Bar2 L →* BarInf L := e.symm.toMonoidHom.comp (QuotientGroup.mk' (center (Bar2 L)))
  have hφ : Function.Surjective φ := e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hQ := hab (P.mapSurjective hφ)
  rw [Sylow.coe_mapSurjective] at hQ
  have hdisj := TauCeti.disjoint_of_not_dvd_natCard_of_isPGroup hZ P.isPGroup'
  refine le_centralizer_iff_isMulCommutative.mp fun x hx => mem_centralizer_iff.mpr fun y hy => ?_
  have hc : φ y * φ x = φ x * φ y := mem_centralizer_iff.mp
    (le_centralizer_iff_isMulCommutative.mpr hQ (mem_map_of_mem φ hx)) (φ y) (mem_map_of_mem φ hy)
  have h1 : e.symm (QuotientGroup.mk' (center (Bar2 L)) (y * x * (x * y)⁻¹)) = 1 := by
    change φ (y * x * (x * y)⁻¹) = 1
    rw [map_mul, map_inv, map_mul, map_mul, hc, mul_inv_cancel]
  have hZc : y * x * (x * y)⁻¹ ∈ center (Bar2 L) := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply]
    exact (MulEquiv.map_eq_one_iff e.symm).mp h1
  exact mul_inv_eq_one.mp (Subgroup.disjoint_def.mp hdisj hZc
    (P.mul_mem (P.mul_mem hy hx) (P.inv_mem (P.mul_mem hx hy))))

theorem uc22s213_not_dvd_card_outer_bar2 {L : Subgroup G} (hq : CFSG.Open.IsQuasisimple (Bar2 L))
    {r : ℕ} (hout : ¬ r ∣ Nat.card (Outer (BarInf L))) :
    ¬ r ∣ Nat.card (Outer (Bar2 L)) := by
  haveI : Group.IsPerfect (Bar2 L) := Group.isPerfect_def.mpr hq.1
  obtain ⟨e⟩ := uc22p21k_barInf_equiv hq
  have h1 : Nat.card (Outer (Bar2 L)) ∣ Nat.card (Outer (Bar2 L ⧸ center (Bar2 L))) :=
    Subgroup.card_dvd_of_injective _ (centerQuotient_outer_injective (Bar2 L))
  rw [← Nat.card_congr (equivalence e).toEquiv] at h1
  exact fun hr => hout (hr.trans h1)

theorem uc22s213_exists_sylow_le_centralizer_of_prime {M L E : Subgroup G} (hLM : L ≤ M)
    (hMN : M ≤ normalizer (L : Set G)) (hq : CFSG.Open.IsQuasisimple (Bar2 L)) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hZ : ¬ r ∣ Nat.card (center (Bar2 L)))
    (hab : ∀ P : Sylow r (BarInf L), IsMulCommutative (P : Subgroup (BarInf L)))
    (hout : ¬ r ∣ Nat.card (Outer (BarInf L))) (hEL : E ≤ L) (hEr : IsPGroup r E) :
    ∃ R, IsSylowOf r R M ∧ E ≤ R ⊓ centralizer (R : Set G) :=
  PartTwo.exists_sylow_le_centralizer_of_isMulCommutative hr hr2 hLM hMN
    (uc22s213_isMulCommutative_sylow_bar2 hq hr hZ hab)
    (fun h => uc22s213_not_dvd_card_outer_bar2 hq hout
      (h.trans (PartTwo.relIndex_centOverO2_dvd_card_outer hLM hMN))) hEL hEr

end CFSG.LocalAnalysis.UniquenessCase.UC22
