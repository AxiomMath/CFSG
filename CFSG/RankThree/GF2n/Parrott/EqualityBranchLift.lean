module

public import CFSG.GroupTheory.ConjOrderThree
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.GF2n.Parrott.CentralizerV
public import CFSG.RankThree.GF2n.Parrott.LiftOrderThree

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

theorem centralizerJ_eq_of_qH_eq_of_orderOf_eq_three (h : Tim79a.ParrottHyp z)
    {σ σ' : ↥(H z)} (hσ : orderOf σ = 3) (hσ' : orderOf σ' = 3) (hq : qH D σ = qH D σ') :
    centralizerJ σ = centralizerJ σ' := by
  have hcos : σ * σ'⁻¹ ∈ (J z).subgroupOf (H z) := by
    rw [J_mem_iff D, map_mul, map_inv, hq, mul_inv_cancel]
  obtain ⟨j, hj, hjconj⟩ := CFSG.GroupTheory.exists_conj_of_order_three_of_mul_inv_mem
    (isPGroup_J_subgroupOf (z := z)) hσ hσ' hcos
  have hjJ : (j : G) ∈ J z := Subgroup.mem_subgroupOf.mp hj
  have hJ' : ⁅J z, J z⁆ = Subgroup.zpowers z := by
    obtain ⟨-, -, hcomm, -, -⟩ := h
    simpa [J, H] using hcomm
  have hσ'z : Commute (σ' : G) z := Subgroup.mem_centralizer_singleton_iff.mp σ'.2
  have hσ'c : ∀ c ∈ ⁅J z, J z⁆, (σ' : G) * c = c * (σ' : G) := by
    intro c hc
    rw [hJ'] at hc
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    exact (hσ'z.zpow_right n).eq
  have hσeq : (σ : G) = (j : G) * (σ' : G) * (j : G)⁻¹ := by
    rw [← hjconj]
    simp
  ext k
  rw [mem_centralizerJ_iff, mem_centralizerJ_iff, hσeq]
  have hcJ : (k : G)⁻¹ * (j : G)⁻¹ * (k : G) * (j : G) ∈ ⁅J z, J z⁆ := by
    have hmem := Subgroup.commutator_mem_commutator ((J z).inv_mem k.2) ((J z).inv_mem hjJ)
    rwa [commutatorElement_def, inv_inv, inv_inv] at hmem
  set c : G := (k : G)⁻¹ * (j : G)⁻¹ * (k : G) * (j : G) with hc
  have hkc : (j : G)⁻¹ * (k : G) * (j : G) = (k : G) * c := by
    rw [hc]
    group
  have hcσ : (k : G) * c * (σ' : G) = (k : G) * (σ' : G) * c := by
    rw [mul_assoc, ← hσ'c c hcJ, ← mul_assoc]
  constructor
  · intro h1
    have h2 : (k : G) * c * (σ' : G) = (σ' : G) * ((k : G) * c) := by
      rw [← hkc]
      calc (j : G)⁻¹ * (k : G) * (j : G) * (σ' : G)
          = (j : G)⁻¹ * ((k : G) * ((j : G) * (σ' : G) * (j : G)⁻¹)) * (j : G) := by group
        _ = (j : G)⁻¹ * (((j : G) * (σ' : G) * (j : G)⁻¹) * (k : G)) * (j : G) := by rw [h1]
        _ = (σ' : G) * ((j : G)⁻¹ * (k : G) * (j : G)) := by group
    have h3 : (k : G) * (σ' : G) * c = (σ' : G) * (k : G) * c := by
      rw [← hcσ, h2, mul_assoc]
    exact mul_right_cancel h3
  · intro h1
    have h2 : (j : G)⁻¹ * (k : G) * (j : G) * (σ' : G) =
        (σ' : G) * ((j : G)⁻¹ * (k : G) * (j : G)) := by
      rw [hkc, hcσ, h1, mul_assoc]
    calc (k : G) * ((j : G) * (σ' : G) * (j : G)⁻¹)
        = (j : G) * ((j : G)⁻¹ * (k : G) * (j : G) * (σ' : G)) * (j : G)⁻¹ := by group
      _ = (j : G) * ((σ' : G) * ((j : G)⁻¹ * (k : G) * (j : G))) * (j : G)⁻¹ := by rw [h2]
      _ = (j : G) * (σ' : G) * (j : G)⁻¹ * (k : G) := by group

end CFSG.RankThree.GF2n.Parrott
