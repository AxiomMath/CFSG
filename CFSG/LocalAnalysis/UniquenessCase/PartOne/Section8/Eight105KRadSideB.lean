module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KRadEigen
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KRadTrans
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KRadBorel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105

open CFSG.Open Subgroup Matrix
open CFSG.Assembly.LowTwoRank (StatedSU)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LinearGroups (stdHermForm)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f ε : ℕ}
  {b : StatedSU (2 * 2 + ε) (2 ^ f) K} {ω : K}

omit [Finite K] in
theorem RadSetup.normalizer_le_of_pCoreOf_le (hS : RadSetup ε b ω) (h : UnitaryFieldData 2 f K)
    (T₀ : Sylow 2 (StatedSU (2 * 2 + ε) (2 ^ f) K))
    (hT₀ : pCoreOf 2 (stabSU (2 ^ f) (eigSU b ω)) ≤ T₀) :
    normalizer ((T₀ : Subgroup (StatedSU (2 * 2 + ε) (2 ^ f) K)) :
      Set (StatedSU (2 * 2 + ε) (2 ^ f) K)) ≤
      stabSU (2 ^ f) (eigSU b ω) := by
  obtain ⟨L, hLrank, hLiso, hNL⟩ :=
    exists_isotropic_normalizer_le h (r := 2) (by norm_num) hS.le_one T₀
  have hnotmem : ∀ a ∈ eigSU b ω, a ∉ L →
      ∀ v ∈ L, stdHermForm h (2 * 2 + ε) a v = 0 := by
    intro a ha haL v hv
    obtain ⟨t, htpc, ht⟩ := exists_transvection_mem_pCoreOf h (hS.isotropic h) ha
    have htT : t ∈ (T₀ : Subgroup (StatedSU (2 * 2 + ε) (2 ^ f) K)) := hT₀ htpc
    have htN : t ∈ normalizer ((T₀ : Subgroup (StatedSU (2 * 2 + ε) (2 ^ f) K)) :
        Set (StatedSU (2 * 2 + ε) (2 ^ f) K)) := Subgroup.le_normalizer htT
    have htL : ((t : GL (Fin (2 * 2 + ε)) K) :
        Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K) *ᵥ v ∈ L :=
      (mem_stabSU.mp (hNL htN)) v hv
    rw [ht v] at htL
    have hsm : stdHermForm h (2 * 2 + ε) a v • a ∈ L := by
      simpa using L.sub_mem htL hv
    by_contra hc
    have haeq : a = (stdHermForm h (2 * 2 + ε) a v)⁻¹ •
        (stdHermForm h (2 * 2 + ε) a v • a) := (inv_smul_smul₀ hc a).symm
    refine haL ?_
    rw [haeq]
    exact L.smul_mem _ hsm
  have horth : ∀ a ∈ eigSU b ω, ∀ v ∈ L, stdHermForm h (2 * 2 + ε) a v = 0 := by
    by_cases hex : ∃ a ∈ eigSU b ω, a ∉ L
    · obtain ⟨a₀, ha₀W, ha₀L⟩ := hex
      have ha₀ := hnotmem a₀ ha₀W ha₀L
      intro a ha v hv
      by_cases hsum : a + a₀ ∈ L
      · have haL : a ∉ L := fun haL => ha₀L (by simpa using L.sub_mem hsum haL)
        exact hnotmem a ha haL v hv
      · have hsum0 := hnotmem (a + a₀) ((eigSU b ω).add_mem ha ha₀W) hsum v hv
        have hadd : stdHermForm h (2 * 2 + ε) (a + a₀) v =
            stdHermForm h (2 * 2 + ε) a v + stdHermForm h (2 * 2 + ε) a₀ v := by
          rw [LinearMap.map_add, LinearMap.add_apply]
        rw [hadd, ha₀ v hv, add_zero] at hsum0
        exact hsum0
    · have hWL : eigSU b ω ≤ L := fun x hx => by
        by_contra hxL
        exact hex ⟨x, hx, hxL⟩
      have hLW : L = eigSU b ω :=
        (Submodule.eq_of_le_of_finrank_eq hWL (by rw [hS.finrank_eig, hLrank])).symm
      intro a ha v hv
      rw [hLW] at hv
      exact hS.isotropic h a ha v hv
  have hLleW : L ≤ eigSU b ω := fun v hv =>
    hS.mem_of_isotropic_orth h (fun w hw => horth w hw v hv) (hLiso v hv v hv)
  have hLW : L = eigSU b ω :=
    Submodule.eq_of_le_of_finrank_eq hLleW (by rw [hLrank, hS.finrank_eig])
  rw [hLW] at hNL
  exact hNL

theorem RadSetup.exists_normalizer_le (hS : RadSetup ε b ω) (h : UnitaryFieldData 2 f K) :
    ∃ T₀ : Sylow 2 (StatedSU (2 * 2 + ε) (2 ^ f) K),
      normalizer ((T₀ : Subgroup (StatedSU (2 * 2 + ε) (2 ^ f) K)) :
        Set (StatedSU (2 * 2 + ε) (2 ^ f) K)) ≤
        stabSU (2 ^ f) (eigSU b ω) := by
  obtain ⟨T₀, hT₀⟩ :=
    IsPGroup.exists_le_sylow (p := 2)
      (P := pCoreOf 2 (stabSU (2 ^ f) (eigSU b ω)))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (stabSU (2 ^ f) (eigSU b ω)))
  exact ⟨T₀, hS.normalizer_le_of_pCoreOf_le h T₀ hT₀⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105
