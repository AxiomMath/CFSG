module

public import CFSG.RankThree.PartTwo.Sec18.Item189K0Quot
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
public import CFSG.RankThree.PartTwo.Sec18.Item189K0Setting

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G] {A B X M : Subgroup G} {c : G}

private theorem central_of_mem_normal_solvable {Q : Type} [Group Q] {K R : Subgroup Q}
    (hK : IsQuasisimple K) [hRn : R.Normal] (hRs : Group.IsSolvable R) {z : Q} (hzK : z ∈ K)
    (hzR : z ∈ R) : ∀ g ∈ K, g * z = z * g := by
  have hperf : Group.IsPerfect K := by
    obtain ⟨hp, -, -⟩ := hK
    exact hp
  haveI : Group.IsPerfect K := hperf
  haveI : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hK
  haveI : Group.IsSolvable R := hRs
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hK
      (inferInstance : (R.subgroupOf K).Normal) with htop | hle
  · exfalso
    have hKR : K ≤ R := fun k hk => by
      have hmem : (⟨k, hk⟩ : K) ∈ R.subgroupOf K := by
        rw [htop]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hmem
    have hs : Group.IsSolvable K :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKR)
    exact Group.IsPerfect.not_isSolvable K hs
  · intro g hg
    have hz : (⟨z, hzK⟩ : K) ∈ Subgroup.center K := hle (Subgroup.mem_subgroupOf.mpr hzR)
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨g, hg⟩)

private theorem commute_of_normalizer_of_mem_normal_solvable {Q : Type} [Group Q]
    {K R : Subgroup Q} (hK : IsQuasisimple K) [hRn : R.Normal] (hRs : Group.IsSolvable R)
    {x : Q} (hxK : x ∈ Subgroup.normalizer (K : Set Q)) (hxR : x ∈ R) :
    ∀ k ∈ K, x * k = k * x := by
  have hperf : Group.IsPerfect K := by
    obtain ⟨hp, -, -⟩ := hK
    exact hp
  have hcomm : ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ Subgroup.centralizer (K : Set Q) := by
    intro k hk
    have h1 : x * k * x⁻¹ * k⁻¹ ∈ K :=
      K.mul_mem ((Subgroup.mem_set_normalizer_iff.mp hxK k).mp hk) (K.inv_mem hk)
    have h2 : x * k * x⁻¹ * k⁻¹ ∈ R := by
      have hc : k * x⁻¹ * k⁻¹ ∈ R := hRn.conj_mem x⁻¹ (R.inv_mem hxR) k
      have heq : x * k * x⁻¹ * k⁻¹ = x * (k * x⁻¹ * k⁻¹) := by simp only [mul_assoc]
      rw [heq]
      exact R.mul_mem hxR hc
    exact Subgroup.mem_centralizer_iff.mpr fun h hh =>
      central_of_mem_normal_solvable hK hRs h1 h2 h hh
  exact commute_of_forall_commutator_mem_centralizer hperf hxK hcomm

theorem K0Setting.le_thetaQuotCentralizer (h45 : Sec4.Item4_5) (h : K0Setting G A B X M c)
    {K : Subgroup G} (hK : K ∈ thetaComponentsIn M) : B ≤ Sec4.thetaQuotCentralizer K := by
  have hBM : B ≤ M := h.le_A.trans h.hAM
  have hA : A ≤ Subgroup.normalizer (K : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsIn_of_item4_5 h45 h.sec4 h.hAM h.plane.isElemAbelian
      ⟨3, le_rfl, h.plane.card_eq.trans (by norm_num)⟩ K hK
  have hBn : B ≤ Subgroup.normalizer (K : Set G) := h.le_A.trans hA
  have hKM : K ≤ M := le_of_mem_thetaComponentsIn hK
  refine (le_thetaQuotCentralizer_iff_imM_commute hK hBM hBn).2 ?_
  intro x hx y hy
  have hRM : (Sec4.oTwoP 3 M).map M.subtype ≤ M := Subgroup.map_subtype_le _
  haveI : (imM M ((Sec4.oTwoP 3 M).map M.subtype)).Normal :=
    normal_imM hRM (le_normalizer_oTwoP_map M)
  exact commute_of_normalizer_of_mem_normal_solvable (imM_isQuasisimple hK)
    (isSolvable_imM (M := M) (isSolvable_oTwoP M))
    (imM_le_normalizer hBM hKM hBn hx) (imM_mono (M := M) h.oTwoThree hx) y hy

end CFSG.RankThree.PartTwo.Sec18
