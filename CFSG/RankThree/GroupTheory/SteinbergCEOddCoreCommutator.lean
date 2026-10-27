module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.RankThree.GroupTheory

open CFSG
open scoped commutatorElement

theorem odd_core_commutator_after_two_core_centralization {H : Type*} [Group H] [Finite H]
    {q : ℕ} (hq : q.Prime) {D R : Subgroup H}
    (hDF : D ≤ (pCore q (H ⧸ pCore 2 H)).comap (QuotientGroup.mk' (pCore 2 H)))
    (hD : IsPGroup q D) (hRD : R ≤ Subgroup.normalizer (D : Set H))
    (hRJ : R ≤ Subgroup.centralizer (pCore 2 H : Set H)) :
    ⁅D, R⁆ ≤ pCore q H := by
  have : Fact q.Prime := ⟨hq⟩
  set J := pCore 2 H
  set π := QuotientGroup.mk' J
  set F := (pCore q (H ⧸ J)).comap π
  set C := F ⊓ Subgroup.centralizer (J : Set H)
  have hFn : F.Normal := Subgroup.Normal.comap inferInstance π
  have hCn : C.Normal := Subgroup.normal_inf_normal F _
  have hED : ⁅D, R⁆ ≤ D := by
    rw [Subgroup.commutator_le]
    intro d hd r hr
    have h1 : r * d⁻¹ * r⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp (hRD hr) d⁻¹).mp (D.inv_mem hd)
    have h2 : ⁅d, r⁆ = d * (r * d⁻¹ * r⁻¹) := by group
    rw [h2]
    exact D.mul_mem hd h1
  have hEJ : ⁅D, R⁆ ≤ Subgroup.centralizer (J : Set H) := by
    rw [Subgroup.commutator_le]
    intro d _ r hr
    have h1 : d * r * d⁻¹ ∈ Subgroup.centralizer (J : Set H) :=
      (Subgroup.normal_centralizer (H := J)).conj_mem r (hRJ hr) d
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ (hRJ hr))
  have hEC : ⁅D, R⁆ ≤ C := le_inf (hED.trans hDF) hEJ
  let f : C →* pCore q (H ⧸ J) :=
    (π.comp C.subtype).codRestrict (pCore q (H ⧸ J)) fun c => c.2.1
  have hker : f.ker ≤ Subgroup.center C := by
    intro c hc
    have hcJ : (c : H) ∈ J := by
      have h : π c = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hc)
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    refine Subgroup.mem_center_iff.mpr fun c' => Subtype.ext ?_
    exact (Subgroup.mem_centralizer_iff.mp c'.2.2 c hcJ).symm
  have hqnil : Group.IsNilpotent (pCore q (H ⧸ J)) := (pCore_isPGroup).isNilpotent
  have hCnil : Group.IsNilpotent C := Subgroup.isNilpotent_of_ker_le_center f hker
  have hEq : IsPGroup q (⁅D, R⁆.subgroupOf C) :=
    (hD.to_le hED).of_injective (Subgroup.subgroupOfEquivOfLe hEC).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hEC).injective
  obtain ⟨P, hP⟩ := hEq.exists_le_sylow
  have hPq := Sylow.map_le_pCore hCn hCnil q P
  have hEmap : ⁅D, R⁆ = (⁅D, R⁆.subgroupOf C).map C.subtype := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hEC]
  rw [hEmap]
  exact (Subgroup.map_mono hP).trans hPq

end CFSG.RankThree.GroupTheory
