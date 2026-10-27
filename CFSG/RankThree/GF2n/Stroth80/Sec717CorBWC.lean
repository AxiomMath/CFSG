module

public import CFSG.CGT.Timmesfeld75.WCBasic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

variable {H : Type} [Group H]

theorem sec717_isWC_of_data {T Zs : Subgroup H} (hT : IsElemAbelian 2 T) (hZT : Zs ≤ T)
    (hZs : ∃ z ∈ Zs, z ≠ 1)
    (hC1 : ∀ x ∈ T, ∀ y ∈ T, x ≠ 1 → y ≠ 1 → ∃ h : H, h * x * h⁻¹ = y)
    (hC2 : ∀ z ∈ Zs, z ≠ 1 → ∀ h : H, h * z * h⁻¹ ∈ T → h * z * h⁻¹ ∉ Zs →
      conjSubgroup h T = T)
    (hC3 : ∀ z ∈ Zs, z ≠ 1 → ∀ g : H, conjSubgroup g T ≤ Subgroup.centralizer {z} →
      conjSubgroup g T = T) :
    IsWC T := by
  have hcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hT.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  refine ⟨hT, fun t ht ht1 => ⟨fun x hx => ?_, fun g hg => ?_⟩⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact (hcomm x hx t ht).symm
  · by_cases htZ : t ∈ Zs
    · exact hC3 t htZ ht1 g hg
    · obtain ⟨z0, hz0, hz01⟩ := hZs
      obtain ⟨h, hh⟩ := hC1 z0 (hZT hz0) t ht hz01 ht1
      have hcen : h * z0 * h⁻¹ ∈ T := by rw [hh]; exact ht
      have hnot : h * z0 * h⁻¹ ∉ Zs := by rw [hh]; exact htZ
      have hhT : conjSubgroup h T = T := hC2 z0 hz0 hz01 h hcen hnot
      have hcentre : conjSubgroup (h⁻¹ * g) T ≤ Subgroup.centralizer {z0} := by
        intro x hx
        rw [mem_conjSubgroup] at hx
        have hs : h * x * h⁻¹ ∈ conjSubgroup g T := by
          rw [mem_conjSubgroup]
          have hy : g⁻¹ * (h * x * h⁻¹) * g = (h⁻¹ * g)⁻¹ * x * (h⁻¹ * g) := by group
          rw [hy]
          exact hx
        have hst := Subgroup.mem_centralizer_iff.mp (hg hs) t (Set.mem_singleton t)
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        rw [hw]
        rw [← hh] at hst
        have e1 : h * x * h⁻¹ * (h * z0 * h⁻¹) = h * (x * z0) * h⁻¹ := by group
        have e2 : h * z0 * h⁻¹ * (h * x * h⁻¹) = h * (z0 * x) * h⁻¹ := by group
        rw [e1, e2] at hst
        have hxz := mul_left_cancel (mul_right_cancel hst)
        exact hxz
      have hgh : conjSubgroup (h⁻¹ * g) T = T := hC3 z0 hz0 hz01 (h⁻¹ * g) hcentre
      have hdecomp : conjSubgroup g T = conjSubgroup h (conjSubgroup (h⁻¹ * g) T) := by
        ext x
        rw [mem_conjSubgroup, mem_conjSubgroup, mem_conjSubgroup]
        have e : (h⁻¹ * g)⁻¹ * (h⁻¹ * x * h) * (h⁻¹ * g) = g⁻¹ * x * g := by group
        rw [e]
      rw [hdecomp, hgh, hhT]

theorem sec717_corBHyp_of_isWC {T : Subgroup H} (hT : IsWC T) : CorBHyp T := by
  have hcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hT.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  refine ⟨hT.1, hT.isTI, fun g => ⟨fun hc => ?_, fun hg => ?_⟩⟩
  · by_cases hnt : ∃ t ∈ T, t ≠ 1
    · obtain ⟨t, ht, ht1⟩ := hnt
      refine (hT.2 t ht ht1).2 g ?_
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]
      exact hc t ht y hy
    · have hnt' : ∀ t ∈ T, t = 1 := fun t ht => by_contra fun h => hnt ⟨t, ht, h⟩
      apply le_antisymm
      · intro x hx
        rw [mem_conjSubgroup] at hx
        have := hnt' _ hx
        have hx1 : x = 1 := by
          have e : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
          rw [e, this, mul_one, mul_inv_cancel]
        rw [hx1]
        exact T.one_mem
      · intro x hx
        have := hnt' x hx
        rw [this]
        exact one_mem _
  · intro x hx y hy
    rw [hg] at hy
    exact hcomm x hx y hy

end CFSG.RankThree.GF2n.Stroth80
