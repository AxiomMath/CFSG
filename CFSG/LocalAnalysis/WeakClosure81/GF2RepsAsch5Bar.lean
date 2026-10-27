module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Defs
public import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Bar2)

@[expose] def barImage {Q : Type} [Group Q] (H T : Subgroup Q) : Subgroup (Bar2 H) :=
  (T.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))

theorem pCore_two_bar2_eq_bot {Q : Type} [Group Q] (H : Subgroup Q) :
    CFSG.pCore 2 (Bar2 H) = ⊥ :=
  CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot (H := ↥H) (p := 2)

theorem isSylowOf_two_iff_isSylowIn {G : Type} [Group G] [Finite G] {P K : Subgroup G} :
    CFSG.ABGLocalTools.IsSylowOf 2 P K ↔ IsSylowIn 2 P K :=
  CFSG.ABGLocalTools.isSylowOf_iff.trans Iff.rfl

private theorem gf2_Bar_isSylowIn_subgroupOf_top {Q : Type} [Group Q] {H T : Subgroup Q}
    (hT : IsSylowIn 2 T H) : IsSylowIn 2 (T.subgroupOf H) ⊤ := by
  have := (E1.isSylowIn_subgroupOf_iff (p := 2) (H := H) hT.le le_rfl).mpr hT
  rwa [Subgroup.subgroupOf_self] at this

theorem pCore_le_subgroupOf_of_isSylowIn {Q : Type} [Group Q] {H T : Subgroup Q}
    (hT : IsSylowIn 2 T H) : CFSG.pCore 2 ↥H ≤ T.subgroupOf H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsSylowIn.le_of_normal (gf2_Bar_isSylowIn_subgroupOf_top hT) le_top inferInstance
    CFSG.pCore_isPGroup

theorem isSylowIn_barImage {Q : Type} [Group Q] [Finite Q] {H T : Subgroup Q}
    (hT : IsSylowIn 2 T H) : IsSylowIn 2 (barImage H T) ⊤ :=
  E1.isSylowIn_two_map_top (QuotientGroup.mk'_surjective _) (gf2_Bar_isSylowIn_subgroupOf_top hT)

theorem hasUniqueMaxOver_barImage {Q : Type} [Group Q] [Finite Q] {H T M : Subgroup Q}
    (hT : IsSylowIn 2 T H) (hU : calNIn H T = {M}) : HasUniqueMaxOver (barImage H T) := by
  have hMmem : M ∈ calNIn H T := by rw [hU]; exact Set.mem_singleton M
  obtain ⟨hTM, hMH, -⟩ := hMmem
  have hO := pCore_le_subgroupOf_of_isSylowIn hT
  refine ⟨(M.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)), ?_, ?_⟩
  · rw [lt_top_iff_ne_top]
    intro htop
    refine absurd (lt_of_lt_of_le hMH ?_) (lt_irrefl M)
    intro h hh
    have hπ : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨h, hh⟩ ∈
        (M.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) := by
      rw [htop]; exact Subgroup.mem_top _
    obtain ⟨m, hm, hmh⟩ := hπ
    have h1 : m⁻¹ * ⟨h, hh⟩ ∈ CFSG.pCore 2 ↥H := by
      rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥H), MonoidHom.mem_ker, map_mul, map_inv, hmh]
      simp
    have h2 : ((m⁻¹ * ⟨h, hh⟩ : ↥H) : Q) ∈ T := hO h1
    have h3 : ((m⁻¹ * ⟨h, hh⟩ : ↥H) : Q) ∈ M := hTM h2
    have h4 : (m : Q) ∈ M := hm
    have h5 : h = (m : Q) * ((m⁻¹ * ⟨h, hh⟩ : ↥H) : Q) := by simp
    rw [h5]
    exact M.mul_mem h4 h3
  · intro X hTX hXtop
    set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
    set Y' : Subgroup ↥H := X.comap π with hY'
    have hTY' : T.subgroupOf H ≤ Y' := fun t ht => hTX (Subgroup.mem_map_of_mem π ht)
    have hY'top : Y' < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro h
      apply (ne_of_lt hXtop)
      rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) X, ← hY', h,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    set Y : Subgroup Q := Y'.map H.subtype with hY
    have hTY : T ≤ Y := fun t ht => ⟨⟨t, hT.le ht⟩, hTY' ht, rfl⟩
    have hYH : Y < H := by
      refine lt_of_le_of_ne (Subgroup.map_subtype_le _) fun h => ?_
      have : Y' = ⊤ := by
        apply Subgroup.map_injective H.subtype_injective
        rw [← hY, h, Subgroup.map_top, Subgroup.range_subtype]
      exact absurd this (ne_of_lt hY'top)
    obtain ⟨M', hM', hYM'⟩ := exists_mem_calNIn_of_lt hTY hYH
    rw [hU] at hM'
    have hM'M : M' = M := hM'
    subst hM'M
    intro x hx
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H) x
    have hhY' : h ∈ Y' := hx
    exact ⟨h, hYM' ⟨h, hhY', rfl⟩, rfl⟩

end CFSG.LocalAnalysis.WeakClosure81
