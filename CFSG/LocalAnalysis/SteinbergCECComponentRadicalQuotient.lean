module

public import CFSG.LocalAnalysis.SteinbergCCCComponentSubnormalSolvable
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical
public import CFSG.GroupTheory.ABGLocalTools.Constraint

public section

namespace CFSG.LocalAnalysis

open Subgroup

theorem Ccomponent_radical_quotient_simple {G : Type*} [Group G] [Finite G] {L : Subgroup G}
    (hL : IsCComponent L) :
    solvableRadical L < ⊤ ∧
      (∀ U : Subgroup L, U < ⊤ → U.IsSubnormal → U ≤ solvableRadical L) ∧
      IsSimpleGroup (L ⧸ solvableRadical L) ∧
      (∃ a b : L ⧸ solvableRadical L, a * b ≠ b * a) ∧
      ∀ M : Subgroup L, (M < ⊤ ∧ M.IsSubnormal ∧
        ∀ U : Subgroup L, U < ⊤ → U.IsSubnormal → M ≤ U → U = M) ↔ M = solvableRadical L := by
  have hL1 : L ≠ ⊥ := hL.1
  have hLp : ⁅L, L⁆ = L := hL.2.1
  have hperf : Group.IsPerfect L := Subgroup.isPerfect_iff.mpr hLp
  have hnt : Nontrivial L := (nontrivial_iff_ne_bot L).mpr hL1
  set R := solvableRadical L with hRdef
  have hRsolv : Group.IsSolvable R := CFSG.ABGLocalTools.solvableRadical_isSolvable
  have hRtop : R < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    apply Group.IsPerfect.not_isSolvable L
    rw [h] at hRsolv
    exact Group.isSolvable_of_surjective (f := (Subgroup.topEquiv (G := L)).toMonoidHom)
      (Subgroup.topEquiv (G := L)).surjective
  have hsub : ∀ U : Subgroup L, U < ⊤ → U.IsSubnormal → U ≤ R := by
    intro U hU hUs
    have hUL : U.map L.subtype < L := by
      have h1 := (map_lt_map_iff_of_injective L.subtype_injective).mpr hU
      rwa [← MonoidHom.range_eq_map, range_subtype] at h1
    have hUs' : ((U.map L.subtype).subgroupOf L).IsSubnormal := by
      rwa [subgroupOf, comap_map_eq_self_of_injective L.subtype_injective]
    have hsolv := Ccomponent_proper_subnormal_solvable hL hUL hUs'
    have hUsolv : Group.IsSolvable U :=
      Group.isSolvable_of_surjective
        (f := (U.equivMapOfInjective L.subtype L.subtype_injective).symm.toMonoidHom)
        (U.equivMapOfInjective L.subtype L.subtype_injective).symm.surjective
    exact SignalizerFunctorTheorem.Nonsolvable.le_solvableRadical_of_isSubnormal hUs hUsolv
  have hntq : Nontrivial (L ⧸ R) := QuotientGroup.nontrivial_iff.mpr hRtop.ne
  have hsimple : IsSimpleGroup (L ⧸ R) :=
    { toNontrivial := hntq
      eq_bot_or_eq_top_of_normal := fun N hN => by
        have hsurj := QuotientGroup.mk'_surjective R
        by_cases htop : N.comap (QuotientGroup.mk' R) = ⊤
        · right
          rw [← Subgroup.map_comap_eq_self_of_surjective hsurj N, htop, ← MonoidHom.range_eq_map,
            QuotientGroup.range_mk']
        · left
          have hle : N.comap (QuotientGroup.mk' R) ≤ R :=
            hsub _ (lt_top_iff_ne_top.mpr htop) (hN.comap _).isSubnormal
          rw [← Subgroup.map_comap_eq_self_of_surjective hsurj N, eq_bot_iff]
          rintro _ ⟨y, hy, rfl⟩
          rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          exact hle hy }
  have hnonab : ∃ a b : L ⧸ R, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have hperfq : Group.IsPerfect (L ⧸ R) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' R) (QuotientGroup.mk'_surjective R)
    have hc : commutator (L ⧸ R) = ⊥ := by
      rw [eq_bot_iff, commutator_def, commutator_le]
      intro a _ b _
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact h a b
    rw [Group.IsPerfect.commutator_eq_top] at hc
    obtain ⟨a, ha⟩ := exists_ne (1 : L ⧸ R)
    exact ha ((Subgroup.mem_bot).mp (hc ▸ mem_top a))
  have hRsn : R.IsSubnormal := (inferInstance : R.Normal).isSubnormal
  refine ⟨hRtop, hsub, hsimple, hnonab, fun M => ⟨fun ⟨hM, hMs, hmax⟩ => ?_, ?_⟩⟩
  · exact (hmax R hRtop hRsn (hsub M hM hMs)).symm
  · rintro rfl
    exact ⟨hRtop, hRsn, fun U hU hUs hRU => le_antisymm (hsub U hU hUs) hRU⟩

end CFSG.LocalAnalysis
