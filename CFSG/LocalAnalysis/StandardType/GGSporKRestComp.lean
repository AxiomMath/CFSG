module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestDefs
public import CFSG.Assembly.Subnormal
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly

private theorem ggSporKRestComp_map_pCore_of_normal {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {N K : Subgroup G} (hNK : N ≤ K) (hN : (N.subgroupOf K).Normal) :
    (CFSG.pCore p N).map N.subtype = N ⊓ (CFSG.pCore p K).map K.subtype := by
  have key := CFSG.LocalCores.prime_set_core_normal_intersection {q : Nat.Primes | q.val = p} hN
  rw [← CFSG.pCore_eq_piCore, ← CFSG.pCore_eq_piCore] at key
  have hmap := congrArg (Subgroup.map K.subtype) key
  rw [Subgroup.map_inf_eq _ _ _ K.subtype_injective, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.2 hNK, Subgroup.map_map] at hmap
  rw [← hmap, ← CFSG.pCore_map_iso p (Subgroup.subgroupOfEquivOfLe hNK), Subgroup.map_map]
  rfl

private theorem ggSporKRestComp_index_ne_two_of_isPerfect {E : Type*} [Group E]
    [Group.IsPerfect E] (D : Subgroup E) : D.index ≠ 2 := by
  intro h2
  have : D.Normal := Subgroup.normal_of_index_eq_two h2
  have hcard : Nat.card (E ⧸ D) = 2 := h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsCyclic (E ⧸ D) := isCyclic_of_prime_card hcard
  have : IsMulCommutative (E ⧸ D) := inferInstance
  have : Subsingleton (E ⧸ D) := Group.IsPerfect.subsingleton_of_isMulCommutative
  have h1 : Nat.card (E ⧸ D) = 1 := Nat.card_unique
  omega

theorem ggSporKRest_component_transfer {W : Type} [Group W] [Finite W] {H N : Subgroup W}
    (hNH : N ≤ H) (hN : (N.subgroupOf H).Normal) (hidx : (N.subgroupOf H).index ≤ 2)
    (C : Subgroup (GGHypQuot H)) (hC : IsComponentOf C ⊤) :
    ∃ C' : Subgroup (↥N ⧸ CFSG.pCore 2 ↥N), IsComponentOf C' ⊤ ∧ Nonempty (↥C ≃* ↥C') := by
  let ι : ↥N →* ↥H := Subgroup.inclusion hNH
  let π : ↥H →* GGHypQuot H := QuotientGroup.mk' (CFSG.pCore 2 ↥H)
  let φ : ↥N →* GGHypQuot H := π.comp ι
  have hker : φ.ker = CFSG.pCore 2 ↥N := by
    ext n
    rw [MonoidHom.mem_ker]
    constructor
    · intro hn
      have h1 : ι n ∈ CFSG.pCore 2 ↥H :=
        (QuotientGroup.eq_one_iff (ι n)).1 (by
          simpa only [φ, MonoidHom.comp_apply, π, QuotientGroup.mk'_apply] using hn)
      have h2 : (n : W) ∈ (CFSG.pCore 2 ↥N).map N.subtype := by
        rw [ggSporKRestComp_map_pCore_of_normal hNH hN]
        exact ⟨n.2, (Subgroup.mem_map_iff_mem Subtype.val_injective).2 h1⟩
      exact (Subgroup.mem_map_iff_mem Subtype.val_injective).1 h2
    · intro hn
      have h2 : (n : W) ∈ (CFSG.pCore 2 ↥N).map N.subtype :=
        (Subgroup.mem_map_iff_mem Subtype.val_injective).2 hn
      rw [ggSporKRestComp_map_pCore_of_normal hNH hN] at h2
      have h1 : ι n ∈ CFSG.pCore 2 ↥H :=
        (Subgroup.mem_map_iff_mem Subtype.val_injective).1 h2.2
      simpa only [φ, MonoidHom.comp_apply, π, QuotientGroup.mk'_apply] using
        (QuotientGroup.eq_one_iff (ι n)).2 h1
  let θ : ↥N ⧸ CFSG.pCore 2 ↥N →* GGHypQuot H :=
    QuotientGroup.lift (CFSG.pCore 2 ↥N) φ (le_of_eq hker.symm)
  have hθmk : ∀ n : ↥N, θ (QuotientGroup.mk n) = φ n := by
    intro n
    exact QuotientGroup.lift_mk (CFSG.pCore 2 ↥N) (le_of_eq hker.symm) n
  have hθinj : Function.Injective θ := by
    rw [QuotientGroup.injective_lift_iff]
    exact hker.symm
  have hRrange : θ.range = (N.subgroupOf H).map π := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine Quotient.inductionOn x ?_
      intro n
      exact ⟨ι n, n.2, (hθmk n).symm⟩
    · rintro ⟨z, hz, rfl⟩
      let n : ↥N := ⟨(z : W), Subgroup.mem_subgroupOf.mp hz⟩
      refine ⟨QuotientGroup.mk n, ?_⟩
      have hι : ι n = z := Subtype.ext rfl
      rw [hθmk]
      change π (ι n) = π z
      rw [hι]
  have hRnorm : ((N.subgroupOf H).map π).Normal :=
    hN.map π (QuotientGroup.mk'_surjective _)
  have hRindex : ((N.subgroupOf H).map π).index ≤ 2 := by
    have hdvd : ((N.subgroupOf H).map π).index ∣ (N.subgroupOf H).index :=
      Subgroup.index_map_dvd (N.subgroupOf H) (QuotientGroup.mk'_surjective _)
    have hpos : 0 < (N.subgroupOf H).index :=
      Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := N.subgroupOf H))
    exact le_trans (Nat.le_of_dvd hpos hdvd) hidx
  have hC_le_R : C ≤ (N.subgroupOf H).map π := by
    haveI : Group.IsPerfect ↥C := ⟨hC.2.2.1⟩
    haveI : ((N.subgroupOf H).map π).Normal := hRnorm
    have hDindex : (((N.subgroupOf H).map π).subgroupOf C).index ≤ 2 := by
      have hdvd : ((N.subgroupOf H).map π).relIndex C ∣ ((N.subgroupOf H).map π).index :=
        Subgroup.relIndex_dvd_index_of_normal _ _
      have hpos : 0 < ((N.subgroupOf H).map π).index :=
        Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := (N.subgroupOf H).map π))
      exact le_trans (Nat.le_of_dvd hpos hdvd) hRindex
    have hDtop : (((N.subgroupOf H).map π).subgroupOf C) = ⊤ := by
      have hne2 : (((N.subgroupOf H).map π).subgroupOf C).index ≠ 2 :=
        ggSporKRestComp_index_ne_two_of_isPerfect _
      have hne0 : (((N.subgroupOf H).map π).subgroupOf C).index ≠ 0 :=
        Subgroup.index_ne_zero_of_finite (H := ((N.subgroupOf H).map π).subgroupOf C)
      exact Subgroup.index_eq_one.mp (by omega)
    intro c hc
    have : (⟨c, hc⟩ : ↥C) ∈ ((N.subgroupOf H).map π).subgroupOf C := by
      rw [hDtop]
      trivial
    exact Subgroup.mem_subgroupOf.mp this
  have hC_le_range : C ≤ θ.range := by
    rw [hRrange]
    exact hC_le_R
  have hmap : (C.comap θ).map θ = C := Subgroup.map_comap_eq_self hC_le_range
  have e : ↥(C.comap θ) ≃* ↥C :=
    (Subgroup.equivMapOfInjective (C.comap θ) θ hθinj).trans (MulEquiv.subgroupCongr hmap)
  refine ⟨C.comap θ, ⟨le_top, ?_, ?_⟩, ⟨e.symm⟩⟩
  · have hsub := hC.2.1.comap θ
    rwa [Subgroup.comap_top] at hsub
  · exact CFSG.Assembly.IsQuasisimple.of_mulEquiv e hC.2.2

theorem ggSporKRest_unmarked_of_solvable {X : Type} [Group X] (h : Group.IsSolvable X) :
    SporKRestUnmarked X := by
  intro C hC hmark
  haveI : Group.IsSolvable X := h
  haveI : Group.IsSolvable (X ⧸ CFSG.pCore 2 X) :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)
  haveI : Group.IsSolvable ↥C := inferInstance
  haveI : Group.IsPerfect ↥C := ⟨hC.2.2.1⟩
  rcases subsingleton_or_nontrivial ↥C with hsub | hnt
  · haveI : Subsingleton ↥C := hsub
    haveI : Subsingleton (↥C ⧸ Subgroup.center ↥C) := inferInstance
    haveI : Nontrivial (↥C ⧸ Subgroup.center ↥C) := hC.2.2.2.toNontrivial
    obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial (↥C ⧸ Subgroup.center ↥C)).exists_pair_ne
    exact hab (Subsingleton.elim a b)
  · exact (Group.IsPerfect.not_isSolvable ↥C) inferInstance

theorem ggSporKRest_exists_component_of_layer {X : Type} [Group X]
    (h : LargeEvenLayer (⊤ : Subgroup X) ≠ ⊥) : ∃ C : Subgroup X, IsComponentOf C ⊤ := by
  by_contra hc
  push Not at hc
  apply h
  have hset : {K : Subgroup X | IsComponentOf K ⊤} = ∅ := by
    ext K
    simp [hc K]
  show LargeEvenLayer (⊤ : Subgroup X) = ⊥
  rw [show LargeEvenLayer (⊤ : Subgroup X) = sSup {K : Subgroup X | IsComponentOf K ⊤} from rfl,
    hset, sSup_empty]

end CFSG.StandardType.SporadicShape
