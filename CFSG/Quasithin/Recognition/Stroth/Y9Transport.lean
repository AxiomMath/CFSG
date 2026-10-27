module

public import CFSG.Quasithin.Background.F1Amalgam

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique

theorem iso_map_inter_of_equiv {X Y Z : Type} [Group X] [Group Y] [Group Z]
    {P1 P2 : Subgroup X} {M1 M2 : Subgroup Y} {Q1 Q2 : Subgroup Z}
    (e : (RankTwoAmalgam.ofSubgroups P1 P2).Iso (RankTwoAmalgam.ofSubgroups M1 M2))
    (ε : Y ≃* Z) (e1 : (RankTwoAmalgam.ofSubgroups M1 M2).G1 ≃* ↥Q1)
    (hQ : (M1 ⊓ M2).map ε.toMonoidHom = Q1 ⊓ Q2)
    (he1 : ∀ x : (RankTwoAmalgam.ofSubgroups M1 M2).G1, (e1 x : Z) = ε x.1) :
    ((P1 ⊓ P2).subgroupOf P1).map (e.φ1.trans e1).toMonoidHom =
      (Q1 ⊓ Q2).subgroupOf Q1 := by
  let ψ1 : ↥P1 ≃* ↥Q1 := e.φ1.trans e1
  ext y
  constructor
  · rintro ⟨b, hb, rfl⟩
    have hb' : b.1 ∈ P1 ⊓ P2 := hb
    let g1 : ↥(P1 ⊓ P2) := ⟨b.1, hb'⟩
    have hc : (e.φ12 g1).1 = (e.φ1 b).1 := by
      have h := congrArg (fun z : ↥M1 => z.1) (e.comm1 g1)
      change ((e.φ12 g1).1) = (e.φ1 b).1 at h
      exact h
    have hmem : (ε (e.φ1 b).1) ∈ (M1 ⊓ M2).map ε.toMonoidHom := by
      rw [← hc]
      exact ⟨(e.φ12 g1).1, (e.φ12 g1).2, rfl⟩
    rw [hQ] at hmem
    have hcoee : (e1 (e.φ1 b)).1 = ε (e.φ1 b).1 := he1 (e.φ1 b)
    refine Subgroup.mem_subgroupOf.2 ⟨(ψ1 b).2, ?_⟩
    change (e1 (e.φ1 b)).1 ∈ Q2
    rw [hcoee]
    exact hmem.2
  · rintro hy
    have hy' : (y : Z) ∈ (M1 ⊓ M2).map ε.toMonoidHom := by
      rw [hQ]
      exact hy
    obtain ⟨m, hm, hme⟩ := hy'
    let m12 : ↥(M1 ⊓ M2) := ⟨m, hm⟩
    let g : ↥(P1 ⊓ P2) := e.φ12.symm m12
    let b : ↥P1 := ⟨g.1, g.2.1⟩
    refine ⟨b, Subgroup.mem_subgroupOf.2 g.2, ?_⟩
    have hg : e.φ12 g = m12 := MulEquiv.apply_symm_apply e.φ12 m12
    have hc : (e.φ1 b).1 = m := by
      have h := congrArg (fun z : ↥M1 => z.1) (e.comm1 g)
      change ((e.φ12 g).1) = (e.φ1 b).1 at h
      rw [hg] at h
      exact h.symm
    apply Subtype.ext
    change (e1 (e.φ1 b)).1 = (y : Z)
    rw [he1 (e.φ1 b), hc]
    exact hme

theorem iso_map_inter_of_equiv_right {X Y Z : Type} [Group X] [Group Y] [Group Z]
    {P1 P2 : Subgroup X} {M1 M2 : Subgroup Y} {Q1 Q2 : Subgroup Z}
    (e : (RankTwoAmalgam.ofSubgroups P1 P2).Iso (RankTwoAmalgam.ofSubgroups M1 M2))
    (ε : Y ≃* Z) (e2 : (RankTwoAmalgam.ofSubgroups M1 M2).G2 ≃* ↥Q2)
    (hQ : (M1 ⊓ M2).map ε.toMonoidHom = Q1 ⊓ Q2)
    (he2 : ∀ x : (RankTwoAmalgam.ofSubgroups M1 M2).G2, (e2 x : Z) = ε x.1) :
    ((P1 ⊓ P2).subgroupOf P2).map (e.φ2.trans e2).toMonoidHom =
      (Q1 ⊓ Q2).subgroupOf Q2 := by
  let ψ2 : ↥P2 ≃* ↥Q2 := e.φ2.trans e2
  ext y
  constructor
  · rintro ⟨b, hb, rfl⟩
    have hb' : b.1 ∈ P1 ⊓ P2 := hb
    let g1 : ↥(P1 ⊓ P2) := ⟨b.1, hb'⟩
    have hc : (e.φ12 g1).1 = (e.φ2 b).1 := by
      have h := congrArg (fun z : ↥M2 => z.1) (e.comm2 g1)
      change ((e.φ12 g1).1) = (e.φ2 b).1 at h
      exact h
    have hmem : (ε (e.φ2 b).1) ∈ (M1 ⊓ M2).map ε.toMonoidHom := by
      rw [← hc]
      exact ⟨(e.φ12 g1).1, (e.φ12 g1).2, rfl⟩
    rw [hQ] at hmem
    have hcoee : (e2 (e.φ2 b)).1 = ε (e.φ2 b).1 := he2 (e.φ2 b)
    refine Subgroup.mem_subgroupOf.2 ⟨?_, (ψ2 b).2⟩
    change (e2 (e.φ2 b)).1 ∈ Q1
    rw [hcoee]
    exact hmem.1
  · rintro hy
    have hy' : (y : Z) ∈ (M1 ⊓ M2).map ε.toMonoidHom := by
      rw [hQ]
      exact hy
    obtain ⟨m, hm, hme⟩ := hy'
    let m12 : ↥(M1 ⊓ M2) := ⟨m, hm⟩
    let g : ↥(P1 ⊓ P2) := e.φ12.symm m12
    let b : ↥P2 := ⟨g.1, g.2.2⟩
    refine ⟨b, Subgroup.mem_subgroupOf.2 g.2, ?_⟩
    have hg : e.φ12 g = m12 := MulEquiv.apply_symm_apply e.φ12 m12
    have hc : (e.φ2 b).1 = m := by
      have h := congrArg (fun z : ↥M2 => z.1) (e.comm2 g)
      change ((e.φ12 g).1) = (e.φ2 b).1 at h
      rw [hg] at h
      exact h.symm
    apply Subtype.ext
    change (e2 (e.φ2 b)).1 = (y : Z)
    rw [he2 (e.φ2 b), hc]
    exact hme

theorem perfect_of_isPerfect_oTwoQuot {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hperf : Group.IsPerfect (oTwoQuot ↥L)) (hO : pCoreOf 2 L ≤ ⁅L, L⁆) :
    ⁅L, L⁆ = L := by
  let π : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (pCore 2 ↥L)
  have hmap : (commutator ↥L).map π = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
    exact Group.IsPerfect.commutator_eq_top
  have hsup : commutator ↥L ⊔ pCore 2 ↥L = ⊤ := by
    have := Subgroup.comap_map_eq π (commutator ↥L)
    rw [hmap, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
    exact this.symm
  have hle : pCore 2 ↥L ≤ commutator ↥L := by
    intro x hx
    have h1 : (x : G) ∈ ⁅L, L⁆ := hO (Subgroup.mem_map_of_mem L.subtype hx)
    rw [← Subgroup.map_subtype_commutator] at h1
    obtain ⟨y, hy, hyx⟩ := h1
    rwa [← L.subtype_injective hyx]
  rw [sup_eq_left.mpr hle] at hsup
  have := congrArg (Subgroup.map L.subtype) hsup
  rwa [Subgroup.map_subtype_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at this

theorem pCoreOf_sup_eq_of_sylow_le {G : Type} [Group G] [Finite G]
    {L B S : Subgroup G} (hBL : B ≤ Subgroup.normalizer (L : Set G))
    (hS : IsSylowTwoOf S (L ⊔ B)) (hSL : S ≤ L) :
    pCoreOf 2 (L ⊔ B) = pCoreOf 2 L := by
  have hPL : pCoreOf 2 (L ⊔ B) ≤ L :=
    (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hS).trans hSL
  refine le_antisymm ?_ ?_
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer
      (r := 2) (N := pCoreOf 2 (L ⊔ B)) (H := L) hPL
      (le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ B)))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ B))
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer
      (r := 2) (N := pCoreOf 2 L) (H := L ⊔ B)
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left)
      (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
        (hBL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)

theorem le_of_isSylowTwoOf_normal {G : Type} [Group G] [Finite G]
    {U H T : Subgroup G} (hU : IsSylowTwoOf U H)
    (hUn : (U.subgroupOf H).Normal) (hT : T ≤ H) (hTp : IsPGroup 2 T) : T ≤ U := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ↥H := Subtype.finite
  haveI : Finite (Sylow 2 ↥H) := inferInstance
  have hT' : IsPGroup 2 (T.subgroupOf H) :=
    hTp.of_equiv (Subgroup.subgroupOfEquivOfLe hT).symm
  obtain ⟨P, hTP⟩ := hT'.exists_le_sylow
  have hU' : IsPGroup 2 (U.subgroupOf H) :=
    hU.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hU.1).symm
  let P₀ : Sylow 2 H := hU'.toSylow hU.2.2
  have hP₀coe : (P₀ : Subgroup H) = U.subgroupOf H := rfl
  have hP₀n : (P₀ : Subgroup H).Normal := by rw [hP₀coe]; exact hUn
  letI : Unique (Sylow 2 ↥H) := Sylow.unique_of_normal P₀ hP₀n
  have huniq : P = P₀ := Subsingleton.elim P P₀
  intro x hx
  have hxP : (⟨x, hT hx⟩ : H) ∈ P := hTP hx
  rw [huniq] at hxP
  change (⟨x, hT hx⟩ : H) ∈ (P₀ : Subgroup H) at hxP
  rw [hP₀coe] at hxP
  exact Subgroup.mem_subgroupOf.mp hxP

end CFSG.Quasithin.Stroth
