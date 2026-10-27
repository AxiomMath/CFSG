module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddChain

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)

private theorem map_conjugate_subgroupOf {G : Type} [Group G] {Z C : Subgroup G} (hZC : Z ≤ C)
    (c : ↥C) :
    (CFSG.conjugate (Z.subgroupOf C) c).map C.subtype = CFSG.conjugate Z (c : G) := by
  unfold CFSG.conjugate
  calc
    ((Z.subgroupOf C).map (MulAut.conj c⁻¹).toMonoidHom).map C.subtype
        = (Z.subgroupOf C).map (C.subtype.comp (MulAut.conj c⁻¹).toMonoidHom) :=
          Subgroup.map_map _ _ _
    _ = (Z.subgroupOf C).map ((MulAut.conj (c : G)⁻¹).toMonoidHom.comp C.subtype) := rfl
    _ = ((Z.subgroupOf C).map C.subtype).map (MulAut.conj (c : G)⁻¹).toMonoidHom :=
          (Subgroup.map_map _ _ _).symm
    _ = (Z ⊓ C).map (MulAut.conj (c : G)⁻¹).toMonoidHom := by
          rw [Subgroup.subgroupOf_map_subtype]
    _ = Z.map (MulAut.conj (c : G)⁻¹).toMonoidHom := by
          rw [inf_of_le_left hZC]

private theorem map_mulAut_conj_subgroupOf {G : Type} [Group G] {Z C : Subgroup G} (hZC : Z ≤ C)
    (c : ↥C) :
    ((Z.subgroupOf C).map (MulAut.conj c)).map C.subtype =
      Z.map (MulAut.conj (c : G)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    exact Subgroup.mem_map.mpr ⟨z, hz, by simp [MulAut.conj_apply]⟩
  · intro hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr
      ⟨(MulAut.conj c) ⟨z, hZC hz⟩, Subgroup.mem_map.mpr
        ⟨⟨z, hZC hz⟩, Subgroup.mem_subgroupOf.mpr hz, rfl⟩, by simp [MulAut.conj_apply]⟩

theorem isWeaklyClosedIn_subgroupOf_normalizer {G : Type} [Group G] {Z C : Subgroup G}
    (hZC : Z ≤ C)
    (hwc : CFSG.ASVolI.ChIJK.IsWeaklyClosedIn Z (Subgroup.normalizer (Z : Set G))) :
    CFSG.ASVolI.ChIJK.IsWeaklyClosedIn (Z.subgroupOf C)
      (Subgroup.normalizer ((Z.subgroupOf C : Subgroup ↥C) : Set ↥C)) := by
  intro c hc
  unfold CFSG.conjugate at hc ⊢
  have hN : (Subgroup.normalizer ((Z.subgroupOf C : Subgroup ↥C) : Set ↥C)).map
      C.subtype ≤ Subgroup.normalizer (Z : Set G) := by
    intro x hx
    obtain ⟨c', hc', rfl⟩ := Subgroup.mem_map.mp hx
    have hmap' := congrArg (Subgroup.map C.subtype)
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp hc')
    rw [map_mulAut_conj_subgroupOf hZC c', Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hZC] at hmap'
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap'
  have hmap := map_conjugate_subgroupOf hZC c
  have hle : CFSG.conjugate Z (c : G) ≤ Subgroup.normalizer (Z : Set G) := by
    rw [← hmap]
    exact (Subgroup.map_mono (f := C.subtype) hc).trans hN
  have hEq := hwc (c : G) hle
  apply Subgroup.map_injective C.subtype_injective
  calc
    (CFSG.conjugate (Z.subgroupOf C) c).map C.subtype = CFSG.conjugate Z (c : G) := hmap
    _ = Z := hEq
    _ = (Z.subgroupOf C).map C.subtype := by
          rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hZC]

theorem isKGroup_centralizer_of_ne_bot {G : Type} [Group G] [Finite G] (hS : StandingGe3 G)
    {X : Subgroup G} (hX : X ≠ ⊥) :
    CFSG.Open.IsKGroup ↥(Subgroup.centralizer (X : Set G)) := by
  have hne : Subgroup.centralizer (X : Set G) ≠ ⊤ := by
    intro htop
    have hXZ : X ≤ Subgroup.center G := by
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro y
      have hy : y ∈ Subgroup.centralizer (X : Set G) := by rw [htop]; exact Subgroup.mem_top y
      exact ((Subgroup.mem_centralizer_iff.mp hy) x hx).symm
    have hcenter_ne_top : Subgroup.center G ≠ ⊤ := by
      intro hcenter
      obtain ⟨a, b, hne⟩ := hS.nonab
      have ha : a ∈ Subgroup.center G := by rw [hcenter]; exact Subgroup.mem_top a
      exact hne (Subgroup.mem_center_iff.mp ha b).symm
    have hcenter_bot : Subgroup.center G = ⊥ :=
      (hS.simple.eq_bot_or_eq_top_of_normal (Subgroup.center G)).resolve_right hcenter_ne_top
    exact hX (le_bot_iff.mp (hcenter_bot ▸ hXZ))
  exact hS.kProper.isKGroup _ hne

theorem pRank_top_le_three_of_mem_uniqueSet {G : Type} [Group G] [Finite G] {D : Data G}
    {C Z : Subgroup G} (hZU : Z ∈ uniqueSet D.M) (hZC : Z ≤ C) (hZcard : Nat.card Z = 3)
    (hrk : CFSG.Open.pRank 3 D.M ≤ 3) :
    CFSG.Open.pRank 3 (⊤ : Subgroup ↥C) ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ'card : Nat.card (Z.subgroupOf C) = 3 := by
    rw [← hZcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZC).toEquiv
  have hZp : IsPGroup 3 (Z.subgroupOf C) := IsPGroup.of_card (n := 1) (by rw [hZ'card]; norm_num)
  obtain ⟨S, hZS⟩ := hZp.exists_le_sylow
  have hS3 : IsPGroup 3 (S.map C.subtype) := (S.isPGroup').map C.subtype
  have hZS' : Z ≤ S.map C.subtype := by
    have h := Subgroup.map_mono (f := C.subtype) hZS
    rwa [Subgroup.subgroupOf_map_subtype, inf_of_le_left hZC] at h
  have hS'M : S.map C.subtype ≤ D.M :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.le_of_mem_uniqueSet_of_isPGroup
      D.maxLocal hZU hZS' hS3
  have hSyl := CFSG.SectionRank.pRank_sylow S
  have hmap : CFSG.Open.pRank 3 (S : Subgroup ↥C) =
      CFSG.Open.pRank 3 (S.map C.subtype) := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (S : Subgroup ↥C),
      CFSG.SectionRank.pRank_eq_pRank_top_subgroup (S.map C.subtype)]
    exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num)
      (Subgroup.equivMapOfInjective (S : Subgroup ↥C) C.subtype C.subtype_injective)
  calc
    CFSG.Open.pRank 3 (⊤ : Subgroup ↥C) = CFSG.Open.pRank 3 (S : Subgroup ↥C) := hSyl.1.symm
    _ = CFSG.Open.pRank 3 (S.map C.subtype) := hmap
    _ ≤ CFSG.Open.pRank 3 D.M :=
      CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hS'M
    _ ≤ 3 := hrk

private theorem centralizer_map_conj_le {G : Type} [Group G] {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    (Subgroup.centralizer (X : Set G)).map (MulAut.conj g).toMonoidHom ≤
      Subgroup.centralizer (X : Set G) := by
  have hg' : X.map (MulAut.conj g⁻¹).toMonoidHom = X :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.inv_mem _ hg)
  intro x hx
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hx
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro y hy
  have hy' : g⁻¹ * y * g ∈ X := by
    have h := Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hy
    rw [hg'] at h
    simpa [MulAut.conj_apply] using h
  have hcomm := hc (g⁻¹ * y * g) hy'
  change y * (MulAut.conj g c) = (MulAut.conj g c) * y
  calc
    y * (g * c * g⁻¹) = g * (g⁻¹ * y * g * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * y * g)) * g⁻¹ := by rw [hcomm]
    _ = (g * c * g⁻¹) * y := by group

theorem normalizer_le_of_centralizer_le_of_mem_uniqueSet_of_le {G : Type} [Group G] [Finite G]
    {D : Data G} {X Z : Subgroup G} (hZU : Z ∈ uniqueSet D.M)
    (hZC : Z ≤ Subgroup.centralizer (X : Set G)) (hCM : Subgroup.centralizer (X : Set G) ≤ D.M) :
    Subgroup.normalizer (X : Set G) ≤ D.M := by
  intro g hg
  have hg' : X.map (MulAut.conj g⁻¹).toMonoidHom = X :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.inv_mem _ hg)
  have hCmap : (Subgroup.centralizer (X : Set G)).map (MulAut.conj g).toMonoidHom ≤
      Subgroup.centralizer (X : Set G) := centralizer_map_conj_le hg
  have hZg : Z.map (MulAut.conj g).toMonoidHom ≤ D.M :=
    (Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hZC).trans (hCmap.trans hCM)
  have hZ_le : Z ≤ D.M.map (MulAut.conj g⁻¹).toMonoidHom := by
    intro z hz
    have hz' : g * z * g⁻¹ ∈ D.M := by
      have h := hZg (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hz)
      simpa [MulAut.conj_apply] using h
    refine Subgroup.mem_map.mpr ⟨g * z * g⁻¹, hz', ?_⟩
    change MulAut.conj g⁻¹ (g * z * g⁻¹) = z
    rw [MulAut.conj_apply]
    group
  have hMmap := hZU.2 g⁻¹ hZ_le
  have hgN : g⁻¹ ∈ Subgroup.normalizer (D.M : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hMmap
  rw [CFSG.RankThreeCoreUniqueness.Helpers.maxTwoLocal_self_normalizing D.M D.maxLocal] at hgN
  simpa using D.M.inv_mem hgN

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
