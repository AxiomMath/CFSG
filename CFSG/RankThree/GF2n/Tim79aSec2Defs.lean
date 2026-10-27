module

public import CFSG.CGT.Timmesfeld75.Sec3Root
public import CFSG.RankThree.GF2n.Basic

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G]

@[expose] def eOf (H : Subgroup G) : Subgroup G :=
  inSubgroup (pCore 2) H ⊓ Subgroup.centralizer (inSubgroup (pCore 2) H : Set G)

@[expose] def omegaOf (V H : Subgroup G) : Set (Subgroup G) :=
  {U | ∃ h ∈ H, U = conjSubgroup h V}

@[expose] def xOf (V H : Subgroup G) : Subgroup G :=
  ⨆ U ∈ omegaOf V H, U

@[expose] def wOf (V H : Subgroup G) : Subgroup G :=
  ⨆ U ∈ omegaOf V H, U ⊓ inSubgroup (pCore 2) H

@[expose] def dOf (V H : Subgroup G) : Set G :=
  {d | d ≠ 1 ∧ ∃ U ∈ omegaOf V H, d ∈ U}

theorem mem_omegaOf {V H U : Subgroup G} :
    U ∈ omegaOf V H ↔ ∃ h ∈ H, U = conjSubgroup h V := Iff.rfl

theorem conjSubgroup_mem_omegaOf {V H : Subgroup G} {h : G} (hh : h ∈ H) :
    conjSubgroup h V ∈ omegaOf V H := ⟨h, hh, rfl⟩

theorem conjSubgroup_mem_omegaOf_of_mem {V H U : Subgroup G} (hU : U ∈ omegaOf V H) {h : G}
    (hh : h ∈ H) : conjSubgroup h U ∈ omegaOf V H := by
  obtain ⟨g, hg, rfl⟩ := hU
  exact ⟨h * g, H.mul_mem hh hg, conjSubgroup_conjSubgroup h g V⟩

theorem le_xOf {V H U : Subgroup G} (hU : U ∈ omegaOf V H) : U ≤ xOf V H :=
  le_iSup₂_of_le U hU le_rfl

theorem inf_pCore_le_wOf {V H U : Subgroup G} (hU : U ∈ omegaOf V H) :
    U ⊓ inSubgroup (pCore 2) H ≤ wOf V H :=
  le_iSup₂_of_le U hU le_rfl

theorem wOf_le_pCore (V H : Subgroup G) : wOf V H ≤ inSubgroup (pCore 2) H :=
  iSup₂_le fun _ _ => inf_le_right

theorem wOf_le_H (V H : Subgroup G) : wOf V H ≤ H :=
  (wOf_le_pCore V H).trans (inSubgroup_pCore_two H).2.1

theorem wOf_le_xOf (V H : Subgroup G) : wOf V H ≤ xOf V H :=
  iSup₂_le fun _ hU => inf_le_left.trans (le_xOf hU)

theorem xOf_le_H {V H : Subgroup G} (hVH : V ≤ H) : xOf V H ≤ H :=
  iSup₂_le fun U hU => by
    obtain ⟨h, hh, rfl⟩ := hU
    exact conjSubgroup_le_of_le_of_mem hVH hh

theorem H_le_normalizer_xOf (V H : Subgroup G) : H ≤ Subgroup.normalizer (xOf V H : Set G) := by
  intro h hh
  rw [mem_normalizer_iff_conjSubgroup_eq]
  have hmap : conjSubgroup h (xOf V H) = ⨆ U ∈ omegaOf V H, conjSubgroup h U := by
    unfold conjSubgroup xOf
    simp only [Subgroup.map_iSup]
  rw [hmap]
  refine le_antisymm (iSup₂_le fun U hU => le_iSup₂_of_le (conjSubgroup h U)
    (conjSubgroup_mem_omegaOf_of_mem hU hh) le_rfl) (iSup₂_le fun U hU => ?_)
  refine le_iSup₂_of_le (conjSubgroup h⁻¹ U) (conjSubgroup_mem_omegaOf_of_mem hU (H.inv_mem hh)) ?_
  rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]

theorem H_le_normalizer_wOf (V H : Subgroup G) : H ≤ Subgroup.normalizer (wOf V H : Set G) := by
  intro h hh
  rw [mem_normalizer_iff_conjSubgroup_eq]
  have hO : conjSubgroup h (inSubgroup (pCore 2) H) = inSubgroup (pCore 2) H :=
    mem_normalizer_iff_conjSubgroup_eq.mp ((inSubgroup_pCore_two H).2.2 hh)
  have hmap : conjSubgroup h (wOf V H) =
      ⨆ U ∈ omegaOf V H, conjSubgroup h U ⊓ inSubgroup (pCore 2) H := by
    unfold wOf
    unfold conjSubgroup
    simp only [Subgroup.map_iSup]
    refine iSup_congr fun U => iSup_congr fun _ => ?_
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj h).injective]
    exact congrArg (fun K => Subgroup.map (MulAut.conj h).toMonoidHom U ⊓ K) hO
  rw [hmap]
  refine le_antisymm (iSup₂_le fun U hU => le_iSup₂_of_le (conjSubgroup h U)
    (conjSubgroup_mem_omegaOf_of_mem hU hh) le_rfl) (iSup₂_le fun U hU => ?_)
  refine le_iSup₂_of_le (conjSubgroup h⁻¹ U) (conjSubgroup_mem_omegaOf_of_mem hU (H.inv_mem hh)) ?_
  rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]

instance wOf_normal (V H : Subgroup G) : ((wOf V H).subgroupOf H).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (wOf_le_H V H)).2 (H_le_normalizer_wOf V H)

theorem H_le_normalizer_eOf (H : Subgroup G) : H ≤ Subgroup.normalizer (eOf H : Set G) :=
  fun _ hh => mem_normalizer_inf ((inSubgroup_pCore_two H).2.2 hh)
    (mem_normalizer_centralizer ((inSubgroup_pCore_two H).2.2 hh))

theorem eOf_le_pCore (H : Subgroup G) : eOf H ≤ inSubgroup (pCore 2) H := inf_le_left

theorem isMulCommutative_eOf (H : Subgroup G) : IsMulCommutative (eOf H) :=
  ⟨⟨fun x y => Subtype.ext
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp x.2).2 y
      (Subgroup.mem_inf.mp y.2).1).symm⟩⟩

theorem isPGroup_pCore (H : Subgroup G) : IsPGroup 2 (inSubgroup (pCore 2) H) :=
  (inSubgroup_pCore_two H).1

theorem dOf_eq_classDIn (V H : Subgroup G) : dOf V H = classDIn H V := by
  ext d
  constructor
  · rintro ⟨hd1, U, ⟨h, hh, rfl⟩, hdU⟩
    exact ⟨hd1, h, hh, hdU⟩
  · rintro ⟨hd1, h, hh, hdU⟩
    exact ⟨hd1, conjSubgroup h V, ⟨h, hh, rfl⟩, hdU⟩

abbrev Hbar (V H : Subgroup G) : Type := ↥H ⧸ (wOf V H).subgroupOf H

@[expose] def piBar (V H : Subgroup G) : ↥H →* Hbar V H := QuotientGroup.mk' _

@[expose] def barOf (V H S : Subgroup G) : Subgroup (Hbar V H) :=
  (S.subgroupOf H).map (piBar V H)

@[expose] def dbarOf (V H : Subgroup G) : Set (Hbar V H) :=
  piBar V H '' {x : ↥H | (x : G) ∈ dOf V H ∧ (x : G) ∉ wOf V H}

theorem piBar_eq_one_iff {V H : Subgroup G} (x : ↥H) :
    piBar V H x = 1 ↔ (x : G) ∈ wOf V H :=
  (QuotientGroup.eq_one_iff x).trans Subgroup.mem_subgroupOf

theorem mem_barOf_iff {V H S : Subgroup G} {y : Hbar V H} :
    y ∈ barOf V H S ↔ ∃ x : ↥H, (x : G) ∈ S ∧ piBar V H x = y := by
  simp only [barOf, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem piBar_surjective (V H : Subgroup G) : Function.Surjective (piBar V H) :=
  QuotientGroup.mk'_surjective _

theorem mem_dbarOf_iff {V H : Subgroup G} {y : Hbar V H} :
    y ∈ dbarOf V H ↔ ∃ x : ↥H, (x : G) ∈ dOf V H ∧ (x : G) ∉ wOf V H ∧ piBar V H x = y := by
  simp only [dbarOf, Set.mem_image, Set.mem_setOf_eq, and_assoc]

end CFSG.RankThree.GF2n.Tim79a
