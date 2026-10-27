module

public import CFSG.RankThree.GroupTheory.SteinbergBYAlphaTransport

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBY

open CFSG CFSG.RankThree.GroupTheory

variable {G : Type*} [Group G]

theorem isPGroup_inSubgroup_pCore (p : ℕ) (X : Subgroup G) :
    IsPGroup p (inSubgroup (pCore p) X) :=
  pCore_isPGroup.map X.subtype

theorem inSubgroup_pCore_le (p : ℕ) (X : Subgroup G) : inSubgroup (pCore p) X ≤ X :=
  Subgroup.map_subtype_le _

theorem le_inSubgroup_pCore {p : ℕ} {Q X : Subgroup G} (hQ : IsPGroup p Q) (hQX : Q ≤ X)
    (hXQ : X ≤ Subgroup.normalizer (Q : Set G)) : Q ≤ inSubgroup (pCore p) X := by
  have hn : (Q.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQX).mpr hXQ
  have hp : IsPGroup p (Q.subgroupOf X) := hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQX).symm
  have hle : Q.subgroupOf X ≤ pCore p X := le_sSup ⟨hn, hp⟩
  intro x hx
  exact ⟨⟨x, hQX hx⟩, hle hx, rfl⟩

theorem normalizer_le_normalizer_inSubgroup_pCore (p : ℕ) (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (inSubgroup (pCore p) X : Set G) :=
  fun _ hg => mem_normalizer_of_map_conj_eq (by
    rw [map_inSubgroup_pCore, map_conj_eq_of_mem_normalizer hg])

theorem le_normalizer_inSubgroup_pCore (p : ℕ) (X : Subgroup G) :
    X ≤ Subgroup.normalizer (inSubgroup (pCore p) X : Set G) :=
  Subgroup.le_normalizer.trans (normalizer_le_normalizer_inSubgroup_pCore p X)

theorem mem_normalizer_inf {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA x, hB x]

theorem inf_inSubgroup_pCore_le {p : ℕ} {X Y : Subgroup G} (hYX : Y ≤ X) :
    Y ⊓ inSubgroup (pCore p) X ≤ inSubgroup (pCore p) Y :=
  le_inSubgroup_pCore ((isPGroup_inSubgroup_pCore p X).to_le inf_le_right) inf_le_left
    fun _ hy => mem_normalizer_inf (Subgroup.le_normalizer hy)
      (le_normalizer_inSubgroup_pCore p X (hYX hy))

theorem inSubgroup_pCore_mono {p : ℕ} {X Y : Subgroup G} (hYX : Y ≤ X)
    (hXY : X ≤ Subgroup.normalizer (Y : Set G)) :
    inSubgroup (pCore p) Y ≤ inSubgroup (pCore p) X :=
  le_inSubgroup_pCore (isPGroup_inSubgroup_pCore p Y) ((inSubgroup_pCore_le p Y).trans hYX)
    (hXY.trans (normalizer_le_normalizer_inSubgroup_pCore p Y))

theorem inSubgroup_pCore_eq_inf {p : ℕ} {X Y : Subgroup G} (hYX : Y ≤ X)
    (hXY : X ≤ Subgroup.normalizer (Y : Set G)) :
    inSubgroup (pCore p) Y = Y ⊓ inSubgroup (pCore p) X :=
  le_antisymm (le_inf (inSubgroup_pCore_le p Y) (inSubgroup_pCore_mono hYX hXY))
    (inf_inSubgroup_pCore_le hYX)

theorem inSubgroup_pCore_top (p : ℕ) : inSubgroup (pCore p) (⊤ : Subgroup G) = pCore p G := by
  rw [inSubgroup, ← pCore_map_iso p (Subgroup.topEquiv (G := G))]
  rfl

theorem centralizer_singleton_eq_centralizer_zpowers (c : G) :
    Subgroup.centralizer ({c} : Set G) =
      Subgroup.centralizer (Subgroup.zpowers c : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem map_subtype_centralizer_singleton (C : Subgroup G) (b : C) :
    (Subgroup.centralizer ({b} : Set C)).map C.subtype =
      C ⊓ Subgroup.centralizer ({(b : G)} : Set G) := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.coe_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, by simpa using congrArg Subtype.val hy⟩
  · rintro ⟨hx, hxb⟩
    exact ⟨⟨x, hx⟩, Subtype.ext hxb, rfl⟩

theorem map_subtype_inSubgroup_pCore_centralizer (p : ℕ) (C : Subgroup G) (b : C) :
    (inSubgroup (pCore p) (Subgroup.centralizer ({b} : Set C))).map C.subtype =
      inSubgroup (pCore p) (C ⊓ Subgroup.centralizer ({(b : G)} : Set G)) := by
  rw [map_inSubgroup_pCore_of_injective p C.subtype C.subtype_injective,
    map_subtype_centralizer_singleton]

end CFSG.RankThree.GroupTheory.SteinbergBY
