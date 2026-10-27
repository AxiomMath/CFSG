module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma43Gen
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G]

@[expose] def compSet (X : Subgroup G) : Set (Subgroup G) :=
  {K | K ≤ X ∧ IsQuasisimple K ∧ (K.subgroupOf X).IsSubnormal}

theorem lay_eq_sSup (X : Subgroup G) : Lay X = sSup (compSet X) := by
  apply le_antisymm
  · rw [Lay, inSubgroup, layer.eq_sSup, Subgroup.map_le_iff_le_comap]
    refine sSup_le fun C hC => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    refine le_sSup ⟨Subgroup.map_subtype_le _,
      LocalCores.isQuasisimple_of_mulEquiv (C.equivMapOfInjective X.subtype X.subtype_injective)
        hC.1, ?_⟩
    have : (C.map X.subtype).subgroupOf X = C :=
      Subgroup.comap_map_eq_self_of_injective X.subtype_injective C
    rw [this]
    exact hC.2
  · refine sSup_le fun K ⟨hKX, hq, hs⟩ => ?_
    have hK : K = (K.subgroupOf X).map X.subtype := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hKX]
    rw [hK]
    exact Subgroup.map_mono (le_sSup
      ⟨LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKX).symm hq, hs⟩)

theorem le_of_isPerfect_of_solvable_quot {H N K : Subgroup G} (hKH : K ≤ H)
    [(N.subgroupOf H).Normal] [Group.IsSolvable (↥H ⧸ N.subgroupOf H)]
    [hK : Group.IsPerfect K] : K ≤ N := by
  haveI : Group.IsPerfect (K.subgroupOf H) :=
    Group.IsPerfect.ofSurjective (G := K) (f := (Subgroup.subgroupOfEquivOfLe hKH).symm.toMonoidHom)
      (MulEquiv.surjective _)
  let π := QuotientGroup.mk' (N.subgroupOf H)
  haveI : Group.IsPerfect ((K.subgroupOf H).map π) := Group.IsPerfect.map _
  have hP : (K.subgroupOf H).map π = ⊥ := by
    by_contra hne
    haveI : Nontrivial ((K.subgroupOf H).map π) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    exact Group.IsPerfect.not_isSolvable ((K.subgroupOf H).map π) inferInstance
  have hle : K.subgroupOf H ≤ N.subgroupOf H := by
    rw [← QuotientGroup.ker_mk' (N.subgroupOf H)]
    exact (Subgroup.map_eq_bot_iff _).mp hP
  exact LocalCores.le_of_subgroupOf_le hKH hle

theorem lay_eq_of_normal {X Y : Subgroup G} (hYX : Y ≤ X) [(Y.subgroupOf X).Normal]
    (hperf : ∀ K : Subgroup G, K ≤ X → Group.IsPerfect K → K ≤ Y) : Lay X = Lay Y := by
  rw [lay_eq_sSup, lay_eq_sSup]
  congr 1
  ext K
  let e := Subgroup.subgroupOfEquivOfLe hYX
  have hcomap : ∀ K : Subgroup G,
      (K.subgroupOf X).subgroupOf (Y.subgroupOf X) = (K.subgroupOf Y).comap e.toMonoidHom :=
    fun K => by ext x; rfl
  constructor
  · rintro ⟨hKX, hq, hs⟩
    haveI := hq.1
    have hKY : K ≤ Y := hperf K hKX hq.1
    refine ⟨hKY, hq, ?_⟩
    have h1 := hs.subgroupOf (K := Y.subgroupOf X)
    rw [hcomap] at h1
    have h2 := h1.map (f := e.toMonoidHom) e.surjective
    rwa [Subgroup.map_comap_eq_self_of_surjective e.surjective] at h2
  · rintro ⟨hKY, hq, hs⟩
    refine ⟨hKY.trans hYX, hq, ?_⟩
    refine Subgroup.IsSubnormal.trans (K := Y.subgroupOf X) (fun x hx => hKY hx) ?_
      (Subgroup.Normal.isSubnormal inferInstance)
    rw [hcomap]
    exact hs.comap _

theorem nor_lay_of_nor {X : Subgroup G} {v : G} (hv : v ∈ Nor X) : v ∈ Nor (Lay X) := by
  have key : ∀ {v : G}, v ∈ Nor X → ∀ z ∈ Lay X, v * z * v⁻¹ ∈ Lay X := by
    intro v hv z hz
    obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
    let φ := normAut X (MulEquiv.refl ↥X) ⟨v, hv⟩
    have hφ : φ z' ∈ layer ↥X := by
      haveI := CFSG.LocalCores.layer_characteristic (G := ↥X)
      have := (Subgroup.characteristic_iff_le_comap.mp this) φ
      exact this hz'
    refine Subgroup.mem_map.mpr ⟨φ z', hφ, ?_⟩
    have := normAut_apply X (MulEquiv.refl ↥X) ⟨v, hv⟩ z'
    simpa using this
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨fun hx => key hv x hx, fun hx => by
    have := key ((Nor X).inv_mem hv) _ hx
    simpa [mul_assoc] using this⟩

end CFSG.RankThree.PartTwo.Sec21.FF79
