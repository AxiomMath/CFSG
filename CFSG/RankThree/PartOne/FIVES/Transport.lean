module

public import CFSG.RankThree.PartOne.FIVES.Core

public section

namespace CFSG.RankThree.PartOne.FIVES

theorem exists_invariant_two_subgroup_of_subgroups {G : Type} [Group G]
    [Finite G] {f : ℕ} (hf : 2 ≤ f) {J K K' A : Subgroup G} (hKJ : K ≤ J) (hK'J : K' ≤ J)
    (hJ : CentrallyUThree f ↥J) (hKs : IsSimpleGroup ↥K) (hKp : Group.IsPerfect ↥K)
    (hK'p : Group.IsPerfect ↥K') {z : G} (hzK : z ∈ K) (hz1 : z ≠ 1) (hz2 : z * z = 1)
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) (hAK : ∀ a ∈ A, ∀ k ∈ K, a * k * a⁻¹ = k)
    (hAK' : ∃ a ∈ A, ∃ y ∈ K', a * y * a⁻¹ ≠ y) :
    ∃ U : Subgroup G, U ≤ J ∧ IsPGroup 2 U ∧ A ≤ Subgroup.normalizer (U : Set G) ∧
      ∃ a ∈ A, ∃ u ∈ U, a * u * a⁻¹ ≠ u := by
  classical
  let Kj : Subgroup ↥J := K.subgroupOf J
  let Kj' : Subgroup ↥J := K'.subgroupOf J
  let eK : ↥Kj ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKJ
  let eK' : ↥Kj' ≃* ↥K' := Subgroup.subgroupOfEquivOfLe hK'J
  have hKjs : IsSimpleGroup ↥Kj := by
    have := hKs
    exact eK.isSimpleGroup
  have hKjp : Group.IsPerfect ↥Kj :=
    Group.IsPerfect.ofSurjective (f := eK.symm.toMonoidHom) eK.symm.surjective
  have hKjp' : Group.IsPerfect ↥Kj' :=
    Group.IsPerfect.ofSurjective (f := eK'.symm.toMonoidHom) eK'.symm.surjective
  have hnorm : ∀ a ∈ A, a ∈ Subgroup.normalizer (J : Set G) := fun a ha => hAJ ha
  let γ : ∀ a : G, a ∈ A → MulAut ↥J := fun a ha => J.normalizerMonoidHom ⟨a, hnorm a ha⟩
  have hγ : ∀ (a : G) (ha : a ∈ A) (x : ↥J), ((γ a ha x : ↥J) : G) = a * (x : G) * a⁻¹ :=
    fun a ha x => Subgroup.normalizerMonoidHom_apply_apply_coe J ⟨a, hnorm a ha⟩ x
  let Γ : Set (MulAut ↥J) := {g | ∃ (a : G) (ha : a ∈ A), g = γ a ha}
  have hzJ : z ∈ J := hKJ hzK
  obtain ⟨U, hU2, hUinv, g₀, ⟨a₀, ha₀, rfl⟩, u, huU, hmove⟩ := exists_invariant_two_subgroup hf hJ
    hKjs hKjp hKjp' (z := ⟨z, hzJ⟩) (Subgroup.mem_subgroupOf.mpr hzK)
    (fun h => hz1 (congrArg Subtype.val h)) (Subtype.ext hz2) Γ
    (by
      rintro _ ⟨a, ha, rfl⟩ k hk
      exact Subtype.ext ((hγ a ha k).trans (hAK a ha (k : G) (Subgroup.mem_subgroupOf.mp hk))))
    (by
      obtain ⟨a, ha, y, hy, hne⟩ := hAK'
      refine ⟨γ a ha, ⟨a, ha, rfl⟩, ⟨y, hK'J hy⟩, Subgroup.mem_subgroupOf.mpr hy, fun h => hne ?_⟩
      have := congrArg Subtype.val h
      rwa [hγ a ha] at this)
  have hcomp : ∀ (a : G) (ha : a ∈ A), (MulAut.conj a).toMonoidHom.comp J.subtype =
      J.subtype.comp (γ a ha).toMonoidHom := by
    intro a ha
    ext x
    exact (hγ a ha x).symm
  refine ⟨U.map J.subtype, Subgroup.map_subtype_le U, hU2.map _, ?_, a₀, ha₀, (u : G),
    Subgroup.mem_map.mpr ⟨u, huU, rfl⟩, fun h => hmove (Subtype.ext ?_)⟩
  · intro a ha
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    calc (U.map J.subtype).map (MulAut.conj a).toMonoidHom
        = U.map ((MulAut.conj a).toMonoidHom.comp J.subtype) := Subgroup.map_map _ _ _
      _ = U.map (J.subtype.comp (γ a ha).toMonoidHom) := by rw [hcomp a ha]
      _ = (U.map (γ a ha).toMonoidHom).map J.subtype := (Subgroup.map_map _ _ _).symm
      _ = U.map J.subtype := by rw [hUinv (γ a ha) ⟨a, ha, rfl⟩]
  · rw [hγ a₀ ha₀]
    exact h

end CFSG.RankThree.PartOne.FIVES
