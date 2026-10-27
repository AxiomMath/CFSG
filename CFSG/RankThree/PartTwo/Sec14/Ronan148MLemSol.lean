module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148M

theorem le_of_isPerfect_of_cover_solvable {G : Type*} [Group G] [Finite G] {K M R : Subgroup G}
    (hKM : K ≤ M) (hMN : M ≤ Subgroup.normalizer (K : Set G))
    (hcov : ∀ m ∈ M, ∃ k ∈ K, k⁻¹ * m ∈ R) (hR : Group.IsSolvable ↥R)
    (hM : Group.IsPerfect ↥M) : M ≤ K := by
  have hKn : (K.subgroupOf M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hKM]
    intro h k hh hk
    exact (Subgroup.mem_set_normalizer_iff.mp (hMN hk) h).mp hh
  have hRM : Group.IsSolvable ↥(R.subgroupOf M) := by
    let f : ↥(R.subgroupOf M) →* ↥R :=
      { toFun := fun x => ⟨(x.1 : G), Subgroup.mem_subgroupOf.mp x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hinj : Function.Injective f := by
      intro x y hxy
      have h3 : ((f x : ↥R) : G) = ((f y : ↥R) : G) := by rw [hxy]
      exact Subtype.ext (Subtype.ext h3)
    exact Group.isSolvable_of_isSolvable_injective hinj
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' (K.subgroupOf M)).comp (R.subgroupOf M).subtype) := by
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (K.subgroupOf M) q
    obtain ⟨k, hk, hr⟩ := hcov (m : G) m.2
    have hrM : k⁻¹ * (m : G) ∈ M := M.mul_mem (M.inv_mem (hKM hk)) m.2
    have hkK : QuotientGroup.mk' (K.subgroupOf M) (⟨k, hKM hk⟩ : ↥M) = 1 :=
      (QuotientGroup.eq_one_iff (⟨k, hKM hk⟩ : ↥M)).mpr (Subgroup.mem_subgroupOf.mpr hk)
    have hprod : m = (⟨k, hKM hk⟩ : ↥M) * (⟨k⁻¹ * (m : G), hrM⟩ : ↥M) :=
      Subtype.ext (mul_inv_cancel_left k (m : G)).symm
    refine ⟨⟨⟨k⁻¹ * (m : G), hrM⟩, Subgroup.mem_subgroupOf.mpr hr⟩, ?_⟩
    show QuotientGroup.mk' (K.subgroupOf M) (⟨k⁻¹ * (m : G), hrM⟩ : ↥M)
        = QuotientGroup.mk' (K.subgroupOf M) m
    conv_rhs => rw [hprod]
    rw [map_mul, hkK, one_mul]
  have hsolv : Group.IsSolvable (↥M ⧸ K.subgroupOf M) := Group.isSolvable_of_surjective hsurj
  have hsub : Subsingleton (↥M ⧸ K.subgroupOf M) := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isSolvable _ hsolv
  intro m hm
  have h1 : QuotientGroup.mk' (K.subgroupOf M) (⟨m, hm⟩ : ↥M) = 1 := Subsingleton.elim _ _
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (⟨m, hm⟩ : ↥M)).mp h1)

end CFSG.RankThree.PartTwo.Sec14.Ronan148M
