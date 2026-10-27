module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.Quasithin

namespace Q16

theorem centralizer_eq_top_of_perfect {K : Type*} [Group K] [Finite K] (N : Subgroup K)
    [N.Normal] (hN : IsPGroup 2 N) (hs : IsSimpleGroup (K ⧸ N)) (hperf : commutator K = ⊤)
    {x : K} (hxN : x ∉ N) (hxc : x ∈ Subgroup.centralizer (N : Set K)) :
    Subgroup.centralizer (N : Set K) = ⊤ := by
  set C : Subgroup K := Subgroup.centralizer (N : Set K) with hC
  have hCn : C.Normal := inferInstance
  have hmap : C.map (QuotientGroup.mk' N) = ⊤ := by
    have : (C.map (QuotientGroup.mk' N)).Normal :=
      Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective N)
    rcases hs.eq_bot_or_eq_top_of_normal (C.map (QuotientGroup.mk' N)) with h | h
    · exfalso
      have hx1 : (QuotientGroup.mk' N) x ∈ C.map (QuotientGroup.mk' N) :=
        Subgroup.mem_map_of_mem _ hxc
      rw [h, Subgroup.mem_bot] at hx1
      exact hxN ((QuotientGroup.eq_one_iff x).mp hx1)
    · exact h
  have hdec : ∀ k : K, ∃ c ∈ C, ∃ n ∈ N, k = c * n := by
    intro k
    have hk : (QuotientGroup.mk' N) k ∈ C.map (QuotientGroup.mk' N) := by
      rw [hmap]
      trivial
    obtain ⟨c, hc, hck⟩ := Subgroup.mem_map.mp hk
    refine ⟨c, hc, c⁻¹ * k, ?_, by group⟩
    have : (QuotientGroup.mk' N) (c⁻¹ * k) = 1 := by
      rw [map_mul, map_inv, hck, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).mp this
  have hpg : IsPGroup 2 (K ⧸ C) := by
    intro g
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨c, hc, n, hn, rfl⟩ := hdec k
    obtain ⟨m, hm⟩ := hN ⟨n, hn⟩
    refine ⟨m, ?_⟩
    have hcmk : (QuotientGroup.mk c : K ⧸ C) = 1 := (QuotientGroup.eq_one_iff c).mpr hc
    have hnm : n ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have h1 : (QuotientGroup.mk (c * n) : K ⧸ C) = QuotientGroup.mk n := by
      rw [QuotientGroup.mk_mul, hcmk, one_mul]
    rw [h1, ← QuotientGroup.mk_pow, hnm, QuotientGroup.mk_one]
  have hperfQ : commutator (K ⧸ C) = ⊤ := by
    have hsurj := QuotientGroup.mk'_surjective C
    have h1 : ⁅(⊤ : Subgroup (K ⧸ C)), (⊤ : Subgroup (K ⧸ C))⁆ =
        Subgroup.map (QuotientGroup.mk' C) ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ := by
      rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ hsurj]
    rw [commutator_def, h1, ← commutator_def, hperf, Subgroup.map_top_of_surjective _ hsurj]
  have hperfect : Group.IsPerfect (K ⧸ C) := Group.isPerfect_def.mpr hperfQ
  have hnil : Group.IsNilpotent (K ⧸ C) := hpg.isNilpotent
  by_cases hsub : Subsingleton (K ⧸ C)
  · ext k
    simp only [Subgroup.mem_top, iff_true]
    exact (QuotientGroup.eq_one_iff k).mp (Subsingleton.elim _ _)
  · have : Nontrivial (K ⧸ C) := not_subsingleton_iff_nontrivial.mp hsub
    exact absurd hnil (Group.IsPerfect.not_isNilpotent (K ⧸ C))

end Q16

end CFSG.Quasithin
