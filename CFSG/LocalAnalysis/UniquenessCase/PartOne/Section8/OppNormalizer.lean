module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ConjSetCard
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {M L : Subgroup G}

theorem mem_normalizer_of_ncard_conjSetOf_le_two_of_odd_order
    (h2 : (conjSetOf M L).ncard ≤ 2) {x : G} (hxM : x ∈ M) (hodd : Odd (orderOf x)) :
    x ∈ normalizer (L : Set G) := by
  classical
  by_contra hxN
  have hLmem : L ∈ conjSetOf M L := mem_conjSetOf_self M L
  have hxmem : L.map (MulAut.conj x).toMonoidHom ∈ conjSetOf M L := ⟨x, hxM, rfl⟩
  have hx2mem : L.map (MulAut.conj (x ^ 2)).toMonoidHom ∈ conjSetOf M L :=
    ⟨x ^ 2, M.pow_mem hxM 2, rfl⟩
  have hne : L.map (MulAut.conj x).toMonoidHom ≠ L := by
    intro h
    exact hxN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
  have hx2N : x ^ 2 ∈ normalizer (L : Set G) := by
    by_contra hx2N
    have hne2 : L.map (MulAut.conj (x ^ 2)).toMonoidHom ≠ L := by
      intro h
      exact hx2N (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
    have hne12 : L.map (MulAut.conj (x ^ 2)).toMonoidHom ≠
        L.map (MulAut.conj x).toMonoidHom := by
      intro h
      have h' := congrArg (fun K : Subgroup G => K.map (MulAut.conj x⁻¹).toMonoidHom) h
      rw [uc22p22d_map_conj_map_conj, uc22p22d_map_conj_map_conj] at h'
      have hxx : x⁻¹ * x = 1 := by group
      have hx2x : x⁻¹ * x ^ 2 = x := by group
      rw [hxx, hx2x] at h'
      have h1 : L.map (MulAut.conj (1 : G)).toMonoidHom = L := by
        rw [show MulAut.conj (1 : G) = 1 by ext y; simp [MulAut.conj_apply]]
        change L.map (MonoidHom.id G) = L
        exact Subgroup.map_id L
      rw [h1] at h'
      exact hne h'
    have hthree : ({L, L.map (MulAut.conj x).toMonoidHom,
        L.map (MulAut.conj (x ^ 2)).toMonoidHom} : Set (Subgroup G)).ncard = 3 := by
      rw [Set.ncard_eq_three]
      refine ⟨L, L.map (MulAut.conj (x ^ 2)).toMonoidHom,
        L.map (MulAut.conj x).toMonoidHom, hne2.symm, hne.symm, hne12, ?_⟩
      ext K
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    have hsub : ({L, L.map (MulAut.conj x).toMonoidHom,
        L.map (MulAut.conj (x ^ 2)).toMonoidHom} : Set (Subgroup G)) ⊆ conjSetOf M L := by
      intro K hK
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hK
      rcases hK with rfl | rfl | rfl
      · exact hLmem
      · exact hxmem
      · exact hx2mem
    have hle := Set.ncard_le_ncard hsub
    omega
  have hxeq : x = (x ^ 2) ^ ((orderOf x + 1) / 2) := by
    rw [← pow_mul]
    have h2k : 2 * ((orderOf x + 1) / 2) = orderOf x + 1 := by
      have ho : orderOf x % 2 = 1 := Nat.odd_iff.mp hodd
      omega
    rw [h2k, pow_succ, pow_orderOf_eq_one, one_mul]
  exact hxN (by
    rw [hxeq]
    exact Subgroup.pow_mem _ hx2N _)

theorem opp_le_normalizer_of_ncard_conjSetOf_le_two {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (h2 : (conjSetOf M L).ncard ≤ 2) :
    Opp p M ≤ normalizer (L : Set G) := by
  have hpodd : Odd p := Nat.Prime.odd_of_ne_two Fact.out hp2
  refine (Subgroup.closure_le (normalizer (L : Set G))).mpr ?_
  rintro x ⟨hxM, k, hxk⟩
  exact mem_normalizer_of_ncard_conjSetOf_le_two_of_odd_order h2 hxM
    (by rw [hxk]; exact hpodd.pow)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
