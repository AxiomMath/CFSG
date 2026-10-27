module

public import CFSG.RankThree.PartTwo.Sec21.FF84S3B

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

variable {G : Type} [Group G] [Finite G]

theorem B_coprime_index_four {X : Subgroup G} (hX : IsPGroup 2 X) {a : G} (ha : orderOf a = 3)
    (hn : a ∈ Nor X) (hnc : ¬ X ≤ Cen a) : 4 ≤ (X ⊓ Cen a).relIndex X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := X ⊓ Cen a with hCdef
  have hdvd : C.relIndex X ∣ Nat.card X := Dvd.intro _ (Subgroup.relIndex_mul_card C X)
  obtain ⟨n, hn'⟩ := hX.exists_card_eq
  rw [hn'] at hdvd
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hne1 : C.relIndex X ≠ 1 := by
    intro h1
    apply hnc
    intro x hx
    exact (Subgroup.mem_inf.1 (Subgroup.relIndex_eq_one.1 h1 hx)).2
  have hbad : C.relIndex X ≠ 2 := by
    intro h2
    have hidx : (C.subgroupOf X).index = 2 := h2
    haveI hnorm : (C.subgroupOf X).Normal := Subgroup.normal_of_index_eq_two hidx
    have hcard : Nat.card (↥X ⧸ C.subgroupOf X) = 2 := hidx
    obtain ⟨x, y, hxy, hset⟩ := Nat.card_eq_two_iff.1 hcard
    have hall : ∀ z : ↥X ⧸ C.subgroupOf X, z = x ∨ z = y := by
      intro z
      have hz : z ∈ ({x, y} : Set (↥X ⧸ C.subgroupOf X)) := by
        rw [hset]
        exact Set.mem_univ z
      simpa using hz
    have hcos : ∀ u ∈ X, ∀ v ∈ X, u ∉ C → v ∉ C → u⁻¹ * v ∈ C := by
      intro u hu v hv huC hvC
      have hu1 : (QuotientGroup.mk (⟨u, hu⟩ : ↥X) : ↥X ⧸ C.subgroupOf X) ≠ 1 := by
        intro h
        rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
        exact huC h
      have hv1 : (QuotientGroup.mk (⟨v, hv⟩ : ↥X) : ↥X ⧸ C.subgroupOf X) ≠ 1 := by
        intro h
        rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
        exact hvC h
      have key : (QuotientGroup.mk (⟨u, hu⟩ : ↥X) : ↥X ⧸ C.subgroupOf X) =
          QuotientGroup.mk (⟨v, hv⟩ : ↥X) := by
        rcases hall (QuotientGroup.mk (⟨u, hu⟩ : ↥X)) with h1 | h1 <;>
          rcases hall (QuotientGroup.mk (⟨v, hv⟩ : ↥X)) with h2 | h2 <;>
          rcases hall (1 : ↥X ⧸ C.subgroupOf X) with h3 | h3 <;>
          first
          | exact h1.trans h2.symm
          | exact absurd (h1.trans h3.symm) hu1
          | exact absurd (h2.trans h3.symm) hv1
      have := QuotientGroup.eq.1 key
      rw [Subgroup.mem_subgroupOf] at this
      exact this
    have h1 : ∀ u ∈ X, ∃ m ∈ C, a * u * a⁻¹ = u * m := by
      intro u hu
      by_cases huC : u ∈ C
      · have hua : u * a = a * u := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 huC).2
        refine ⟨1, C.one_mem, ?_⟩
        rw [mul_one, ← hua, mul_inv_cancel_right]
      · have hv : a * u * a⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 hn u).1 hu
        have hvC : a * u * a⁻¹ ∉ C := by
          intro hvC
          have hcv : (a * u * a⁻¹) * a = a * (a * u * a⁻¹) :=
            Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hvC).2
          apply huC
          have hue : u = a * u * a⁻¹ := by
            calc u = a⁻¹ * (a * u * a⁻¹) * a := by group
              _ = a⁻¹ * ((a * u * a⁻¹) * a) := by group
              _ = a⁻¹ * (a * (a * u * a⁻¹)) := by rw [hcv]
              _ = a * u * a⁻¹ := by group
          rw [hue]
          exact hvC
        exact ⟨u⁻¹ * (a * u * a⁻¹), hcos u hu _ hv huC hvC,
          (mul_inv_cancel_left u _).symm⟩
    have h2' : ∀ m ∈ C, a * m * a⁻¹ = m := by
      intro m hm
      have hma : m * a = a * m := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hm).2
      rw [← hma, mul_inv_cancel_right]
    have hstab := S3.B_stability 2 X C a hX inf_le_left hnorm hn
      (by rw [ha]; norm_num) h1 h2'
    apply hnc
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hstab x hx)
  rcases i with _ | _ | i
  · exact absurd (hi.trans (by norm_num)) hne1
  · exact absurd (hi.trans (by norm_num)) hbad
  · rw [hi]
    exact le_trans (by norm_num : (4 : ℕ) ≤ 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) (by omega))

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
