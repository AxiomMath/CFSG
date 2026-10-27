module

public import CFSG.Quasithin.Vol2.Asc94.TS40c

public section

namespace CFSG.Quasithin.A94

open CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] [Finite G] {z : G}

theorem Frame4.card_Gz (F : Frame4 G z) (hU1 : ∀ u ∈ F.U, u ≠ 1 → InZG z u)
    (hU2 : ∀ u ∈ F.U2, u ≠ 1 → InZG z u) : F.Gz.ncard = 9 := by
  classical
  have hsum := F.sum_Gz hU1 hU2
  by_cases h4 : F.Γ 4 ⊆ F.Gz <;> by_cases h5 : F.Γ 5 ⊆ F.Gz
  · exfalso
    simp only [h4, h5, if_true] at hsum
    haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
    refine F.not_prime_dvd_card_normalizer_J 13 (by norm_num) hcong16_13 ?_
    rw [F.card_normalizer_J, hsum]
    exact Dvd.dvd.mul_right (by norm_num : 13 ∣ 13) _
  · simp only [h4, h5, if_true, if_false] at hsum
    omega
  · simp only [h4, h5, if_true, if_false] at hsum
    omega
  · exfalso
    simp only [h4, h5, if_false] at hsum
    exact F.false_of_card_Gz_5 (by omega) h4 h5

theorem Frame4.exists_Δ12 (F : Frame4 G z) (hU1 : ∀ u ∈ F.U, u ≠ 1 → InZG z u)
    (hU2 : ∀ u ∈ F.U2, u ≠ 1 → InZG z u) :
    ∃ j : Fin 7, 4 ≤ j.val ∧ F.Δ j ⊆ F.Sz ∧ (F.Δ j).ncard = 12 := by
  classical
  have h9 := F.card_Gz hU1 hU2
  have hsum := F.sum_Gz hU1 hU2
  have hk : ∃ k : Fin 6, 4 ≤ k.val ∧ F.Γ k ⊆ F.Gz := by
    by_cases h4 : F.Γ 4 ⊆ F.Gz
    · exact ⟨4, by decide, h4⟩
    · by_cases h5 : F.Γ 5 ⊆ F.Gz
      · exact ⟨5, by decide, h5⟩
      · exfalso
        simp only [h4, h5, if_false] at hsum
        omega
  obtain ⟨k, hk4, hkS⟩ := hk
  obtain ⟨b, hb⟩ := F.Γ_nonempty k
  have hbGz := hkS hb
  have hbB : b ∈ F.A ⊓ F.A' := hbGz.1
  have hb1 : b ≠ 1 := hbGz.2.1
  have hbA : b ∈ F.A := (Subgroup.mem_inf.1 hbB).1
  have hbA' : b ∈ F.A' := (Subgroup.mem_inf.1 hbB).2
  have hbΔ : b ∈ ⋃ i, F.Δ i := by
    rw [F.Δ_union]
    exact ⟨hbA, hb1⟩
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hbΔ
  have hbQ_false : b ∉ F.Q := by
    intro hbQ
    have hsq : b * b = 1 := by
      rw [← sq]
      exact F.A_elem.2 b hbA
    have : ∃ i : Fin 6, i.val ≤ 3 ∧ b ∈ F.Γ i := by
      rcases F.Q_inv b hbQ hsq hb1 with h | ⟨h, hne⟩ | ⟨h, hne⟩ | h
      · exact ⟨0, by decide, by rw [F.Γ0]; exact h⟩
      · refine ⟨1, by decide, ?_⟩
        rw [F.Γ1]
        exact ⟨Subgroup.mem_inf.2 ⟨hbB, h⟩, by simp [hb1, hne]⟩
      · refine ⟨2, by decide, ?_⟩
        rw [F.Γ2]
        exact ⟨Subgroup.mem_inf.2 ⟨hbB, h⟩, by simp [hb1, hne]⟩
      · refine ⟨3, by decide, ?_⟩
        obtain ⟨hnU, hnU2, hnQ⟩ := F.TQ_not_U b h
        rw [F.Γ3]
        exact ⟨hbA, hbA', hnQ, hb1, hnU, hnU2⟩
    obtain ⟨i, hi3, hbi⟩ := this
    have hne : i ≠ k := by
      intro h
      subst h
      omega
    exact Set.disjoint_left.1 (F.Γ_disj i k hne) hbi hb
  have hj4 : 4 ≤ j.val := by
    by_contra hlt
    push Not at hlt
    exact hbQ_false (F.Δ_Q j (by omega) b hj)
  have hbSz : b ∈ F.Sz := ⟨hbA, hb1, hbGz.2.2⟩
  have hjS : F.Δ j ⊆ F.Sz := by
    rcases F.dich j with h | h
    · exact h
    · exact absurd hbSz (Set.disjoint_left.1 h hj)
  refine ⟨j, hj4, hjS, ?_⟩
  obtain ⟨k', hk', hk'21⟩ := F.toFrame2.card_NA
  have horbΔ : {x : G | ∃ l ∈ F.NA, x = l⁻¹ * b * l} = F.Δ j := by
    ext x
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact F.Δ_inv j b hj l hl
    · intro hx
      obtain ⟨l, hl, hxl⟩ := F.Δ_trans j b hj x hx
      exact ⟨l, hl, hxl⟩
  have horbΓ : {x : G | ∃ l ∈ F.T, x = l⁻¹ * b * l} = F.Γ k := by
    ext x
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact F.Γ_inv k b hb l hl
    · intro hx
      obtain ⟨l, hl, hxl⟩ := F.Γ_trans k b hb x hx
      exact ⟨l, hl, hxl⟩
  have c1 := card_orbit_eq_ncard F.NA b (F.Δ j) horbΔ
  have c2 := card_orbit_eq_ncard F.T b (F.Γ k) horbΓ
  have hΓk : (F.Γ k).ncard = 4 := by
    rw [F.Γ_card k]
    fin_cases k <;> simp at hk4 ⊢
  rw [hΓk, F.card_T] at c2
  have hT256 : Nat.card ↥(F.T ⊓ Subgroup.centralizer ({b} : Set G)) = 256 := by omega
  obtain ⟨s, hs⟩ : 256 ∣ Nat.card ↥(F.NA ⊓ Subgroup.centralizer ({b} : Set G)) := by
    rw [← hT256]
    exact Subgroup.card_dvd_of_le (inf_le_inf_right _ F.T_le_NA)
  rw [hs, hk'] at c1
  have hΔj : (F.Δ j).ncard = 12 ∨ (F.Δ j).ncard = 24 := by
    rw [F.Δ_card j]
    revert hj4
    fin_cases j <;> simp
  rcases hΔj with h | h
  · exact h
  · exfalso
    rw [h] at c1
    have hk3 : k' ∈ Nat.divisors 21 := Nat.mem_divisors.2 ⟨hk'21, by norm_num⟩
    have hdiv21 : Nat.divisors 21 = {1, 3, 7, 21} := by decide
    rw [hdiv21] at hk3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk3
    omega

theorem s40_1 (F : Frame4 G z) (hU1 : ∀ u ∈ F.U, u ≠ 1 → InZG z u)
    (hU2 : ∀ u ∈ F.U2, u ≠ 1 → InZG z u) :
    F.Gz.ncard = 9 ∧ Nat.card ↥(Subgroup.normalizer (F.J : Set G)) = 9 * 1024 ∧
      ∃ j : Fin 7, 4 ≤ j.val ∧ F.Δ j ⊆ F.Sz ∧ (F.Δ j).ncard = 12 :=
  ⟨F.card_Gz hU1 hU2, by rw [F.card_normalizer_J, F.card_Gz hU1 hU2], F.exists_Δ12 hU1 hU2⟩

end CFSG.Quasithin.A94
