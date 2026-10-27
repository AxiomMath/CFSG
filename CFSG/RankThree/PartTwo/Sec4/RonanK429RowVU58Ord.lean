module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVTools
import CFSG.RankThree.PartTwo.Sec13.Item13Models

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU)

namespace RowV

theorem prime_pow_eq_eight {p e : ℕ} (hp : p.Prime) (h : p ^ e = 8) : p = 2 ∧ e = 3 := by
  have he : e ≠ 0 := by
    rintro rfl
    simp at h
  have hp2 : p = 2 := by
    have hdvd : p ∣ 2 ^ 3 := by
      rw [show (2 : ℕ) ^ 3 = 8 from rfl, ← h]
      exact dvd_pow_self p he
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd)
  subst hp2
  exact ⟨rfl, Nat.pow_right_injective le_rfl (h.trans (by norm_num))⟩

theorem isType429_u38_of_dvd {X : Type} [Group X] [Finite X] [Group.IsPerfect X] {N B : ℕ}
    (hN : 0 < N) (hd : Nat.card X ∣ N) (hB : 3 * N < B ^ 3 * ((B ^ 2 - 1) * (B ^ 3 - 1)))
    (hL : ∀ q < B, q % 3 = 1 → ¬ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) ∣ 3 * N)
    (hU : ∀ q < B, q % 3 = 2 → q ≠ 2 → q ≠ 8 → ¬ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) ∣ 3 * N)
    (h7 : ¬ 2520 ∣ N) (h12 : ¬ 95040 ∣ N) (h22 : ¬ 443520 ∣ N) (hJ : ¬ 604800 ∣ N)
    (hX : IsType429 X) : Nonempty (X ≃* projSU 3 2 3) := by
  rcases hX with ⟨p, e, hp, he, h⟩ | h | h | h | h
  · have hpp : p.Prime := Fact.out
    have h3d : 3 * Nat.card X ∣ 3 * N := Nat.mul_dvd_mul_left 3 hd
    have hq1 : 1 ≤ p ^ e := Nat.one_le_pow _ _ hpp.pos
    rcases h with ⟨h1, ⟨φ⟩⟩ | ⟨h2, ⟨φ⟩⟩
    · exfalso
      have hc := KS14.card_projSL_three_mul_gcd (GaloisField p e)
      rw [GaloisField.card p e (by omega), ← Nat.card_congr φ.toEquiv] at hc
      have hg : Nat.gcd 3 (p ^ e - 1) = 3 := Nat.gcd_eq_left (by omega)
      rw [hg, mul_comm] at hc
      rw [hc] at h3d
      exact hL _ (lt_of_dvd_ordL (by omega) hB h3d) h1 h3d
    · by_cases hq8 : p ^ e = 8
      · obtain ⟨rfl, rfl⟩ := prime_pow_eq_eight hpp hq8
        exact ⟨φ⟩
      · exfalso
        have hc := KS14.card_projSU_three_mul_gcd p e he
        rw [← Nat.card_congr φ.toEquiv] at hc
        have hg : Nat.gcd 3 (p ^ e + 1) = 3 := Nat.gcd_eq_left (by omega)
        rw [hg, mul_comm] at hc
        by_cases hq2 : p ^ e = 2
        · rw [hq2] at hc
          have hcard : Nat.card X = 72 := by omega
          have : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
          obtain ⟨rfl, rfl⟩ := (Nat.prime_two.pow_eq_iff).mp hq2
          have hs := Sec13.isSolvable_projSU_two
          have hsolv : IsSolvable X :=
            solvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective
          exact Group.IsPerfect.not_isSolvable X hsolv
        · rw [hc] at h3d
          exact hU _ (lt_of_dvd_ordU (by omega) hB h3d) h2 hq2 hq8 h3d
  · obtain ⟨φ⟩ := h
    exfalso
    apply h7
    rw [← KS14.card_alternatingGroup_five_seven_ten.2.1, ← Nat.card_congr φ.toEquiv]
    exact hd
  · obtain ⟨φ⟩ := h
    exfalso
    apply h12
    rw [← KS14.card_nativeM12, ← Nat.card_congr φ.toEquiv]
    exact hd
  · obtain ⟨φ⟩ := h
    exfalso
    apply h22
    rw [← KS14.card_nativeM22, ← Nat.card_congr φ.toEquiv]
    exact hd
  · obtain ⟨φ⟩ := h
    exfalso
    apply hJ
    rw [← KS14.card_nativeJ2, ← Nat.card_congr φ.toEquiv]
    exact hd

theorem isType429_m12_of_dvd {X : Type} [Group X] [Finite X] [Group.IsPerfect X] {N B : ℕ}
    (hN : 0 < N) (hd : Nat.card X ∣ N) (hB : 3 * N < B ^ 3 * ((B ^ 2 - 1) * (B ^ 3 - 1)))
    (hL : ∀ q < B, q % 3 = 1 → ¬ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) ∣ 3 * N)
    (hU : ∀ q < B, q % 3 = 2 → q ≠ 2 → ¬ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) ∣ 3 * N)
    (h7 : ¬ 2520 ∣ N) (h22 : ¬ 443520 ∣ N) (hJ : ¬ 604800 ∣ N)
    (hX : IsType429 X) : Nonempty (X ≃* Blueprint.NativeSporadic.M12) := by
  rcases hX with ⟨p, e, hp, he, h⟩ | h | h | h | h
  · exact absurd h (not_isoLThreePi_of_dvd hN hd hB hL hU he)
  · obtain ⟨φ⟩ := h
    exfalso
    apply h7
    rw [← KS14.card_alternatingGroup_five_seven_ten.2.1, ← Nat.card_congr φ.toEquiv]
    exact hd
  · exact h
  · obtain ⟨φ⟩ := h
    exfalso
    apply h22
    rw [← KS14.card_nativeM22, ← Nat.card_congr φ.toEquiv]
    exact hd
  · obtain ⟨φ⟩ := h
    exfalso
    apply hJ
    rw [← KS14.card_nativeJ2, ← Nat.card_congr φ.toEquiv]
    exact hd

theorem not_isType429_of_dvd_of_dvd {X : Type} [Group X] [Finite X] [Group.IsPerfect X]
    {N B M : ℕ} (hN : 0 < N) (hd : Nat.card X ∣ N) (hM : M ∣ Nat.card X)
    (hB : 3 * N < B ^ 3 * ((B ^ 2 - 1) * (B ^ 3 - 1)))
    (hL : ∀ q < B, q % 3 = 1 → q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) ∣ 3 * N →
      ¬ 3 * M ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)))
    (hU : ∀ q < B, q % 3 = 2 → q ≠ 2 → q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) ∣ 3 * N →
      ¬ 3 * M ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)))
    (h7 : ¬ M ∣ 2520) (h12 : ¬ M ∣ 95040) (h22 : ¬ M ∣ 443520) (hJ : ¬ M ∣ 604800) :
    ¬ IsType429 X := by
  have h3M : 3 * M ∣ 3 * Nat.card X := Nat.mul_dvd_mul_left 3 hM
  rintro (⟨p, e, hp, he, h⟩ | h | h | h | h)
  · have hpp : p.Prime := Fact.out
    have h3d : 3 * Nat.card X ∣ 3 * N := Nat.mul_dvd_mul_left 3 hd
    have hq1 : 1 ≤ p ^ e := Nat.one_le_pow _ _ hpp.pos
    rcases h with ⟨h1, ⟨φ⟩⟩ | ⟨h2, ⟨φ⟩⟩
    · have hc := KS14.card_projSL_three_mul_gcd (GaloisField p e)
      rw [GaloisField.card p e (by omega), ← Nat.card_congr φ.toEquiv] at hc
      have hg : Nat.gcd 3 (p ^ e - 1) = 3 := Nat.gcd_eq_left (by omega)
      rw [hg, mul_comm] at hc
      rw [hc] at h3d h3M
      exact hL _ (lt_of_dvd_ordL (by omega) hB h3d) h1 h3d h3M
    · have hc := KS14.card_projSU_three_mul_gcd p e he
      rw [← Nat.card_congr φ.toEquiv] at hc
      have hg : Nat.gcd 3 (p ^ e + 1) = 3 := Nat.gcd_eq_left (by omega)
      rw [hg, mul_comm] at hc
      by_cases hq2 : p ^ e = 2
      · rw [hq2] at hc
        have hcard : Nat.card X = 72 := by omega
        have : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
        obtain ⟨rfl, rfl⟩ := (Nat.prime_two.pow_eq_iff).mp hq2
        have hs := Sec13.isSolvable_projSU_two
        have hsolv : IsSolvable X :=
          solvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective
        exact Group.IsPerfect.not_isSolvable X hsolv
      · rw [hc] at h3d h3M
        exact hU _ (lt_of_dvd_ordU (by omega) hB h3d) h2 hq2 h3d h3M
  · obtain ⟨φ⟩ := h
    apply h7
    rw [← KS14.card_alternatingGroup_five_seven_ten.2.1, ← Nat.card_congr φ.toEquiv]
    exact hM
  · obtain ⟨φ⟩ := h
    apply h12
    rw [← KS14.card_nativeM12, ← Nat.card_congr φ.toEquiv]
    exact hM
  · obtain ⟨φ⟩ := h
    apply h22
    rw [← KS14.card_nativeM22, ← Nat.card_congr φ.toEquiv]
    exact hM
  · obtain ⟨φ⟩ := h
    apply hJ
    rw [← KS14.card_nativeJ2, ← Nat.card_congr φ.toEquiv]
    exact hM

theorem exists_orderOf_ten_M12 : ∃ x : Blueprint.NativeSporadic.M12, orderOf x = 10 := by
  set a : Equiv.Perm (Fin 12) := List.formPerm [0, 3] * List.formPerm [2, 9] *
    List.formPerm [4, 10] * List.formPerm [5, 11] with ha
  set b : Equiv.Perm (Fin 12) := List.formPerm [0, 7, 8] * List.formPerm [1, 2, 3] *
    List.formPerm [4, 11, 10] * List.formPerm [5, 9, 6] with hb
  have hamem : a ∈ Blueprint.NativeSporadic.M12 := Subgroup.subset_closure (by simp [ha])
  have hbmem : b ∈ Blueprint.NativeSporadic.M12 := Subgroup.subset_closure (by simp [hb])
  have hbi : b⁻¹ ∈ Blueprint.NativeSporadic.M12 := Subgroup.inv_mem _ hbmem
  set w := a * b * a * b * a * b * a * b⁻¹ * a * b⁻¹ with hw
  have hwmem : w ∈ Blueprint.NativeSporadic.M12 := by
    have h : ∀ {x y : Equiv.Perm (Fin 12)}, x ∈ Blueprint.NativeSporadic.M12 →
        y ∈ Blueprint.NativeSporadic.M12 → x * y ∈ Blueprint.NativeSporadic.M12 :=
      fun hx hy => Subgroup.mul_mem _ hx hy
    exact h (h (h (h (h (h (h (h (h hamem hbmem) hamem) hbmem) hamem) hbmem) hamem) hbi) hamem) hbi
  refine ⟨⟨w, hwmem⟩, ?_⟩
  rw [Subgroup.orderOf_mk, orderOf_eq_iff (by norm_num)]
  refine ⟨by decide +kernel, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide +kernel

end RowV

end CFSG.RankThree.PartTwo.Sec4.RonanK429
