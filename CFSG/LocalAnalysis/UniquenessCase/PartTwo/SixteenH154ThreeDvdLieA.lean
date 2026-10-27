module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import CFSG.Open.StatedAPI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s16h_nontrivial_of_isQuasisimple {X : Type} [Group X]
    (hX : CFSG.Open.IsQuasisimple X) : Nontrivial X := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  haveI : Subsingleton X := h
  haveI : Subsingleton (X ⧸ Subgroup.center X) := inferInstance
  obtain ⟨a, b, hab⟩ := hX.2.exists_pair_ne
  exact hab (Subsingleton.elim a b)

theorem s16h_not_isMulCommutative_of_isQuasisimple {X : Type} [Group X]
    (hX : CFSG.Open.IsQuasisimple X) : ¬ IsMulCommutative X := by
  intro h
  haveI := h
  have hc : Subgroup.center X = ⊤ := Subgroup.center_eq_top
  haveI : Subsingleton (X ⧸ Subgroup.center X) := by
    rw [hc]
    exact QuotientGroup.subsingleton_quotient_top
  obtain ⟨a, b, hab⟩ := hX.2.exists_pair_ne
  exact hab (Subsingleton.elim a b)

theorem s16h_three_dvd_four_pow_sub_one (a : ℕ) : 3 ∣ 4 ^ a - 1 := by
  simpa using Nat.sub_dvd_pow_sub_pow 4 1 a

theorem s16h_three_dvd_two_pow_sq_sub_one {a : ℕ} : 3 ∣ (2 ^ a) ^ 2 - 1 := by
  have h : (2 ^ a) ^ 2 = 4 ^ a := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [h]
  exact s16h_three_dvd_four_pow_sub_one a

theorem s16h_three_dvd_prod_Icc {q n : ℕ} (hq : 3 ∣ q ^ 2 - 1) (hn : 2 ≤ n) :
    3 ∣ ∏ i ∈ Finset.Icc 2 n, (q ^ i - 1) := by
  refine dvd_trans hq (Finset.dvd_prod_of_mem _ ?_)
  rw [Finset.mem_Icc]
  exact ⟨le_rfl, hn⟩

theorem s16h_three_dvd_div_of_coprime {N g : ℕ} (hg : g ∣ N) (h3 : 3 ∣ N)
    (hcop : Nat.Coprime 3 g) : 3 ∣ N / g := by
  have hN : N = g * (N / g) := (Nat.mul_div_cancel' hg).symm
  have hmul : 3 ∣ g * (N / g) := by rw [← hN]; exact h3
  exact hcop.dvd_of_dvd_mul_left hmul

theorem s16h_three_dvd_div_of_mul_dvd {N g : ℕ} (hg0 : 0 < g) (hg : g ∣ N)
    (h : 3 * g ∣ N) : 3 ∣ N / g := by
  have hN : N = g * (N / g) := (Nat.mul_div_cancel' hg).symm
  have hmul : g * 3 ∣ g * (N / g) := by
    rw [hN] at h
    rwa [mul_comm 3 g] at h
  exact (Nat.mul_dvd_mul_iff_left hg0).mp hmul

theorem s16h_three_dvd_sq_add_self_add_one {q : ℕ} (hq : 1 ≤ q) (h : 3 ∣ q - 1) :
    3 ∣ q ^ 2 + q + 1 := by
  rw [← Int.natCast_dvd_natCast]
  have h3 : (3 : ℤ) ∣ (q : ℤ) - 1 := by
    obtain ⟨k, hk⟩ := h
    refine ⟨(k : ℤ), ?_⟩
    have hcast : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by
      rw [Nat.cast_sub hq, Nat.cast_one]
    rw [← hcast, hk]
    push_cast
    ring
  have hcast : ((q ^ 2 + q + 1 : ℕ) : ℤ) = (q : ℤ) ^ 2 + (q : ℤ) + 1 := by
    push_cast
    ring
  rw [hcast]
  have hEq : (q : ℤ) ^ 2 + (q : ℤ) + 1 = ((q : ℤ) - 1) * ((q : ℤ) + 2) + 3 := by ring
  rw [hEq]
  exact dvd_add (h3.mul_right _) (dvd_refl 3)

theorem s16h_three_dvd_sq_sub_self_add_one {q : ℕ} (hq : 1 ≤ q) (h : 3 ∣ q + 1) :
    3 ∣ q ^ 2 - q + 1 := by
  rw [← Int.natCast_dvd_natCast]
  have h3 : (3 : ℤ) ∣ (q : ℤ) + 1 := by exact_mod_cast h
  have hcast : ((q ^ 2 - q + 1 : ℕ) : ℤ) = (q : ℤ) ^ 2 - (q : ℤ) + 1 := by
    have h1 : q ≤ q ^ 2 := by nlinarith
    rw [Nat.cast_add, Nat.cast_sub h1]
    push_cast
    ring
  rw [hcast]
  have hEq : (q : ℤ) ^ 2 - (q : ℤ) + 1 = ((q : ℤ) + 1) * ((q : ℤ) - 2) + 3 := by ring
  rw [hEq]
  exact dvd_add (h3.mul_right _) (dvd_refl 3)

theorem s16h_add_one_dvd_sq_sub_one {q : ℕ} (hq : 1 ≤ q) : q + 1 ∣ q ^ 2 - 1 := by
  have h : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    apply Nat.cast_injective (R := ℤ)
    rw [Nat.cast_sub (by nlinarith : 1 ≤ q ^ 2), Nat.cast_mul, Nat.cast_sub hq]
    push_cast
    ring
  rw [h]
  exact ⟨q - 1, rfl⟩

theorem s16h_pow_three_add_one_factor (q : ℕ) :
    q ^ 3 + 1 = (q + 1) * (q ^ 2 - q + 1) := by
  apply Nat.cast_injective (R := ℤ)
  have h1 : q ≤ q ^ 2 := by nlinarith
  have hcast : ((q ^ 2 - q + 1 : ℕ) : ℤ) = (q : ℤ) ^ 2 - (q : ℤ) + 1 := by
    rw [Nat.cast_add, Nat.cast_sub h1]
    push_cast
    ring
  rw [Nat.cast_mul, hcast]
  push_cast
  ring

theorem s16h_pow_three_sub_one_factor {q : ℕ} (hq : 1 ≤ q) :
    q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
  apply Nat.cast_injective (R := ℤ)
  rw [Nat.cast_sub (Nat.one_le_pow 3 q (by omega)), Nat.cast_mul, Nat.cast_sub hq]
  push_cast
  ring

theorem s16h_three_mul_dvd_pow_add_one {q g : ℕ} (hq : 1 ≤ q) (hg : g ∣ q + 1)
    (h3 : 3 ∣ q + 1) : 3 * g ∣ q ^ 3 + 1 := by
  have h3q : 3 ∣ q ^ 2 - q + 1 := s16h_three_dvd_sq_sub_self_add_one hq h3
  have h1 : (q + 1) * 3 ∣ q ^ 3 + 1 := by
    rw [s16h_pow_three_add_one_factor q]
    exact mul_dvd_mul_left (q + 1) h3q
  rw [mul_comm (q + 1) 3] at h1
  exact dvd_trans (mul_dvd_mul_left 3 hg) h1

theorem s16h_three_mul_dvd_pow_sub_one {q g : ℕ} (hq : 1 ≤ q) (hg : g ∣ q - 1)
    (h3 : 3 ∣ q - 1) : 3 * g ∣ q ^ 3 - 1 := by
  have h3q : 3 ∣ q ^ 2 + q + 1 := s16h_three_dvd_sq_add_self_add_one hq h3
  have h1 : (q - 1) * 3 ∣ q ^ 3 - 1 := by
    rw [s16h_pow_three_sub_one_factor hq]
    exact mul_dvd_mul_left (q - 1) h3q
  rw [mul_comm (q - 1) 3] at h1
  exact dvd_trans (mul_dvd_mul_left 3 hg) h1

theorem s16h_subsingleton_statedSL_of_le_one {K : Type} [Field K] {n : ℕ} (hn : n ≤ 1) :
    Subsingleton ↥(StatedSL n K) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hn with rfl | rfl
  · haveI : Subsingleton (Matrix (Fin 0) (Fin 0) K) := inferInstance
    haveI : Subsingleton (GL (Fin 0) K) :=
      Subsingleton.units_of_isUnit fun a _ => Subsingleton.elim a 1
    infer_instance
  · have hle : StatedSL 1 K ≤ ⊥ := by
      refine (Subgroup.closure_le _).2 ?_
      intro A hA
      change A = 1
      refine Units.ext (Matrix.ext fun i j => ?_)
      fin_cases i
      fin_cases j
      have hdet : (A : Matrix (Fin 1) (Fin 1) K) 0 0 = 1 := by
        simpa [Matrix.det_fin_one] using hA
      simpa using hdet
    have hbot : StatedSL 1 K = ⊥ := le_antisymm hle bot_le
    rw [hbot]
    infer_instance

theorem s16h_subsingleton_statedSU_of_le_one {K : Type} [Field K] {n q : ℕ} (hn : n ≤ 1) :
    Subsingleton ↥(StatedSU n q K) := by
  haveI : Subsingleton ↥(StatedSL n K) := s16h_subsingleton_statedSL_of_le_one hn
  refine Subsingleton.intro fun a b => ?_
  have ha : (a : GL (Fin n) K) ∈ StatedSL n K := CFSG.Open.StatedAPI.statedSU_le_statedSL n q K a.2
  have hb : (b : GL (Fin n) K) ∈ StatedSL n K := CFSG.Open.StatedAPI.statedSU_le_statedSL n q K b.2
  have h : (⟨(a : GL (Fin n) K), ha⟩ : ↥(StatedSL n K)) = ⟨(b : GL (Fin n) K), hb⟩ :=
    Subsingleton.elim _ _
  have hval : (a : GL (Fin n) K) = (b : GL (Fin n) K) :=
    congrArg (fun z : ↥(StatedSL n K) => (z : GL (Fin n) K)) h
  exact Subtype.ext hval

theorem s16h_card_statedSp_zero (K : Type) [Field K] :
    Nat.card ↥(StatedSp 0 K) = 1 := by
  haveI : Subsingleton (Matrix (Fin 0 ⊕ Fin 0) (Fin 0 ⊕ Fin 0) K) := inferInstance
  haveI : Subsingleton (GL (Fin 0 ⊕ Fin 0) K) :=
    Subsingleton.units_of_isUnit fun a _ => Subsingleton.elim a 1
  haveI : Subsingleton ↥(StatedSp 0 K) := inferInstance
  exact Nat.card_of_subsingleton 1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

