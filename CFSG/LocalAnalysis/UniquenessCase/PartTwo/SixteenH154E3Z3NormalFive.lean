module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Data.Finite.Perm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

variable {D : Type*} [Group D] [Finite D]

theorem s16h_e3_sylow_eq_bot_of_closure_involutions {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hgen : closure {x : D | orderOf x = 2} = ⊤) (P : Sylow p D)
    (hP : normalizer (P : Set D) ≤ centralizer (P : Set D)) :
    (P : Subgroup D) = ⊥ := by
  have hker : (MonoidHom.transferSylow P hP).ker = ⊤ := by
    rw [eq_top_iff, ← hgen, closure_le]
    intro x hx
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    have h2 : orderOf (MonoidHom.transferSylow P hP x) ∣ 2 := by
      have := orderOf_map_dvd (MonoidHom.transferSylow P hP) x
      rwa [show orderOf x = 2 from hx] at this
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp P.isPGroup') (MonoidHom.transferSylow P hP x)
    rw [hk] at h2
    rcases k with _ | k
    · simpa using hk
    · exfalso
      have hpd : p ∣ 2 := (dvd_pow_self p (Nat.succ_ne_zero k)).trans h2
      exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp hpd)
  have hc := (MonoidHom.ker_transferSylow_isComplement' P hP).card_mul
  rw [hker, Subgroup.card_top] at hc
  have h1 : Nat.card (P : Subgroup D) = 1 := by
    have hpos : 0 < Nat.card D := Nat.card_pos
    nlinarith
  exact Subgroup.card_eq_one.mp h1

theorem s16h_e3_not_dvd_card_of_closure_involutions {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hgen : closure {x : D | orderOf x = 2} = ⊤)
    (hP : ∀ P : Sylow p D, normalizer (P : Set D) ≤ centralizer (P : Set D)) :
    ¬ p ∣ Nat.card D := fun hd =>
  (default : Sylow p D).ne_bot_of_dvd_card hd
    (s16h_e3_sylow_eq_bot_of_closure_involutions hp2 hgen default (hP default))

theorem s16h_e3_exists_normal_card_five [Nontrivial D]
    (hgen : closure {x : D | orderOf x = 2} = ⊤)
    (hO2 : ∀ N : Subgroup D, N.Normal → IsPGroup 2 N → N = ⊥)
    (hcard : Nat.card D ∣ 2 ^ 6 * 3 ^ 3 * 5 * 7)
    (h3 : ∀ P : Sylow 3 D, normalizer (P : Set D) ≤ centralizer (P : Set D))
    (h7 : ∀ P : Sylow 7 D, normalizer (P : Set D) ≤ centralizer (P : Set D)) :
    ∃ F : Subgroup D, F.Normal ∧ Nat.card F = 5 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set n := Nat.card D with hn
  have hn3 : ¬ 3 ∣ n := s16h_e3_not_dvd_card_of_closure_involutions (by norm_num) hgen h3
  have hn7 : ¬ 7 ∣ n := s16h_e3_not_dvd_card_of_closure_involutions (by norm_num) hgen h7
  have h320 : n ∣ 320 := by
    have hc3 : n.Coprime 3 := Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd
      Nat.prime_three).mpr hn3)
    have hc7 : n.Coprime 7 := Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd
      (by norm_num)).mpr hn7)
    have hc : n.Coprime 189 := by
      have := Nat.Coprime.mul_right (Nat.Coprime.pow_right 3 hc3) hc7
      norm_num at this
      exact this
    exact hc.dvd_of_dvd_mul_right (by norm_num at hcard ⊢; exact hcard)
  have h2grp_of_dvd : ∀ H : Subgroup D, Nat.card H ∣ 64 → IsPGroup 2 H := by
    intro H hH
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (show Nat.card H ∣ 2 ^ 6 from hH)
    exact IsPGroup.of_card hi
  have h5 : 5 ∣ n := by
    by_contra h5
    have hc5 : n.Coprime 5 := Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd
      (by norm_num)).mpr h5)
    have h64 : n ∣ 64 := hc5.dvd_of_dvd_mul_right (by simpa using h320)
    have := hO2 ⊤ inferInstance (h2grp_of_dvd ⊤ (by rwa [Subgroup.card_top]))
    exact bot_ne_top this.symm
  have h2 : 2 ∣ n := by
    by_contra h2
    have hsub : {x : D | orderOf x = 2} ⊆ (⊥ : Subgroup D) := by
      intro x hx
      exact absurd ((show orderOf x = 2 from hx) ▸ orderOf_dvd_natCard x) h2
    have : (⊤ : Subgroup D) = ⊥ := by rw [← hgen]; exact le_bot_iff.mp ((closure_le _).mpr hsub)
    exact bot_ne_top this.symm
  obtain S : Sylow 2 D := default
  have hn2 : Nat.card (Sylow 2 D) = 5 := by
    have hidx : (S : Subgroup D).index ∣ 5 := by
      have hd : (S : Subgroup D).index ∣ 320 := (Subgroup.index_dvd_card _).trans h320
      have hco : (S : Subgroup D).index.Coprime 2 := Nat.coprime_comm.mp
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr S.not_dvd_index)
      exact (Nat.Coprime.pow_right 6 hco).dvd_of_dvd_mul_left (by simpa using hd)
    have hdv := (S.card_dvd_index).trans hidx
    rcases (Nat.dvd_prime (by norm_num)).mp hdv with h1 | h5'
    · exfalso
      haveI : Subsingleton (Sylow 2 D) := (Nat.card_eq_one_iff_unique.mp h1).1
      exact S.ne_bot_of_dvd_card h2 (hO2 S S.normal_of_subsingleton S.isPGroup')
    · exact h5'
  have hN : IsPGroup 2 (normalizer (S : Set D)) := by
    apply h2grp_of_dvd
    have hmul := (normalizer (S : Set D)).card_mul_index
    rw [← S.card_eq_index_normalizer, hn2] at hmul
    have : Nat.card (normalizer (S : Set D)) * 5 ∣ 64 * 5 := by rw [hmul]; simpa using h320
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) this
  have h120 : n ∣ 120 := by
    let φ := MulAction.toPermHom D (Sylow 2 D)
    have hker : φ.ker = ⊥ := by
      apply hO2 _ φ.normal_ker
      apply hN.to_le
      intro x hx
      have hx' : x • S = S := by
        have := congrArg (fun σ : Equiv.Perm (Sylow 2 D) => σ S) (MonoidHom.mem_ker.mp hx)
        simpa [φ] using this
      exact (Sylow.smul_eq_iff_mem_normalizer).mp hx'
    have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hker
    have := Subgroup.card_dvd_of_injective φ hinj
    rwa [Nat.card_perm, hn2] at this
  have h40 : n ∣ 40 := by
    have := Nat.dvd_gcd h120 h320
    norm_num at this
    exact this
  obtain P : Sylow 5 D := default
  have hn5 : Nat.card (Sylow 5 D) = 1 := by
    have hd : Nat.card (Sylow 5 D) ∣ 40 :=
      ((P.card_dvd_index).trans (Subgroup.index_dvd_card _)).trans h40
    have hm : Nat.card (Sylow 5 D) % 5 = 1 := card_sylow_modEq_one 5 D
    generalize Nat.card (Sylow 5 D) = m at hd hm ⊢
    have hle : m ≤ 40 := Nat.le_of_dvd (by norm_num) hd
    clear * - hd hm hle
    interval_cases m <;> omega
  haveI : Subsingleton (Sylow 5 D) := (Nat.card_eq_one_iff_unique.mp hn5).1
  refine ⟨P, P.normal_of_subsingleton, ?_⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
  have hd : 5 ^ k ∣ 40 := hk ▸ (Subgroup.card_subgroup_dvd_card _).trans h40
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact P.ne_bot_of_dvd_card h5 (Subgroup.card_eq_one.mp (by simpa using hk))
  have hk1 : k ≤ 1 := by
    by_contra hk1
    have := (pow_dvd_pow 5 (show 2 ≤ k by omega)).trans hd
    norm_num at this
  rw [hk, show k = 1 by omega, pow_one]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
