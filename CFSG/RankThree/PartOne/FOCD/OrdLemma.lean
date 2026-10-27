module

public import CFSG.RankThree.PartOne.FOC.Transfer
import CFSG.RankThree.PartOne.S12K.Rigidity
public import CFSG.Timmesfeld.Orders.Bang
import all CFSG.Timmesfeld.Orders.Distinct

public section

namespace CFSG.RankThree.PartOne.FOCD

open Subgroup CFSG CFSG.Blueprint CFSG.RankThree.PartOne CFSG.RankThree.PartOne.FOC
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

open CFSG.RankThree.PartOne.S12K (charTwoOrder card_of_lieModel_two)

open CFSG.Timmesfeld CFSG.Timmesfeld.Orders
open CFSG.Open

theorem isPrimitivePrimeDivisor_of_prime {p r : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hrp : r ∣ 2 ^ p - 1) : IsPrimitivePrimeDivisor r p := by
  refine ⟨hr, hrp, fun j hj hjp hrj => ?_⟩
  have hg : Nat.gcd j p = 1 := by
    rw [Nat.gcd_comm]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => by
      have := Nat.le_of_dvd hj h
      omega
  have h1 : r ∣ Nat.gcd (2 ^ j - 1) (2 ^ p - 1) := Nat.dvd_gcd hrj hrp
  rw [Nat.pow_sub_one_gcd_pow_sub_one, hg, pow_one] at h1
  exact hr.one_lt.ne' (Nat.dvd_one.1 h1)

theorem two_mul_add_one_le_of_prime_dvd {p r : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hr : r.Prime)
    (hrp : r ∣ 2 ^ p - 1) : 2 * p + 1 ≤ r := by
  have hr2 : r ≠ 2 := by
    rintro rfl
    have h1 : 2 ∣ 2 ^ p - 1 := hrp
    have h2 : 2 ∣ 2 ^ p := dvd_pow_self 2 hp.ne_zero
    have h3 : 1 ≤ 2 ^ p := Nat.one_le_two_pow
    omega
  have : Fact r.Prime := ⟨hr⟩
  have : Fact p.Prime := ⟨hp⟩
  have h2ne : (2 : ZMod r) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod r) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 this)
  have hpow : (2 : ZMod r) ^ p = 1 := by
    have h1 : ((2 ^ p - 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hrp
    rw [Nat.cast_sub Nat.one_le_two_pow] at h1
    push_cast at h1
    exact sub_eq_zero.1 h1
  have hord : orderOf (2 : ZMod r) = p := by
    refine orderOf_eq_prime hpow fun h1 => ?_
    have h3 : (1 : ZMod r) = 0 := by
      calc (1 : ZMod r) = 2 - 1 := by norm_num
        _ = 1 - 1 := by rw [h1]
        _ = 0 := by ring
    exact one_ne_zero h3
  have h1 : p ∣ r - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one h2ne
  have h2 : 2 ∣ r - 1 := by
    have := hr.eq_two_or_odd'
    rcases this with h | h
    · exact absurd h hr2
    · obtain ⟨k, hk⟩ := h
      exact ⟨k, by omega⟩
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (by omega)
  have h3 : 2 * p ∣ r - 1 := hcop.mul_dvd_of_dvd_of_dvd h2 h1
  have := Nat.le_of_dvd (by have := hr.two_le; omega) h3
  omega

@[expose] def primes71 : Finset ℕ :=
  {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71}

@[expose] def N71 : ℕ := ∏ r ∈ primes71, r ^ 100

theorem prime_le_71_of_dvd {q : ℕ} (hq : q.Prime) (h : q ∣ N71) : q ≤ 71 := by
  unfold N71 at h
  obtain ⟨r, hr, hqr⟩ := (Prime.dvd_finsetProd_iff hq.prime _).1 h
  have hr' : r.Prime := by
    unfold primes71 at hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  have : q = r := (Nat.prime_dvd_prime_iff_eq hq hr').1 (hq.dvd_of_dvd_pow hqr)
  subst this
  unfold primes71 at hr
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  omega

theorem exists_prime_dvd_two_pow_sub_one_not_dvd {N p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hN : N ∣ N71) : ∃ r, r.Prime ∧ r ∣ 2 ^ p - 1 ∧ ¬ r ∣ N := by
  have key : ∀ r : ℕ, r.Prime → 72 ≤ r → r ∣ 2 ^ p - 1 → ∃ r, r.Prime ∧ r ∣ 2 ^ p - 1 ∧
      ¬ r ∣ N := fun r hr h72 hrp =>
    ⟨r, hr, hrp, fun h => by have := prime_le_71_of_dvd hr (h.trans hN); omega⟩
  by_cases hp37 : 37 ≤ p
  · have hne : 2 ^ p - 1 ≠ 1 := by
      have : 2 ^ 37 ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp37
      omega
    have hr := Nat.minFac_prime hne
    have hrp : (2 ^ p - 1).minFac ∣ 2 ^ p - 1 := Nat.minFac_dvd _
    have := two_mul_add_one_le_of_prime_dvd hp (by omega) hr hrp
    exact key _ hr (by omega) hrp
  · have hcases : p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 ∨ p = 29 ∨ p = 31 := by
      interval_cases p <;> first | omega | (exfalso; norm_num at hp)
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact key 127 (by norm_num) (by norm_num) (by norm_num)
    · exact key 89 (by norm_num) (by norm_num) (by norm_num)
    · exact key 8191 (by norm_num) (by norm_num) (by norm_num)
    · exact key 131071 (by norm_num) (by norm_num) (by norm_num)
    · exact key 524287 (by norm_num) (by norm_num) (by norm_num)
    · exact key 178481 (by norm_num) (by norm_num) (by norm_num)
    · exact key 233 (by norm_num) (by norm_num) (by norm_num)
    · have hne : 2 ^ 31 - 1 ≠ 1 := by norm_num
      have hr := Nat.minFac_prime hne
      have hrp : (2 ^ 31 - 1).minFac ∣ 2 ^ 31 - 1 := Nat.minFac_dvd _
      generalize (2 ^ 31 - 1).minFac = r at hr hrp
      by_cases h72 : 72 ≤ r
      · exact key r hr h72 hrp
      · exfalso
        have hr71 : r ≤ 71 := by omega
        interval_cases r <;> first | omega | norm_num at hr

section Certs


theorem prime_dvd_card_lieModel_two {X : Type} [Group X] {t : StatedLieTag} {n m p r : ℕ}
    (hX : LieModel X t n 2 m) (hp : p.Prime) (hpm : p ∣ m) (hr : r.Prime) (hrp : r ∣ 2 ^ p - 1) :
    r ∣ Nat.card X := by
  have hprim := isPrimitivePrimeDivisor_of_prime hp hr hrp
  obtain ⟨hadm, hcard⟩ := card_of_lieModel_two hX
  rw [hcard]
  have hm : 1 ≤ m := hadm.2.1
  have hpm2 : p ∣ m * 2 := Dvd.dvd.mul_right hpm 2
  have hpf : p ∣ 2 * (m * 2) := Dvd.dvd.mul_left hpm2 2
  cases t
  case PSL =>
    obtain ⟨-, -, hn, -⟩ := hadm
    exact (profile_ordA (n := n - 1) (f := m) (by omega) hm |>.prim r p hprim hp.pos).2
      (by unfold zA; exact ⟨2, by simp; omega, hpm2⟩)
  case PSU =>
    obtain ⟨-, -, hn, -⟩ := hadm
    exact (profile_ordTwistedA (n := n - 1) (g := m) (by omega) hm |>.prim r p hprim hp.pos).2
      (by unfold zU; exact ⟨2, by simp; omega, Or.inl ⟨even_two, hpm2⟩⟩)
  case PSp =>
    obtain ⟨-, -, hn, -⟩ := hadm
    exact (profile_ordBC (n := n) hm |>.prim r p hprim hp.pos).2
      (by unfold zBC; exact ⟨1, by simp; omega, by simpa using hpm2⟩)
  case POmegaOdd => exact absurd rfl hadm.2.2.2
  case POmegaPlus =>
    obtain ⟨-, -, hn⟩ := hadm
    exact (profile_ordD (n := n) (by omega) hm |>.prim r p hprim hp.pos).2
      (by unfold zD; exact Or.inr ⟨1, by simp; omega, by simpa using hpm2⟩)
  case POmegaMinus =>
    obtain ⟨-, -, hn⟩ := hadm
    exact (profile_ordTwistedD (n := n) (by omega) hm |>.prim r p hprim hp.pos).2
      (by unfold z2D; exact Or.inr ⟨1, by simp; omega, by simpa using hpm2⟩)
  case G2 =>
    exact (profile_ordG2 (f := m) hm |>.prim r p hprim hp.pos).2
      (by unfold zG2 zList; exact ⟨2, by simp, hpm2⟩)
  case F4 =>
    exact (profile_ordF4 (f := m) hm |>.prim r p hprim hp.pos).2
      (by unfold zF4 zList; exact ⟨2, by simp, hpm2⟩)
  case E6 =>
    exact (profile_ordE6 (f := m) hm |>.prim r p hprim hp.pos).2
      (by unfold zE6 zList; exact ⟨2, by simp, hpm2⟩)
  case E7 =>
    exact (profile_ordE7 (f := m) hm |>.prim r p hprim hp.pos).2
      (by unfold zE7 zList; exact ⟨2, by simp, hpm2⟩)
  case E8 =>
    exact (profile_ordE8 (f := m) hm |>.prim r p hprim hp.pos).2
      (by unfold zE8 zList; exact ⟨2, by simp, hpm2⟩)
  case twistedE6 =>
    exact (profile_ordTwistedE6 (f := m) hm |>.prim r p hprim hp.pos).2
      (by unfold z2E6; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hpm2)))))
  case trialityD4 =>
    exact (profile_ordTrialityD4 (f := m) hm |>.prim r p hprim hp.pos).2
      (by unfold zD4; exact Or.inr (Or.inr hpm2))
  case twistedB2 =>
    exact (profile_ordSuzuki (f := m) hm |>.prim r p hprim hp.pos).2
      (by unfold zSz; exact Or.inr hpm)
  case twistedG2 =>
    obtain ⟨-, -, -, hp3, -⟩ := hadm
    omega
  case twistedF4 =>
    exact (profile_ordTwistedF4 (f := m) hm |>.prim r p hprim hp.pos).2
      (by unfold z2F4; exact Or.inr (Or.inr (Or.inr hpm)))
  case Tits =>
    obtain ⟨-, -, -, -, hm1⟩ := hadm
    exact absurd (Nat.le_of_dvd one_pos (hm1 ▸ hpm)) (by have := hp.two_le; omega)

theorem fieldInnerT_of_prime_not_dvd {T : Type} [Group T] [Finite T] {p : ℕ} (hp : p.Prime)
    {r : ℕ} (hr : r.Prime) (hrp : r ∣ 2 ^ p - 1) (hrT : ¬ r ∣ Nat.card T) : FieldInnerT p T := by
  intro _ x β E _ _ _ _ _ _ _ ⟨t, n, f, _, hLie⟩
  have h1 : r ∣ Nat.card (↥E ⧸ Subgroup.center ↥E) :=
    prime_dvd_card_lieModel_two hLie hp (dvd_mul_right p f) hr hrp
  have h2 : Nat.card (↥E ⧸ Subgroup.center ↥E) ∣ Nat.card E := by
    rw [← Subgroup.index_eq_card]
    exact Subgroup.index_dvd_card _
  exact hrT (h1.trans (h2.trans (Subgroup.card_subgroup_dvd_card E)))

theorem fieldInnerT_of_dvd_N71 {T : Type} [Group T] [Finite T] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hT : Nat.card T ∣ N71) (h5 : p = 5 → ¬ 31 ∣ Nat.card T) : FieldInnerT p T := by
  rcases Nat.lt_or_ge p 7 with h | h
  · have hp5' : p = 5 := by
      interval_cases p <;> first | rfl | (exfalso; norm_num at hp)
    exact fieldInnerT_of_prime_not_dvd hp (r := 31) (by norm_num) (by rw [hp5']; norm_num)
      (h5 hp5')
  · obtain ⟨r, hr, hrp, hrT⟩ := exists_prime_dvd_two_pow_sub_one_not_dvd hp h hT
    exact fieldInnerT_of_prime_not_dvd hp hr hrp (fun hd => hrT hd)

end Certs

end CFSG.RankThree.PartOne.FOCD
