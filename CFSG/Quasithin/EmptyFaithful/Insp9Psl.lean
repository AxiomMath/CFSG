module

public import CFSG.Quasithin.EmptyFaithful.Insp9Basic
public import CFSG.Quasithin.EmptyFaithful.Insp9Ord
public import CFSG.Quasithin.EmptyFaithful.Insp9Case
import CFSG.Adapters.StatedPSLTwo

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

namespace Insp9

variable {D : Type} [Group D] [Finite D] {D₁ D₂ J N : Subgroup D}

theorem Data.not_two_pow_dvd (h : Data D₁ D₂ J N) {k m : ℕ}
    (hT : Nat.card ↥(D₁ ⊓ D₂) = 2 ^ k) (hm : k < m) : ¬ 2 ^ m ∣ Nat.card D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT'⟩ := h.amalgam.toIsGoldschmidtTriple.sylow
  have h1 : Nat.card ↥T = 2 ^ (Nat.card D).factorization 2 := Sylow.card_eq_multiplicity T
  have h2 : Nat.card ↥T = Nat.card ↥(D₁ ⊓ D₂) := by rw [← hT']; rfl
  rw [hT] at h2
  have h3 : k = (Nat.card D).factorization 2 :=
    Nat.pow_right_injective le_rfl (h2.symm.trans h1)
  intro hdvd
  have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (Nat.card_pos (α := D)).ne').mp hdvd
  omega

theorem Data.N_ne_bot (h : Data D₁ D₂ J N) : N ≠ ⊥ := by
  intro hN
  apply h.J_ne_bot
  exact le_bot_iff.mp (hN ▸ h.J_le_N)

theorem Data.N_eq_top_of_simple (h : Data D₁ D₂ J N) (hs : IsSimpleGroup D) : N = ⊤ := by
  have := h.normal
  exact (hs.eq_bot_or_eq_top_of_normal N).resolve_left h.N_ne_bot

omit [Finite D] in
theorem isSimpleGroup_psl_two {Y : Type} [Group Y] {p f : ℕ}
    (hm : F6.IsL2 p f Y) : IsSimpleGroup Y :=
  CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel_psl_two hm

omit [Finite D] in
theorem two_mul_card_psl_two_pow {Y : Type} [Group Y] {p f : ℕ} (hp2 : p ≠ 2)
    (h : F6.IsL2 p f Y) : 2 * Nat.card Y = p ^ f * ((p ^ f) ^ 2 - 1) := by
  unfold F6.IsL2 at h
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL
    (by norm_num : 1 ≤ 2), hK]
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have h2 : 2 ∣ p ^ f - 1 := by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k, by omega⟩
  rw [Nat.gcd_eq_left h2]
  simp only [Finset.Icc_self, Finset.prod_singleton]
  have h3 : 2 ∣ (p ^ f) ^ (2 * (2 - 1) / 2) * ((p ^ f) ^ 2 - 1) := by
    have : 2 ∣ (p ^ f) ^ 2 - 1 := h2.trans (by simpa using Nat.sub_dvd_pow_sub_pow (p ^ f) 1 2)
    exact this.mul_left _
  rw [Nat.mul_div_cancel' h3]
  norm_num

omit [Group D] [Finite D] in
theorem arith_case4 {p n : ℕ} (hp : p.Prime) (hmod : p % 24 = 11 ∨ p % 24 = 13)
    (hcard : 2 * n = p * (p ^ 2 - 1)) : ¬ (n ∣ 12096 ∨ n ∈ omegaQL) := by
  have hp2 : p ≠ 2 := by omega
  rintro (hd | hm)
  · have h1 : p ∣ 2 * n := by rw [hcard]; exact Dvd.intro _ rfl
    have hpn : p ∣ n := ((Nat.Prime.dvd_mul hp).mp h1).resolve_left (fun h => by
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h
      omega)
    have h12096 : p ∣ 2 ^ 6 * (3 ^ 3 * 7) := by norm_num; exact hpn.trans hd
    rcases (Nat.Prime.dvd_mul hp).mp h12096 with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
      omega
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h)
        omega
      · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).mp h
        omega
  · have hmem : p * (p ^ 2 - 1) ∈ omegaQL.image (2 * ·) := Finset.mem_image.mpr ⟨n, hm, hcard⟩
    have hbound : ∀ x ∈ omegaQL.image (2 * ·), x ≤ 4194048 := by
      unfold omegaQL; decide +kernel
    have hle := hbound _ hmem
    have hp200 : p < 200 := by
      by_contra hcon
      have h1 : 200 ≤ p := by omega
      have h2 : 40000 ≤ p ^ 2 := by nlinarith
      have h3 : 39999 ≤ p ^ 2 - 1 := by omega
      have := Nat.mul_le_mul h1 h3
      omega
    have hdec : ∀ q ∈ Finset.range 200, (q % 24 = 11 ∨ q % 24 = 13) →
        q * (q ^ 2 - 1) ∉ omegaQL.image (2 * ·) := by
      unfold omegaQL; decide +kernel
    exact hdec p (Finset.mem_range.mpr hp200) hmod hmem

theorem case4_false (h : Data D₁ D₂ J N) (hs : B56Setting D N) {p : ℕ} (hp : p.Prime)
    (hmod : p % 24 = 11 ∨ p % 24 = 13) (hL2 : F6.IsL2 p 1 D)
    (hT : Nat.card ↥(D₁ ⊓ D₂) = 4) : False := by
  have hsimple := isSimpleGroup_psl_two hL2
  have hcard : 2 * Nat.card D = p * (p ^ 2 - 1) := by
    simpa using two_mul_card_psl_two_pow (by omega) hL2
  have hN := h.N_eq_top_of_simple hsimple
  have hnc : ∃ a b : D, a * b ≠ b * a := by
    by_contra hcomm
    push Not at hcomm
    have : IsMulCommutative D := ⟨⟨fun a b => hcomm a b⟩⟩
    have hq : (Nat.card D).Prime := hsimple.prime_card
    have h1 : p ∣ 2 * Nat.card D := by rw [hcard]; exact Dvd.intro _ rfl
    have h2 : p ∣ Nat.card D := ((Nat.Prime.dvd_mul hp).mp h1).resolve_left (fun h => by
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h
      omega)
    have h3 : p = Nat.card D := (Nat.prime_dvd_prime_iff_eq hp hq).mp h2
    rw [← h3] at hcard
    have h11 : 11 ≤ p := by
      have := hp.two_le
      omega
    have h4 : 121 ≤ p ^ 2 := by nlinarith
    have h5 : 120 ≤ p ^ 2 - 1 := by omega
    nlinarith
  have hqs := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1
  let e : ↥N ≃* D := (MulEquiv.subgroupCongr hN).trans Subgroup.topEquiv
  have hqsN : CFSG.IsQuasisimple ↥N := CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hqs
  have hql := hs.ql_of_quasisimple hqsN
  have h8 : ¬ 2 ^ 8 ∣ Nat.card ↥N := by
    rw [Nat.card_congr e.toEquiv]
    exact fun hd => h.not_two_pow_dvd (k := 2) (by simpa using hT) (m := 3) (by norm_num)
      ((Nat.pow_dvd_pow 2 (by norm_num : 3 ≤ 8)).trans hd)
  have hord := b56QL_card_le7 hql h8
  rw [Nat.card_congr e.toEquiv] at hord
  exact arith_case4 hp hmod hcard hord

end Insp9

end CFSG.Quasithin
