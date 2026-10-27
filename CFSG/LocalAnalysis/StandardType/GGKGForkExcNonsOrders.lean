module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcFrame
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSylowCyclic

public section

namespace CFSG.StandardType

namespace ExcNons

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE

private theorem ggKGNo_pow_sub_one_ne_zero {q d : ℕ} (hq : 1 < q) (hd : d ≠ 0) :
    q ^ d - 1 ≠ 0 := by
  have h : 1 < q ^ d := one_lt_pow₀ hq hd
  omega

private theorem ggKGNo_prod_map_ne_zero {l : List ℕ} {f : ℕ → ℕ}
    (h : ∀ d ∈ l, f d ≠ 0) : (l.map f).prod ≠ 0 := by
  apply List.prod_ne_zero
  intro h0
  rw [List.mem_map] at h0
  obtain ⟨d, hd, hfd⟩ := h0
  exact h d hd hfd

private theorem ggKGNo_lte_even {p q d : ℕ} (hp : p.Prime) (hq : 1 < q)
    (hpq : p ∣ q + 1) (hpodd : Odd p) (hp_not_dvd_q : ¬ p ∣ q)
    (hp_not_dvd_qm1 : ¬ p ∣ q - 1) (hd : Even d) (hd0 : d ≠ 0) :
    padicValNat p (q ^ d - 1) = padicValNat p (q + 1) + padicValNat p (d / 2) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq2 : 1 < q ^ 2 := one_lt_pow₀ hq (by norm_num)
  have hsq : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    zify [hq.le, hq2.le]
    ring
  have hpq2 : p ∣ q ^ 2 - 1 := by
    rw [hsq]; exact dvd_mul_of_dvd_right hpq (q - 1)
  have hpnq2 : ¬ p ∣ q ^ 2 := fun h => hp_not_dvd_q (hp.dvd_of_dvd_pow h)
  have hd2 : d / 2 ≠ 0 := by
    rcases hd with ⟨k, hk⟩
    omega
  have h := padicValNat.pow_sub_pow (p := p) (x := q ^ 2) (y := 1) hpodd hq2 hpq2 hpnq2 hd2
  rw [one_pow] at h
  have hpow : (q ^ 2) ^ (d / 2) = q ^ d := by
    rw [← pow_mul]
    congr 1
    rcases hd with ⟨k, hk⟩
    omega
  rw [hpow] at h
  rw [hsq, padicValNat.mul (by omega) (by omega),
    padicValNat.eq_zero_of_not_dvd hp_not_dvd_qm1, zero_add] at h
  exact h

private theorem ggKGNo_val_even_degrees {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hq : 1 < q) (hpq : p ∣ q + 1) (l : List ℕ)
    (hl : ∀ d ∈ l, d ≠ 0 ∧ Even d) :
    padicValNat p (l.map (fun d => q ^ d - 1)).prod =
      l.length * padicValNat p (q + 1) +
        padicValNat p ((l.map (fun d => d / 2)).prod) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact Nat.odd_iff.mpr h
  have hp_not_dvd_q : ¬ p ∣ q := by
    intro hd
    have h1 : p ∣ (q + 1) - q := Nat.dvd_sub hpq hd
    have h2 : (q + 1) - q = 1 := by omega
    rw [h2] at h1
    exact hp.not_dvd_one h1
  have hp_not_dvd_qm1 : ¬ p ∣ q - 1 := by
    intro hd
    have h1 : p ∣ (q + 1) - (q - 1) := Nat.dvd_sub hpq hd
    have h2 : (q + 1) - (q - 1) = 2 := by omega
    rw [h2] at h1
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h1
    omega
  revert hl
  induction l with
  | nil =>
    intro hl
    simp
  | cons a t ih =>
    intro hl
    have ha : a ≠ 0 ∧ Even a := hl a (by simp)
    have ht : ∀ d ∈ t, d ≠ 0 ∧ Even d := fun d hd => hl d (by simp [hd])
    have hih := ih ht
    have hfa : q ^ a - 1 ≠ 0 := ggKGNo_pow_sub_one_ne_zero hq ha.1
    have hft : (t.map (fun d => q ^ d - 1)).prod ≠ 0 :=
      ggKGNo_prod_map_ne_zero fun d hd => ggKGNo_pow_sub_one_ne_zero hq (ht d hd).1
    have hga : a / 2 ≠ 0 := by
      rcases ha.2 with ⟨k, hk⟩
      omega
    have hgt : (t.map (fun d => d / 2)).prod ≠ 0 :=
      ggKGNo_prod_map_ne_zero fun d hd => by
        have hd0 := (ht d hd).1
        rcases (ht d hd).2 with ⟨k, hk⟩
        omega
    rw [List.map_cons, List.prod_cons, padicValNat.mul hfa hft]
    rw [ggKGNo_lte_even hp hq hpq hpodd hp_not_dvd_q hp_not_dvd_qm1 ha.2 ha.1, hih]
    rw [List.length_cons, List.map_cons, List.prod_cons, padicValNat.mul hga hgt]
    ring

private theorem ggKGNo_padicValNat_2903040 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    padicValNat p 2903040 = padicValNat p 22680 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hfac : 2903040 = 2 ^ 7 * 22680 := by norm_num
  rw [hfac, padicValNat.mul (by norm_num) (by norm_num)]
  have h2 : ¬ p ∣ 2 ^ 7 := by
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd)
    omega
  rw [padicValNat.eq_zero_of_not_dvd h2, zero_add]

private theorem ggKGNo_padicValNat_696729600 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    padicValNat p 696729600 = padicValNat p 2721600 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hfac : 696729600 = 2 ^ 8 * 2721600 := by norm_num
  rw [hfac, padicValNat.mul (by norm_num) (by norm_num)]
  have h2 : ¬ p ∣ 2 ^ 8 := by
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd)
    omega
  rw [padicValNat.eq_zero_of_not_dvd h2, zero_add]

private theorem ggKGNo_E7_val {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : 1 < q)
    (hpq : p ∣ q + 1) :
    padicValNat p (q ^ 63 * (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) *
        (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1)) =
      7 * padicValNat p (q + 1) + padicValNat p 2903040 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp_not_dvd_q : ¬ p ∣ q := by
    intro hd
    have h1 : p ∣ (q + 1) - q := Nat.dvd_sub hpq hd
    have h2 : (q + 1) - q = 1 := by omega
    rw [h2] at h1
    exact hp.not_dvd_one h1
  have heq : q ^ 63 * (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) *
        (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1) =
      q ^ 63 * (([18, 14, 12, 10, 8, 6, 2] : List ℕ).map (fun d => q ^ d - 1)).prod := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    ring
  have hFne : (([18, 14, 12, 10, 8, 6, 2] : List ℕ).map (fun d => q ^ d - 1)).prod ≠ 0 := by
    apply ggKGNo_prod_map_ne_zero
    intro d hd
    have hd0 : d ≠ 0 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
    exact ggKGNo_pow_sub_one_ne_zero hq hd0
  have hlist := ggKGNo_val_even_degrees hp hp5 hq hpq [18, 14, 12, 10, 8, 6, 2] (by decide)
  rw [heq, padicValNat.mul (pow_ne_zero 63 (by omega)) hFne, padicValNat.pow,
    padicValNat.eq_zero_of_not_dvd hp_not_dvd_q, Nat.mul_zero, zero_add, hlist]
  have hlen : ([18, 14, 12, 10, 8, 6, 2] : List ℕ).length = 7 := by decide
  have hhalf : (([18, 14, 12, 10, 8, 6, 2] : List ℕ).map (fun d => d / 2)).prod = 22680 := by
    decide
  rw [hlen, hhalf, ggKGNo_padicValNat_2903040 hp hp5]

private theorem ggKGNo_E8_val {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : 1 < q)
    (hpq : p ∣ q + 1) :
    padicValNat p (q ^ 120 * (q ^ 30 - 1) * (q ^ 24 - 1) * (q ^ 20 - 1) * (q ^ 18 - 1) *
        (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 2 - 1)) =
      8 * padicValNat p (q + 1) + padicValNat p 696729600 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp_not_dvd_q : ¬ p ∣ q := by
    intro hd
    have h1 : p ∣ (q + 1) - q := Nat.dvd_sub hpq hd
    have h2 : (q + 1) - q = 1 := by omega
    rw [h2] at h1
    exact hp.not_dvd_one h1
  have heq : q ^ 120 * (q ^ 30 - 1) * (q ^ 24 - 1) * (q ^ 20 - 1) * (q ^ 18 - 1) *
        (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 2 - 1) =
      q ^ 120 * (([30, 24, 20, 18, 14, 12, 8, 2] : List ℕ).map (fun d => q ^ d - 1)).prod := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    ring
  have hFne :
      (([30, 24, 20, 18, 14, 12, 8, 2] : List ℕ).map (fun d => q ^ d - 1)).prod ≠ 0 := by
    apply ggKGNo_prod_map_ne_zero
    intro d hd
    have hd0 : d ≠ 0 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
    exact ggKGNo_pow_sub_one_ne_zero hq hd0
  have hlist := ggKGNo_val_even_degrees hp hp5 hq hpq [30, 24, 20, 18, 14, 12, 8, 2] (by decide)
  rw [heq, padicValNat.mul (pow_ne_zero 120 (by omega)) hFne, padicValNat.pow,
    padicValNat.eq_zero_of_not_dvd hp_not_dvd_q, Nat.mul_zero, zero_add, hlist]
  have hlen : ([30, 24, 20, 18, 14, 12, 8, 2] : List ℕ).length = 8 := by decide
  have hhalf : (([30, 24, 20, 18, 14, 12, 8, 2] : List ℕ).map (fun d => d / 2)).prod = 2721600 := by
    decide
  rw [hlen, hhalf, ggKGNo_padicValNat_696729600 hp hp5]

theorem padicValNat_card_adjointGroup_E7_nons
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K + 1) :
    padicValNat p (Nat.card (adjointGroup .E7 K)) =
      7 * padicValNat p (Nat.card K + 1) + padicValNat p 2903040 := by
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hq2 : 1 < Nat.card K := Finite.one_lt_card
  have hodd : Nat.gcd 2 (Nat.card K - 1) = 1 := by
    have : Fintype K := Fintype.ofFinite K
    have h0 : ((Fintype.card K : ℕ) : K) = 0 := FiniteField.cast_card_eq_zero K
    have h2 : 2 ∣ Nat.card K := by
      rw [Nat.card_eq_fintype_card]
      exact (CharP.cast_eq_zero_iff K 2 _).1 h0
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    have h3 : ¬ 2 ∣ Nat.card K - 1 := by omega
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h3
  have hH : Nat.card (torusGroup .E7 K) = (Nat.card K - 1) ^ 7 := by
    have h := CFSG.Timmesfeld.ExceptionalOrders.card_torusGroup_E7 (K := K)
    rwa [Nat.gcd_comm, hodd, mul_one] at h
  have hCeq : Nat.card (adjointGroup .E7 K) =
      Nat.card K ^ 63 * (Nat.card K ^ 18 - 1) * (Nat.card K ^ 14 - 1) * (Nat.card K ^ 12 - 1) *
        (Nat.card K ^ 10 - 1) * (Nat.card K ^ 8 - 1) * (Nat.card K ^ 6 - 1) *
        (Nat.card K ^ 2 - 1) := by
    have hord := CFSG.Timmesfeld.ExceptionalOrders.ordE7_mul (Nat.card K) hq1
    rw [TableBExc.card_adjointGroup_E7_eq, hH, TableBExc.prodE7]
    conv_rhs => rw [← hord]
    ring
  rw [hCeq]
  exact ggKGNo_E7_val hp hp5 hq2 hpq

theorem padicValNat_card_adjointGroup_E8_nons
    {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K + 1) :
    padicValNat p (Nat.card (adjointGroup .E8 K)) =
      8 * padicValNat p (Nat.card K + 1) + padicValNat p 696729600 := by
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hq2 : 1 < Nat.card K := Finite.one_lt_card
  have hH : Nat.card (torusGroup .E8 K) = (Nat.card K - 1) ^ 8 :=
    CFSG.Timmesfeld.ExceptionalOrders.card_torusGroup_E8 (K := K)
  have hCeq : Nat.card (adjointGroup .E8 K) =
      Nat.card K ^ 120 * (Nat.card K ^ 30 - 1) * (Nat.card K ^ 24 - 1) *
        (Nat.card K ^ 20 - 1) * (Nat.card K ^ 18 - 1) * (Nat.card K ^ 14 - 1) *
        (Nat.card K ^ 12 - 1) * (Nat.card K ^ 8 - 1) * (Nat.card K ^ 2 - 1) := by
    have hord := CFSG.Timmesfeld.ExceptionalOrders.ordE8_eq (Nat.card K) hq1
    rw [CFSG.Open.ordE8] at hord
    rw [TableBExc.card_adjointGroup_E8_eq, hH, TableBExc.prodE8]
    conv_rhs => rw [← hord]
    ring
  rw [hCeq]
  exact ggKGNo_E8_val hp hp5 hq2 hpq

end ExcNons

end CFSG.StandardType

end
