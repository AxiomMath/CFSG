module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusPlane

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted

theorem omq_omMinus_wt_torus_long {n : ℕ} {K : Type} [Field K] [Finite K] {b c : K}
    {k : Type*} [Field k] {m h : ℕ} (hm : m = Nat.card Kˣ) (ι : K →+* k)
    (ι' : ShortField b c →+* k) (ν : OmqMinusLat (n - 1) m h) {i : Fin (n - 1)}
    (hi : i.val + 1 < n - 1) (a : Kˣ) :
    omqMinusWt n ι ι' ν ((minusFrame n b c).longTorus (succ_ne_of_lt n hi) true false a) =
      ι (a : K) ^ (ν.1 i - ν.1 ⟨i.val + 1, hi⟩).val := by
  classical
  haveI : NeZero m := ⟨by rw [hm]; exact Nat.card_pos.ne'⟩
  have ht := omq_omMinus_toral_longTorus (b := b) (c := c) hi a
  rw [omq_omMinus_wt_eq_of_toral ι ι' ν ht]
  set j : Fin (n - 1) := ⟨i.val + 1, hi⟩ with hj
  have hji : j ≠ i := (succ_ne_of_lt n hi).symm
  have hij : i ≠ j := succ_ne_of_lt n hi
  have hprod : ∏ l : Fin (n - 1), ι ((if l = i then a else if l = j then a⁻¹ else 1 : Kˣ) : K) ^
      (ν.1 l).val = ι (a : K) ^ (ν.1 i).val * ι ((a⁻¹ : Kˣ) : K) ^ (ν.1 j).val := by
    rw [← Finset.prod_subset (Finset.subset_univ {i, j}), Finset.prod_pair hij]
    · simp [hij, hji]
    · intro l _ hl
      have h1 : l ≠ i := fun h => hl (by simp [h])
      have h2 : l ≠ j := fun h => hl (by simp [h])
      simp [h1, h2]
  rw [hprod]
  simp only [map_one, one_pow, mul_one, ZMod.val_zero, pow_zero]
  have hu : ι (a : K) ^ m = 1 := by
    rw [hm, ← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one', Units.val_one, map_one]
  have hne : ι (a : K) ≠ 0 := fun h0 => a.ne_zero (ι.injective (h0.trans (map_zero ι).symm))
  have hinv : ι ((a⁻¹ : Kˣ) : K) = (ι (a : K))⁻¹ := by
    rw [Units.val_inv_eq_inv_val, map_inv₀]
  rw [hinv, inv_pow]
  have hmod : ι (a : K) ^ ((ν.1 i - ν.1 j).val + (ν.1 j).val) = ι (a : K) ^ (ν.1 i).val := by
    rw [pow_eq_pow_mod (a := ι (a : K)) (n := m) _ hu, pow_eq_pow_mod (a := ι (a : K)) (n := m)
      (ν.1 i).val hu]
    congr 1
    have : (((ν.1 i - ν.1 j).val + (ν.1 j).val : ℕ) : ZMod m) = (((ν.1 i).val : ℕ) : ZMod m) := by
      rw [Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
        sub_add_cancel]
    exact (ZMod.natCast_eq_natCast_iff' _ _ m).mp this
  rw [pow_add] at hmod
  rw [← hmod]
  field_simp

theorem omq_omMinus_wt_torus_short {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k : Type*} [Field k] {m h : ℕ} (ι : K →+* k)
    (ι' : ShortField b c →+* k) (hι' : ∀ x : K, ι' (algebraMap K (ShortField b c) x) = ι x)
    (ν : OmqMinusLat (n - 1) m h) (i : Fin (n - 1)) (u : (ShortField b c)ˣ) :
    omqMinusWt n ι ι' ν (shortTorusHom n hirr i u) =
      ι' (u : ShortField b c) ^ (((Nat.card K : ℤ) + 1) * ((ν.1 i).val : ℤ) +
        (1 - (Nat.card K : ℤ)) * (ν.2.val : ℤ)) := by
  classical
  haveI := fact_shortField hirr
  have ht := omq_omMinus_toral_shortTorusHom hirr i u
  rw [omq_omMinus_wt_eq_of_toral ι ι' ν ht]
  have hprod : ∏ l : Fin (n - 1), ι ((if l = i then Units.map QuadraticAlgebra.norm u else 1 : Kˣ)
      : K) ^ (ν.1 l).val = ι (QuadraticAlgebra.norm (u : ShortField b c)) ^ (ν.1 i).val := by
    rw [Finset.prod_eq_single i]
    · simp
    · intro l _ hl
      simp [hl]
    · simp
  rw [hprod]
  have hne : ι' (u : ShortField b c) ≠ 0 := fun h0 =>
    u.ne_zero (ι'.injective (h0.trans (map_zero ι').symm))
  have h1 : ι (QuadraticAlgebra.norm (u : ShortField b c)) =
      ι' (u : ShortField b c) ^ (Nat.card K + 1) := by
    rw [← hι', ← omq_shortField_pow_card_succ hirr, map_pow]
  have hs : star (u : ShortField b c) = (u : ShortField b c) ^ Nat.card K := by
    have e := QuadraticAlgebra.algebraMap_norm_eq_mul_star (u : ShortField b c)
    rw [← omq_shortField_pow_card_succ hirr, pow_succ'] at e
    exact (mul_left_cancel₀ u.ne_zero e).symm
  have h2 : ι' ((u : ShortField b c) / star (u : ShortField b c)) =
      ι' (u : ShortField b c) ^ (1 - (Nat.card K : ℤ)) := by
    rw [hs, map_div₀, map_pow, zpow_sub₀ hne, zpow_one, zpow_natCast]
  rw [h1, h2, ← zpow_natCast (ι' (u : ShortField b c) ^ (Nat.card K + 1)),
    ← zpow_natCast (ι' (u : ShortField b c) ^ (1 - (Nat.card K : ℤ))), ← zpow_natCast,
    ← zpow_mul, ← zpow_mul, ← zpow_add₀ hne]
  congr 1

theorem omq_omMinus_card_shortField_units {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card (ShortField b c)ˣ = Nat.card Kˣ * (Nat.card K + 1) := by
  haveI := fact_shortField hirr
  haveI := finite_shortField (b := b) (c := c)
  rw [Nat.card_units, Nat.card_units]
  have hF : Nat.card (ShortField b c) = Nat.card K ^ 2 := by
    rw [Nat.card_congr (QuadraticAlgebra.equivProd (-c) b), Nat.card_prod, sq]
  rw [hF]
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  obtain ⟨q, hq'⟩ : ∃ q, Nat.card K = q + 1 := ⟨Nat.card K - 1, by omega⟩
  rw [hq']
  simp only [Nat.add_sub_cancel]
  ring_nf
  omega

theorem omq_omMinus_exists_short_exponent {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k : Type*} [Field k] {m h : ℕ}
    (hm : m = Nat.card Kˣ) (hh : h = Nat.card K + 1) (ι : K →+* k) (ι' : ShortField b c →+* k)
    (hι' : ∀ x : K, ι' (algebraMap K (ShortField b c) x) = ι x) (a : ZMod m) (d : ZMod h) :
    ∃ C : ℕ, 1 ≤ C ∧ C ≤ m * h ∧ (C : ZMod m) = 2 * a ∧ (C : ZMod h) = 2 * d ∧
      ∀ (i : Fin (n - 1)) (u : (ShortField b c)ˣ),
        omqMinusWt n ι ι' (((fun _ => a : Fin (n - 1) → ZMod m), d) : OmqMinusLat (n - 1) m h)
          (shortTorusHom n hirr i u) = ι' (u : ShortField b c) ^ C := by
  classical
  haveI := fact_shortField hirr
  haveI := finite_shortField (b := b) (c := c)
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have hcard := omq_omMinus_card_shortField_units hirr
  rw [← hm, ← hh] at hcard
  have hN : 0 < m * h := by rw [← hcard]; exact Nat.card_pos
  set N := m * h with hNdef
  set E : ℤ := ((Nat.card K : ℤ) + 1) * (a.val : ℤ) + (1 - (Nat.card K : ℤ)) * (d.val : ℤ)
    with hE
  let C₀ : ℕ := (E % (N : ℤ)).toNat
  have hC₀ : (C₀ : ℤ) = E % (N : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hN.ne'))
  have hC₀lt : C₀ < N := by
    have := Int.emod_lt_of_pos E (by exact_mod_cast hN : (0 : ℤ) < N)
    omega
  let C : ℕ := if C₀ = 0 then N else C₀
  have hC1 : 1 ≤ C := by
    show 1 ≤ if C₀ = 0 then N else C₀
    split_ifs with h0
    · exact hN
    · omega
  have hCN : C ≤ N := by
    show (if C₀ = 0 then N else C₀) ≤ N
    split_ifs with h0
    · exact le_rfl
    · omega
  have hCE : (C : ℤ) ≡ E [ZMOD (N : ℤ)] := by
    show ((if C₀ = 0 then N else C₀ : ℕ) : ℤ) ≡ E [ZMOD (N : ℤ)]
    split_ifs with h0
    · have : ((N : ℕ) : ℤ) ≡ 0 [ZMOD (N : ℤ)] := by simp [Int.modEq_zero_iff_dvd]
      refine this.trans ?_
      rw [h0] at hC₀
      exact (Int.modEq_iff_dvd.mpr (by simpa [Int.emod_emod_of_dvd] using
        (Int.dvd_of_emod_eq_zero hC₀.symm))).symm
    · rw [hC₀]
      exact (Int.mod_modEq E N)
  haveI : NeZero m := ⟨by rw [hm]; exact Nat.card_pos.ne'⟩
  haveI : NeZero h := ⟨by omega⟩
  have hqm : Nat.card K = m + 1 := by
    have h1 : m = Nat.card K - 1 := by rw [hm, Nat.card_units]
    omega
  have hqh : Nat.card K + 1 = h := hh.symm
  have hmN : m ∣ N := Dvd.intro _ rfl
  have hhN : h ∣ N := Dvd.intro_left _ rfl
  refine ⟨C, hC1, hCN, ?_, ?_, ?_⟩
  · have h1 : ((C : ℤ) : ZMod m) = (E : ZMod m) :=
      (ZMod.intCast_eq_intCast_iff _ _ m).mpr (Int.ModEq.of_dvd (by exact_mod_cast hmN) hCE)
    have h2 : (E : ZMod m) = 2 * a := by
      rw [hE]
      push_cast
      rw [hqm]
      simp [ZMod.natCast_self, ZMod.natCast_zmod_val]
      ring
    rw [← h2, ← h1]
    simp
  · have h1 : ((C : ℤ) : ZMod h) = (E : ZMod h) :=
      (ZMod.intCast_eq_intCast_iff _ _ h).mpr (Int.ModEq.of_dvd (by exact_mod_cast hhN) hCE)
    have h2 : (E : ZMod h) = 2 * d := by
      rw [hE]
      push_cast
      have h0 : (Nat.card K : ZMod h) + 1 = 0 := by
        rw [← Nat.cast_one, ← Nat.cast_add, hqh, ZMod.natCast_self]
      have h3 : (Nat.card K : ZMod h) = -1 := eq_neg_of_add_eq_zero_left h0
      rw [h3]
      simp [ZMod.natCast_zmod_val]
      ring
    rw [← h2, ← h1]
    simp
  · intro i u
    rw [omq_omMinus_wt_torus_short hirr ι ι' hι']
    show ι' (u : ShortField b c) ^ E = ι' (u : ShortField b c) ^ C
    have hne : ι' (u : ShortField b c) ≠ 0 := fun h0 =>
      u.ne_zero (ι'.injective (h0.trans (map_zero ι').symm))
    let w : kˣ := Units.mk0 (ι' (u : ShortField b c)) hne
    have hw : w ^ N = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      show ι' (u : ShortField b c) ^ N = 1
      have hu : u ^ N = 1 := by rw [← hcard]; exact pow_card_eq_one'
      rw [← map_pow, ← Units.val_pow_eq_pow_val, hu, Units.val_one, map_one]
    have hord : (orderOf w : ℤ) ∣ (N : ℤ) := by
      exact_mod_cast orderOf_dvd_of_pow_eq_one hw
    have hmod : E ≡ (C : ℤ) [ZMOD (orderOf w : ℤ)] := (Int.ModEq.of_dvd hord hCE).symm
    have hwE : w ^ E = w ^ (C : ℤ) := zpow_eq_zpow_iff_modEq.mpr hmod
    have := congrArg (fun x : kˣ => (x : k)) hwE
    simpa [Units.val_zpow_eq_zpow_val, zpow_natCast, w] using this

end CFSG.LocalAnalysis.WeakClosure81
