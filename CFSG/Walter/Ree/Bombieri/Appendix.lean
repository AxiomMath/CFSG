module

public import CFSG.Walter.Ree.Bombieri.AppCheck
public import CFSG.Walter.Ree.Defs
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.Walter.Ree.Bombieri

open Polynomial

theorem F3P.valid_normalize (a : F3P) : (F3P.normalize a).Valid := by
  apply F3P.valid_of_testBit
  intro i
  simp only [F3P.normalize, Nat.testBit_xor, Nat.testBit_and]
  cases a.p.testBit i <;> cases a.n.testBit i <;> decide

theorem F3P.ev_ne_zero_of_unitCheck {R : Type*} [CommRing R] [Nontrivial R]
    {ι : ZMod 3 →+* R} {r : R} {f a : F3P} {k : ℕ} (hf : f.Valid) (ha : a.Valid)
    (hf0 : F3P.ev ι r f = 0) (h : F3P.unitCheck f k a = true) : F3P.ev ι r a ≠ 0 := by
  intro h0
  have h1 := congrArg (F3P.ev ι r) (beq_iff_eq.mp h)
  rw [F3P.ev_mulMod hf ha (F3P.valid_normalize _) hf0, h0, zero_mul, F3P.ev_one] at h1
  exact zero_ne_one h1

variable {K : Type*} [Field K] [Fintype K] [CharP K 3]

noncomputable abbrev castThree (K : Type*) [Field K] [CharP K 3] : ZMod 3 →+* K :=
  ZMod.castHom (dvd_refl 3) K

theorem exists_root_of_rootCheck {k : ℕ} (hK : Fintype.card K = 3 ^ k) {f : F3P}
    (h : F3P.rootCheck f k = true) : ∃ r : K, F3P.ev (castThree K) r f = 0 := by
  simp only [F3P.rootCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hv, hk⟩, hk1⟩, hpow⟩ := h
  have hv' : f.Valid := (F3P.valid_iff f).mpr hv
  set g := F3P.decode f with hg
  have hdvd : g ∣ X ^ (3 ^ k) - X := by
    have h1 := congrArg (F3P.ev (AdjoinRoot.of g) (AdjoinRoot.root g)) hpow
    have h0 : F3P.ev (AdjoinRoot.of g) (AdjoinRoot.root g) f = 0 := by
      rw [F3P.ev_def]; exact AdjoinRoot.eval₂_root g
    rw [F3P.ev_powMod hv' F3P.valid_X h0, F3P.ev_X] at h1
    rw [← AdjoinRoot.mk_eq_zero, map_sub, map_pow, AdjoinRoot.mk_X, h1, sub_self]
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  have hsplit : Splits (X ^ Fintype.card K - X : K[X]) := by
    rw [splits_iff_card_roots, FiniteField.roots_X_pow_card_sub_X,
      FiniteField.X_pow_card_sub_X_natDegree_eq K hq]
    rfl
  have hdvdK : g.map (castThree K) ∣ X ^ Fintype.card K - X := by
    rw [hK]
    simpa using Polynomial.map_dvd (castThree K) hdvd
  have hgs := hsplit.of_dvd (FiniteField.X_pow_card_sub_X_ne_zero K hq) hdvdK
  have hcoeff : (g.map (castThree K)).coeff k ≠ 0 := by
    have hn : f.n.testBit k = false := by
      have := hv'.not_both k
      simpa [hk] using this
    rw [coeff_map, hg, F3P.coeff_decode]
    simp [F3P.cf, hk, hn]
  have hdeg : (g.map (castThree K)).degree ≠ 0 := by
    have hne : g.map (castThree K) ≠ 0 := fun h0 => hcoeff (by rw [h0, coeff_zero])
    rw [degree_eq_natDegree hne]
    have := le_natDegree_of_ne_zero hcoeff
    exact_mod_cast (by omega : (g.map (castThree K)).natDegree ≠ 0)
  obtain ⟨r, hr⟩ := hgs.exists_eval_eq_zero hdeg
  exact ⟨r, by rwa [eval_map, ← F3P.ev_def] at hr⟩

omit [CharP K 3] in
theorem pow_eq_self_of_mod {n : ℕ} (hn : n % (Fintype.card K - 1) = 1) (x : K) : x ^ n = x := by
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  by_cases hx : x = 0
  · rw [hx, zero_pow hn0]
  · conv_lhs => rw [← Nat.div_add_mod n (Fintype.card K - 1), hn, pow_add, pow_mul,
      FiniteField.pow_card_sub_one_eq_one x hx, one_pow, one_mul, pow_one]

omit [CharP K 3] in
theorem pow_eq_pow_of_modEq {n m : ℕ} (h : n ≡ m [MOD Fintype.card K - 1]) {x : K} (hx : x ≠ 0) :
    x ^ n = x ^ m := by
  have hu : (Units.mk0 x hx) ^ n = (Units.mk0 x hx) ^ m := by
    classical
    rw [pow_eq_pow_iff_modEq]
    refine h.of_dvd ?_
    rw [← Fintype.card_units]
    exact orderOf_dvd_card
  simpa using congrArg Units.val hu

omit [CharP K 3] in
theorem modEq_of_exponent {b a : ℕ} {σ : K ≃+* K} (hσ : ∀ x, σ x = x ^ 3 ^ b)
    (hB : ∀ x : K, (σ x * x) ^ a = x ^ 2) : (3 ^ b + 1) * a ≡ 2 [MOD Fintype.card K - 1] := by
  have ha : a ≠ 0 := by
    rintro rfl
    simpa using hB 0
  have hle : 2 ≤ (3 ^ b + 1) * a := by
    have h3 : 2 ≤ 3 ^ b + 1 := by have := Nat.one_le_pow b 3 (by norm_num); omega
    calc 2 = 2 * 1 := by norm_num
      _ ≤ (3 ^ b + 1) * a := Nat.mul_le_mul h3 (Nat.pos_of_ne_zero ha)
  have hall : ∀ x : Kˣ, x ^ ((3 ^ b + 1) * a - 2) = 1 := by
    intro x
    have h1 := hB x
    rw [hσ, ← pow_succ, ← pow_mul] at h1
    have h2 : (x : K) ^ ((3 ^ b + 1) * a - 2) * (x : K) ^ 2 = 1 * (x : K) ^ 2 := by
      rw [← pow_add, Nat.sub_add_cancel hle, h1, one_mul]
    have h3 := mul_right_cancel₀ (pow_ne_zero 2 x.ne_zero) h2
    exact Units.ext (by simpa using h3)
  have hdvd := (FiniteField.forall_pow_eq_one_iff K _).mp hall
  exact ((Nat.modEq_iff_dvd' hle).mpr hdvd).symm

omit [Fintype K] in
theorem three_eq_zero : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3

theorem checkCase_sound {k b : ℕ} (hK : Fintype.card K = 3 ^ k) {f : F3P} (hf : f.Valid)
    {r : K} (hr : F3P.ev (castThree K) r f = 0) (h : F3P.checkCase f k b = true)
    {σ : K ≃+* K} (hσ : ∀ x, σ x = x ^ 3 ^ b) {a : ℕ} (ha : Even a)
    (hB : ∀ x : K, (σ x * x) ^ a = x ^ 2) :
    ∃ p ∈ ESigma K σ, thompsonT a p.1 p.2.1 p.2.2 ≠ 0 := by
  simp only [F3P.checkCase, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨harith, hu0⟩, hu1⟩, hu2⟩, hT⟩ := h
  simp only [F3P.arithCheck, Bool.and_eq_true, beq_iff_eq] at harith
  obtain ⟨⟨⟨⟨⟨⟨hs, hac⟩, haeven⟩, hq2⟩, hhodd⟩, hb2⟩, hgcd⟩ := harith
  rw [← hK] at hs hac hq2 hhodd hgcd
  set s := F3P.expS k b
  set ac := F3P.expA k b
  set v := F3P.caseVals f k b with hv
  have vX : (F3P.X).Valid := F3P.valid_X
  have v1 : (F3P.one).Valid := F3P.valid_one
  have hz : v.z = F3P.powMod f k (F3P.add F3P.X F3P.one) s := rfl
  have hy : v.y = F3P.powMod f k (F3P.sub F3P.X F3P.one) s := rfl
  have hu : v.u = F3P.sub (F3P.powMod f k v.z (3 ^ b + 1)) (F3P.powMod f k v.y (3 ^ b + 1)) := rfl
  have hA : v.A = F3P.powMod f k (F3P.sub v.u F3P.one) ac := rfl
  have hBv : v.B = F3P.powMod f k v.u ac := rfl
  have hC : v.C = F3P.powMod f k (F3P.add v.u F3P.one) ac := rfl
  have hTv : v.T = F3P.add (F3P.sub (F3P.sub (F3P.mulMod f k v.z v.A)
      (F3P.mulMod f k (F3P.add (F3P.sub v.z v.y) F3P.one) v.B)) (F3P.mulMod f k v.y v.C))
      (F3P.mulMod f k v.A v.C) := rfl
  have vz : v.z.Valid := by rw [hz]; exact F3P.valid_powMod hf (F3P.valid_add vX v1)
  have vy : v.y.Valid := by rw [hy]; exact F3P.valid_powMod hf (F3P.valid_sub vX v1)
  have vu : v.u.Valid := by
    rw [hu]; exact F3P.valid_sub (F3P.valid_powMod hf vz) (F3P.valid_powMod hf vy)
  have vA : v.A.Valid := by rw [hA]; exact F3P.valid_powMod hf (F3P.valid_sub vu v1)
  have vB : v.B.Valid := by rw [hBv]; exact F3P.valid_powMod hf vu
  have vC : v.C.Valid := by rw [hC]; exact F3P.valid_powMod hf (F3P.valid_add vu v1)
  have vT : v.T.Valid := by
    rw [hTv]
    exact F3P.valid_add (F3P.valid_sub (F3P.valid_sub (F3P.valid_mulMod hf vz)
      (F3P.valid_mulMod hf (F3P.valid_add (F3P.valid_sub vz vy) v1))) (F3P.valid_mulMod hf vy))
      (F3P.valid_mulMod hf vA)
  have ez : F3P.ev (castThree K) r v.z = (r + 1) ^ s := by
    rw [hz, F3P.ev_powMod hf (F3P.valid_add vX v1) hr, F3P.ev_add vX v1, F3P.ev_X, F3P.ev_one]
  have ey : F3P.ev (castThree K) r v.y = (r - 1) ^ s := by
    rw [hy, F3P.ev_powMod hf (F3P.valid_sub vX v1) hr, F3P.ev_sub vX v1, F3P.ev_X, F3P.ev_one]
  have eu : F3P.ev (castThree K) r v.u =
      F3P.ev (castThree K) r v.z ^ (3 ^ b + 1) - F3P.ev (castThree K) r v.y ^ (3 ^ b + 1) := by
    rw [hu, F3P.ev_sub (F3P.valid_powMod hf vz) (F3P.valid_powMod hf vy),
      F3P.ev_powMod hf vz hr, F3P.ev_powMod hf vy hr]
  have eA : F3P.ev (castThree K) r v.A = (F3P.ev (castThree K) r v.u - 1) ^ ac := by
    rw [hA, F3P.ev_powMod hf (F3P.valid_sub vu v1) hr, F3P.ev_sub vu v1, F3P.ev_one]
  have eB : F3P.ev (castThree K) r v.B = F3P.ev (castThree K) r v.u ^ ac := by
    rw [hBv, F3P.ev_powMod hf vu hr]
  have eC : F3P.ev (castThree K) r v.C = (F3P.ev (castThree K) r v.u + 1) ^ ac := by
    rw [hC, F3P.ev_powMod hf (F3P.valid_add vu v1) hr, F3P.ev_add vu v1, F3P.ev_one]
  have eT : F3P.ev (castThree K) r v.T =
      F3P.ev (castThree K) r v.z * F3P.ev (castThree K) r v.A -
        (F3P.ev (castThree K) r v.z - F3P.ev (castThree K) r v.y + 1) *
          F3P.ev (castThree K) r v.B -
        F3P.ev (castThree K) r v.y * F3P.ev (castThree K) r v.C +
      F3P.ev (castThree K) r v.A * F3P.ev (castThree K) r v.C := by
    rw [hTv, F3P.ev_add _ (F3P.valid_mulMod hf vA), F3P.ev_sub _ (F3P.valid_mulMod hf vy),
      F3P.ev_sub (F3P.valid_mulMod hf vz) (F3P.valid_mulMod hf _), F3P.ev_mulMod hf vz vA hr,
      F3P.ev_mulMod hf (F3P.valid_add (F3P.valid_sub vz vy) v1) vB hr,
      F3P.ev_add (F3P.valid_sub vz vy) v1, F3P.ev_sub vz vy, F3P.ev_one,
      F3P.ev_mulMod hf vy vC hr, F3P.ev_mulMod hf vA vC hr]
    all_goals first
      | exact F3P.valid_sub (F3P.valid_sub (F3P.valid_mulMod hf vz)
          (F3P.valid_mulMod hf (F3P.valid_add (F3P.valid_sub vz vy) v1)))
          (F3P.valid_mulMod hf vy)
      | exact F3P.valid_sub (F3P.valid_mulMod hf vz)
          (F3P.valid_mulMod hf (F3P.valid_add (F3P.valid_sub vz vy) v1))
      | exact F3P.valid_add (F3P.valid_sub vz vy) v1
  have nu0 : F3P.ev (castThree K) r v.u ≠ 0 := F3P.ev_ne_zero_of_unitCheck hf vu hr hu0
  have nu1 : F3P.ev (castThree K) r v.u - 1 ≠ 0 := by
    have := F3P.ev_ne_zero_of_unitCheck hf (F3P.valid_sub vu v1) hr hu1
    rwa [F3P.ev_sub vu v1, F3P.ev_one] at this
  have nu2 : F3P.ev (castThree K) r v.u + 1 ≠ 0 := by
    have := F3P.ev_ne_zero_of_unitCheck hf (F3P.valid_add vu v1) hr hu2
    rwa [F3P.ev_add vu v1, F3P.ev_one] at this
  have nT : F3P.ev (castThree K) r v.T ≠ 0 := F3P.ev_ne_zero_of_unitCheck hf vT hr hT
  set z := F3P.ev (castThree K) r v.z
  set y := F3P.ev (castThree K) r v.y
  set u := F3P.ev (castThree K) r v.u
  have hpow (w : K) : (w ^ s) ^ (3 ^ b + 2) = w := by
    rw [← pow_mul, mul_comm]; exact pow_eq_self_of_mod hs w
  have hq1 : 2 < Fintype.card K - 1 := by
    have hpos : 0 < Fintype.card K - 1 := by have := Fintype.one_lt_card (α := K); omega
    have := Nat.mod_lt ((3 ^ b + 1) * ac) hpos
    omega
  have hmodA : a ≡ ac [MOD Fintype.card K - 1] := by
    have h1 := modEq_of_exponent hσ hB
    have h2 : (3 ^ b + 1) * ac ≡ 2 [MOD Fintype.card K - 1] := by
      unfold Nat.ModEq; rw [hac, Nat.mod_eq_of_lt hq1]
    have h12 := h1.trans h2.symm
    obtain ⟨c, hc⟩ : ∃ c, 3 ^ b + 1 = 2 * c := ⟨(3 ^ b + 1) / 2, by omega⟩
    obtain ⟨hh, hh'⟩ : ∃ hh, Fintype.card K - 1 = 2 * hh := ⟨(Fintype.card K - 1) / 2, by omega⟩
    rw [hc, hh', mul_assoc, mul_assoc] at h12
    have h3 := Nat.ModEq.mul_left_cancel' two_ne_zero h12
    rw [show (3 ^ b + 1) / 2 = c by omega, show (Fintype.card K - 1) / 2 = hh by omega] at hgcd
    have h4 : a ≡ ac [MOD hh] :=
      Nat.ModEq.cancel_left_of_coprime (by rw [Nat.gcd_comm]; exact hgcd) h3
    have h5 : a ≡ ac [MOD 2] := by
      unfold Nat.ModEq; rw [Nat.even_iff.mp ha, haeven]
    have hodd : Odd hh := Nat.odd_iff.mpr (by
      rw [show (Fintype.card K - 1) / 2 = hh by omega] at hhodd; exact hhodd)
    rw [hh']
    exact (Nat.modEq_and_modEq_iff_modEq_mul (Nat.coprime_two_left.mpr hodd)).mp ⟨h5, h4⟩
  refine ⟨(z, y, u), ⟨?_, ?_, ?_⟩, ?_⟩
  ·
    simp only [hσ]
    rw [← pow_add, ← pow_add, ez, ey, hpow, hpow]
    linear_combination (three_eq_zero (K := K))
  · simp only [hσ]
    rw [← pow_succ, ← pow_succ, eu]
  · intro h3
    have : (u - 1) * u * (u + 1) = 0 := by linear_combination h3
    rcases mul_eq_zero.mp this with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact nu1 h
      · exact nu0 h
    · exact nu2 h
  · simp only [thompsonT]
    rw [pow_eq_pow_of_modEq hmodA nu1, pow_eq_pow_of_modEq hmodA nu0,
      pow_eq_pow_of_modEq hmodA nu2,
      show u ^ 2 - 1 = (u - 1) * (u + 1) by ring,
      pow_eq_pow_of_modEq hmodA (mul_ne_zero nu1 nu2), mul_pow, ← eA, ← eB, ← eC, ← eT]
    exact nT

end CFSG.Walter.Ree.Bombieri
