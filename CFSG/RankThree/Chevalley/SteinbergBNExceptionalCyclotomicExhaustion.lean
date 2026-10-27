module

public import CFSG.RankThree.SteinbergR3EOrdinaryECrossPrimeParts
public import CFSG.RankThree.Classical2.TwistedE6RationalOrder
public import CFSG.LieType.Chevalley.TrialityExactFiniteOrder
public import CFSG.RankThree.Chevalley.SteinbergCFExceptionalModelCover
public import CFSG.RankThree.Chevalley.EvenRealThreeCentralizingInvolution

public section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Polynomial
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.RankThree.OrdinaryECrossPrime (ordinary_E_exact_cross_prime_order_parts)
open CFSG.RankThree.Classical2 (twisted_E6_full_rational_fixed_group_order)

@[expose] noncomputable def exhaustionPhi : ℕ → ℤ[X]
  | 1 => X - 1
  | 2 => X + 1
  | 3 => X ^ 2 + X + 1
  | 4 => X ^ 2 + 1
  | 5 => X ^ 4 + X ^ 3 + X ^ 2 + X + 1
  | 6 => X ^ 2 - X + 1
  | 7 => X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1
  | 8 => X ^ 4 + 1
  | 9 => X ^ 6 + X ^ 3 + 1
  | 10 => X ^ 4 - X ^ 3 + X ^ 2 - X + 1
  | 12 => X ^ 4 - X ^ 2 + 1
  | 14 => X ^ 6 - X ^ 5 + X ^ 4 - X ^ 3 + X ^ 2 - X + 1
  | 15 => X ^ 8 - X ^ 7 + X ^ 5 - X ^ 4 + X ^ 3 - X + 1
  | 18 => X ^ 6 - X ^ 3 + 1
  | 20 => X ^ 8 - X ^ 6 + X ^ 4 - X ^ 2 + 1
  | 24 => X ^ 8 - X ^ 4 + 1
  | 30 => X ^ 8 + X ^ 7 - X ^ 5 - X ^ 4 - X ^ 3 + X + 1
  | _ => 0

@[expose] def exhaustionMinusFactors : ℕ → List ℕ
  | 2 => [1, 2]
  | 5 => [1, 5]
  | 6 => [1, 2, 3, 6]
  | 8 => [1, 2, 4, 8]
  | 9 => [1, 3, 9]
  | 10 => [1, 2, 5, 10]
  | 12 => [1, 2, 3, 4, 6, 12]
  | 14 => [1, 2, 7, 14]
  | 18 => [1, 2, 3, 6, 9, 18]
  | 20 => [1, 2, 4, 5, 10, 20]
  | 24 => [1, 2, 3, 4, 6, 8, 12, 24]
  | 30 => [1, 2, 3, 5, 6, 10, 15, 30]
  | _ => []

theorem pow_sub_one_eq_prod_exhaustionPhi (x : ℤ) {d : ℕ}
    (hd : d ∈ ([2, 5, 6, 8, 9, 10, 12, 14, 18, 20, 24, 30] : List ℕ)) :
    x ^ d - 1 = ((exhaustionMinusFactors d).map fun m => (exhaustionPhi m).eval x).prod := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [exhaustionMinusFactors, exhaustionPhi, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, eval_add, eval_sub, eval_pow, eval_X, eval_one, mul_one] <;> ring

theorem plus_factors_eq_prod_exhaustionPhi (x : ℤ) :
    x ^ 9 + 1 = ([2, 6, 18].map fun m => (exhaustionPhi m).eval x).prod ∧
      x ^ 5 + 1 = ([2, 10].map fun m => (exhaustionPhi m).eval x).prod ∧
      x ^ 8 + x ^ 4 + 1 = ([3, 6, 12].map fun m => (exhaustionPhi m).eval x).prod := by
  refine ⟨?_, ?_, ?_⟩ <;>
  simp only [exhaustionPhi, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, eval_add,
    eval_sub, eval_pow, eval_X, eval_one, mul_one] <;> ring

theorem exists_dvd_exhaustionPhi_of_dvd_prod {p : ℕ} (hp : p.Prime) {x : ℤ} {M : List ℕ}
    (h : (p : ℤ) ∣ (M.map fun m => (exhaustionPhi m).eval x).prod) :
    ∃ m ∈ M, (p : ℤ) ∣ (exhaustionPhi m).eval x := by
  obtain ⟨a, ha, hpa⟩ := (Prime.dvd_prod_iff (Nat.prime_iff_prime_int.mp hp)).mp h
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp ha
  exact ⟨m, hm, hpa⟩

theorem exists_mem_dvd_of_ordProj_eq_prod {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) (hpn : p ∣ n)
    {D : List ℕ} {g : ℕ → ℕ} (h : ordProj[p] n = (D.map fun d => ordProj[p] (g d)).prod) :
    ∃ d ∈ D, p ∣ g d := by
  by_contra hcon
  push Not at hcon
  have h1 : (D.map fun d => ordProj[p] (g d)).prod = 1 := List.prod_eq_one fun x hx => by
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
    rw [Nat.factorization_eq_zero_of_not_dvd (hcon d hd), pow_zero]
  rw [h1] at h
  rcases Nat.pow_eq_one.mp h with h2 | h2
  · exact hp.one_lt.ne' h2
  · exact (hp.factorization_pos_of_dvd hn hpn).ne' h2

theorem exists_mem_row_of_dvd_pow_sub_one {p q : ℕ} (hp : p.Prime) (hq : 1 ≤ q) {D : List ℕ}
    (hD : ∀ d ∈ D, d ∈ ([2, 5, 6, 8, 9, 10, 12, 14, 18, 20, 24, 30] : List ℕ)) {row : Finset ℕ}
    (hrow : ∀ d ∈ D, ∀ m ∈ exhaustionMinusFactors d, m ∈ row) (h : ∃ d ∈ D, p ∣ q ^ d - 1) :
    ∃ m ∈ row, (p : ℤ) ∣ (exhaustionPhi m).eval (q : ℤ) := by
  obtain ⟨d, hdD, hpd⟩ := h
  have hcast : ((q ^ d - 1 : ℕ) : ℤ) = (q : ℤ) ^ d - 1 := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hq), Nat.cast_pow, Nat.cast_one]
  have h1 : (p : ℤ) ∣ (q : ℤ) ^ d - 1 := by
    rw [← hcast]
    exact Int.natCast_dvd_natCast.mpr hpd
  rw [pow_sub_one_eq_prod_exhaustionPhi _ (hD d hdD)] at h1
  obtain ⟨m, hm, hpm⟩ := exists_dvd_exhaustionPhi_of_dvd_prod hp h1
  exact ⟨m, hrow d hdD m hm, hpm⟩

theorem eq_and_eq_one_of_zmod_geom_sum_eq_zero {p r : ℕ} (hp : p = 5 ∨ p = 7) (hr : r = 5 ∨ r = 7)
    (hpr : p ≤ r) (y : ZMod p) (hy : y ≠ 0) (h : ∑ j ∈ Finset.range r, y ^ j = 0) :
    p = r ∧ y = 1 := by
  rcases hp with rfl | rfl <;> rcases hr with rfl | rfl
  · revert y
    decide
  · revert y
    decide
  · omega
  · revert y
    decide

theorem small_prime_geom_sum_guard {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {q : ℤ}
    (hpq : ¬(p : ℤ) ∣ q) {r : ℕ} (hr : r = 5 ∨ r = 7) {δ : ℤ} (hδ : δ = 1 ∨ δ = -1)
    (h : (p : ℤ) ∣ ∑ j ∈ Finset.range r, (δ * q) ^ j) (hpr : p ≤ r) :
    p = r ∧ q ≡ δ [ZMOD r] := by
  have hp57 : p = 5 ∨ p = 7 := by
    have hr7 : r ≤ 7 := by omega
    have hp7 : p ≤ 7 := hpr.trans hr7
    interval_cases p
    · exact absurd hp (by norm_num)
    · exact Or.inl rfl
    · exact absurd hp (by norm_num)
    · exact Or.inr rfl
  have hδ2 : δ * δ = 1 := by rcases hδ with rfl | rfl <;> norm_num
  have hy : ((δ * q : ℤ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro hd
    apply hpq
    have := dvd_mul_of_dvd_right hd δ
    rwa [← mul_assoc, hδ2, one_mul] at this
  have hs : ∑ j ∈ Finset.range r, ((δ * q : ℤ) : ZMod p) ^ j = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h
    push_cast at this ⊢
    exact this
  obtain ⟨rfl, hy1⟩ := eq_and_eq_one_of_zmod_geom_sum_eq_zero hp57 hr hpr _ hy hs
  refine ⟨rfl, (ZMod.intCast_eq_intCast_iff _ _ _).mp ?_⟩
  have h1 : ((δ : ℤ) : ZMod p) * ((δ * q : ℤ) : ZMod p) = ((δ : ℤ) : ZMod p) := by
    rw [hy1, mul_one]
  have h2 : ((δ * (δ * q) : ℤ) : ZMod p) = ((δ : ℤ) : ZMod p) := by
    push_cast at h1 ⊢
    exact h1
  rwa [← mul_assoc, hδ2, one_mul] at h2

theorem exhaustionPhi_twenty_mod_five :
    (5 : ℤ[X]) ∣ exhaustionPhi 20 - (X ^ 2 + 1) ^ 4 ∧
      ∀ x : ℤ, (5 : ℤ) ∣ (exhaustionPhi 20).eval x ↔ (5 : ℤ) ∣ (exhaustionPhi 4).eval x := by
  refine ⟨⟨-(X ^ 6 + X ^ 4 + X ^ 2), by simp only [exhaustionPhi]; ring⟩, fun x => ?_⟩
  have e : (exhaustionPhi 20).eval x = (x ^ 2 + 1) ^ 4 - 5 * (x ^ 6 + x ^ 4 + x ^ 2) := by
    simp only [exhaustionPhi, eval_add, eval_sub, eval_pow, eval_X, eval_one]
    ring
  have e4 : (exhaustionPhi 4).eval x = x ^ 2 + 1 := by
    simp only [exhaustionPhi, eval_add, eval_pow, eval_X, eval_one]
  rw [e, e4]
  have h5 : Prime (5 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by norm_num)
  constructor
  · intro h
    have h' : (5 : ℤ) ∣ (x ^ 2 + 1) ^ 4 := by
      have := dvd_add h (dvd_mul_right 5 (x ^ 6 + x ^ 4 + x ^ 2))
      rwa [sub_add_cancel] at this
    exact h5.dvd_of_dvd_pow h'
  · intro h
    exact dvd_sub (dvd_pow h (by norm_num)) (dvd_mul_right _ _)

theorem exact_E_type_and_triality_cross_prime_factor_exhaustion {p ℓ f : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hℓp : ℓ ≠ p) {T : Type} [Group T] [Finite T] {τ : StatedLieTag}
    (hmod : ChevalleyExceptionalModel T τ ℓ f) :
    (p ∣ Nat.card T →
      (τ = .E6 → ∃ m ∈ ({1, 2, 3, 4, 5, 6, 8, 9, 12} : Finset ℕ),
        (p : ℤ) ∣ (exhaustionPhi m).eval ((ℓ ^ f : ℕ) : ℤ)) ∧
      (τ = .E7 → ∃ m ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 18} : Finset ℕ),
        (p : ℤ) ∣ (exhaustionPhi m).eval ((ℓ ^ f : ℕ) : ℤ)) ∧
      (τ = .E8 → ∃ m ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 18, 20, 24, 30} : Finset ℕ),
        (p : ℤ) ∣ (exhaustionPhi m).eval ((ℓ ^ f : ℕ) : ℤ)) ∧
      (τ = .twistedE6 → ∃ m ∈ ({1, 2, 3, 4, 6, 8, 10, 12, 18} : Finset ℕ),
        (p : ℤ) ∣ (exhaustionPhi m).eval ((ℓ ^ f : ℕ) : ℤ)) ∧
      (τ = .trialityD4 → ∃ m ∈ ({1, 2, 3, 6, 12} : Finset ℕ),
        (p : ℤ) ∣ (exhaustionPhi m).eval ((ℓ ^ f : ℕ) : ℤ))) ∧
    (∀ r : ℕ, r = 5 ∨ r = 7 → ∀ δ : ℤ, δ = 1 ∨ δ = -1 →
      (p : ℤ) ∣ ∑ j ∈ Finset.range r, (δ * ((ℓ ^ f : ℕ) : ℤ)) ^ j → p ≤ r →
        p = r ∧ ((ℓ ^ f : ℕ) : ℤ) ≡ δ [ZMOD r]) ∧
    ((5 : ℤ[X]) ∣ exhaustionPhi 20 - (X ^ 2 + 1) ^ 4 ∧
      ∀ x : ℤ, (5 : ℤ) ∣ (exhaustionPhi 20).eval x ↔ (5 : ℤ) ∣ (exhaustionPhi 4).eval x) := by
  have hℓ : ℓ.Prime := hmod.1.1
  have hf : 1 ≤ f := hmod.1.2.1
  have hpq : ¬p ∣ ℓ ^ f := fun h =>
    hℓp ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp (hp.dvd_of_dvd_pow h)).symm
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  refine ⟨fun hpT => ?_, fun r hr δ hδ h hpr => small_prime_geom_sum_guard hp hp3
    (fun h' => hpq (Int.natCast_dvd_natCast.mp h')) hr hδ h hpr, exhaustionPhi_twenty_mod_five⟩
  have hT0 : Nat.card T ≠ 0 := Nat.card_pos.ne'
  have hord : ∀ τ' : Tag, UntwistedChevalleyModel T τ' (ℓ ^ f) →
      ∃ K : Type, ∃ _ : Field K, ∃ _ : Finite K, Nat.card K = ℓ ^ f ∧
        Nat.card (adjointGroup τ' K) = Nat.card T := by
    intro τ' hU
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted hU
    exact ⟨K, inferInstance, inferInstance, hK, Nat.card_congr e.toEquiv⟩
  refine ⟨fun hτ => ?_, fun hτ => ?_, fun hτ => ?_, fun hτ => ?_, fun hτ => ?_⟩
  · subst hτ
    obtain ⟨K, _, _, hK, hcard⟩ := hord .E6 hmod.2
    have h := (ordinary_E_exact_cross_prime_order_parts (K := K) hp hp3
      (by rw [hK]; exact hpq)).1
    rw [hcard, hK] at h
    exact exists_mem_row_of_dvd_pow_sub_one hp hq1 (by decide) (by decide)
      (exists_mem_dvd_of_ordProj_eq_prod hp hT0 hpT h)
  · subst hτ
    obtain ⟨K, _, _, hK, hcard⟩ := hord .E7 hmod.2
    have h := (ordinary_E_exact_cross_prime_order_parts (K := K) hp hp3
      (by rw [hK]; exact hpq)).2.1
    rw [hcard, hK] at h
    exact exists_mem_row_of_dvd_pow_sub_one hp hq1 (by decide) (by decide)
      (exists_mem_dvd_of_ordProj_eq_prod hp hT0 hpT h)
  · subst hτ
    obtain ⟨K, _, _, hK, hcard⟩ := hord .E8 hmod.2
    have h := (ordinary_E_exact_cross_prime_order_parts (K := K) hp hp3
      (by rw [hK]; exact hpq)).2.2
    rw [hcard, hK] at h
    exact exists_mem_row_of_dvd_pow_sub_one hp hq1 (by decide) (by decide)
      (exists_mem_dvd_of_ordProj_eq_prod hp hT0 hpT h)
  ·
    subst hτ
    obtain ⟨-, K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hmod
    replace hK : Nat.card K = (ℓ ^ f) ^ 2 := hK
    obtain ⟨e'⟩ := nonempty_derivedCentralQuotient_equiv .E6 hℓ hf K hK σ hσ
    have hTC : Nat.card T = Nat.card (graphFixedRootGroup TwistTag.E6 K σ) :=
      Nat.card_congr (e.trans e').toEquiv
    have : Fact ℓ.Prime := ⟨hℓ⟩
    have : CharP K ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      hℓ (by omega : 1 ≤ f * 2) (by rw [hK, ← pow_mul])
    let Ω := AlgebraicClosure K
    have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap K Ω).injective ℓ
    obtain ⟨hfin, -, hder, -, -, hRcard, -⟩ := twisted_E6_full_rational_fixed_group_order hℓ hf K
      hK σ hσ Ω (iterateFrobenius Ω ℓ f) (fun c => iterateFrobenius_def ℓ f c)
    have hle : (graphFixedRootGroup TwistTag.E6 K σ).map (baseChangeGL (algebraMap K Ω)) ≤
        twistedFixedGroup TwistTag.E6 Ω (iterateFrobenius Ω ℓ f) := by
      rw [← hder]
      exact Subgroup.commutator_le_self _
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective (baseChangeGL_injective _), ← hTC, hRcard] at hdvd
    have hpR := hpT.trans hdvd
    set q := ℓ ^ f
    have hminus : ∀ d ∈ ([12, 8, 6, 2] : List ℕ), p ∣ q ^ d - 1 →
        ∃ m ∈ ({1, 2, 3, 4, 6, 8, 10, 12, 18} : Finset ℕ),
          (p : ℤ) ∣ (exhaustionPhi m).eval (q : ℤ) := fun d hd hpd =>
      exists_mem_row_of_dvd_pow_sub_one hp hq1 (D := [12, 8, 6, 2]) (by decide) (by decide)
        ⟨d, hd, hpd⟩
    have hplus : ∀ M : List ℕ, (∀ m ∈ M, m ∈ ({1, 2, 3, 4, 6, 8, 10, 12, 18} : Finset ℕ)) →
        ∀ n : ℕ, (n : ℤ) = (M.map fun m => (exhaustionPhi m).eval (q : ℤ)).prod → p ∣ n →
        ∃ m ∈ ({1, 2, 3, 4, 6, 8, 10, 12, 18} : Finset ℕ),
          (p : ℤ) ∣ (exhaustionPhi m).eval (q : ℤ) := fun M hM n hn hpn => by
      have h1 : (p : ℤ) ∣ (M.map fun m => (exhaustionPhi m).eval (q : ℤ)).prod := by
        rw [← hn]
        exact Int.natCast_dvd_natCast.mpr hpn
      obtain ⟨m, hm, hpm⟩ := exists_dvd_exhaustionPhi_of_dvd_prod hp h1
      exact ⟨m, hM m hm, hpm⟩
    obtain ⟨h9, h5, -⟩ := plus_factors_eq_prod_exhaustionPhi (q : ℤ)
    rcases (Nat.Prime.dvd_mul hp).1 hpR with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
        · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
          · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
            · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
              · exact absurd (hp.dvd_of_dvd_pow h) hpq
              · exact hminus 12 (by decide) h
            · exact hplus [2, 6, 18] (by decide) _ (by push_cast; exact h9) h
          · exact hminus 8 (by decide) h
        · exact hminus 6 (by decide) h
      · exact hplus [2, 10] (by decide) _ (by push_cast; exact h5) h
    · exact hminus 2 (by decide) h
  ·
    subst hτ
    obtain ⟨-, K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hmod
    replace hK : Nat.card K = (ℓ ^ f) ^ 3 := hK
    obtain ⟨e'⟩ := nonempty_derivedCentralQuotient_equiv .D4 hℓ hf K hK σ hσ
    have hTC : Nat.card T = Nat.card (graphFixedRootGroup TwistTag.D4 K σ) :=
      Nat.card_congr (e.trans e').toEquiv
    obtain ⟨hC, -⟩ := triality_both_orientations_exact_finite_order ℓ f hℓ hf K hK 1
      (Or.inl rfl) σ (fun c => by rw [pow_one]; exact hσ c)
    rw [← hTC] at hC
    rw [hC] at hpT
    set q := ℓ ^ f
    have hrow : ∀ M : List ℕ, (∀ m ∈ M, m ∈ ({1, 2, 3, 6, 12} : Finset ℕ)) →
        ∀ n : ℕ, (n : ℤ) = (M.map fun m => (exhaustionPhi m).eval (q : ℤ)).prod → p ∣ n →
        ∃ m ∈ ({1, 2, 3, 6, 12} : Finset ℕ), (p : ℤ) ∣ (exhaustionPhi m).eval (q : ℤ) :=
      fun M hM n hn hpn => by
        have h1 : (p : ℤ) ∣ (M.map fun m => (exhaustionPhi m).eval (q : ℤ)).prod := by
          rw [← hn]
          exact Int.natCast_dvd_natCast.mpr hpn
        obtain ⟨m, hm, hpm⟩ := exists_dvd_exhaustionPhi_of_dvd_prod hp h1
        exact ⟨m, hM m hm, hpm⟩
    have hcast : ∀ d, ((q ^ d - 1 : ℕ) : ℤ) = (q : ℤ) ^ d - 1 := fun d => by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ hq1), Nat.cast_pow, Nat.cast_one]
    obtain ⟨-, -, h8⟩ := plus_factors_eq_prod_exhaustionPhi (q : ℤ)
    rcases (Nat.Prime.dvd_mul hp).1 hpT with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
        · exact absurd (hp.dvd_of_dvd_pow h) hpq
        · exact hrow (exhaustionMinusFactors 2) (by decide) _
            (by rw [hcast]; exact pow_sub_one_eq_prod_exhaustionPhi _ (by decide)) h
      · exact hrow (exhaustionMinusFactors 6) (by decide) _
          (by rw [hcast]; exact pow_sub_one_eq_prod_exhaustionPhi _ (by decide)) h
    · exact hrow [3, 6, 12] (by decide) _ (by push_cast; exact h8) h

end CFSG.RankThree.Chevalley
