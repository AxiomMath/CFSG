module

public import CFSG.Timmesfeld.LieEmbed.UnitaryWitt

public section

namespace CFSG.Timmesfeld.LieEmbed

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

section Linear

variable {F : Type*} [Field F] {σ : F ≃+* F} {n : ℕ}

theorem uForm_add_left (x y v : Fin n → F) : uForm σ (x + y) v = uForm σ x v + uForm σ y v := by
  simp only [uForm_eq, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem uForm_sub_right (v x y : Fin n → F) : uForm σ v (x - y) = uForm σ v x - uForm σ v y := by
  simp only [uForm_eq, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem uForm_zero_right (v : Fin n → F) : uForm σ v 0 = 0 := by
  simp [uForm_eq]

theorem uForm_sum_right {ι : Type*} (s : Finset ι) (v : Fin n → F) (x : ι → Fin n → F) :
    uForm σ v (∑ k ∈ s, x k) = ∑ k ∈ s, uForm σ v (x k) := by
  simp only [uForm_eq, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

theorem IsUTransGroup.commute {v : Fin n → F} {X : Subgroup (SU σ n)} (h : IsUTransGroup σ v X)
    (hvv : uForm σ v v = 0) : ∀ x ∈ X, ∀ y ∈ X, Commute x y := by
  intro x hx y hy
  obtain ⟨a, -, ha⟩ := (h.1 x).1 hx
  obtain ⟨b, -, hb⟩ := (h.1 y).1 hy
  apply suMat_injective σ
  rw [map_mul, map_mul, ha, hb, uTrans_mul_uTrans σ hvv, uTrans_mul_uTrans σ hvv, add_comm]

theorem uForm_eq_zero_comm (hσ : ∀ c, σ (σ c) = c) {x y : Fin n → F} (h : uForm σ x y = 0) :
    uForm σ y x = 0 := by
  rw [← uForm_conj σ hσ, h, map_zero]

variable (σ) in
@[expose] def uFormL (v : Fin n → F) : (Fin n → F) →ₗ[F] F where
  toFun := uForm σ v
  map_add' := uForm_add_right v
  map_smul' c x := uForm_smul_right σ c v x

variable (σ) in
theorem exists_ne_zero_forall_uForm_eq_zero {ι : Type*} [Fintype ι] (s : ι → Fin n → F)
    (hs : Fintype.card ι < n) : ∃ v : Fin n → F, v ≠ 0 ∧ ∀ k, uForm σ (s k) v = 0 := by
  have hker := LinearMap.ker_ne_bot_of_finrank_lt
    (f := LinearMap.pi fun k => uFormL σ (s k))
    (by rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fin_fun]; exact hs)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨v, hv0, fun k => congrFun (LinearMap.mem_ker.1 hv) k⟩

theorem exists_uForm_single_ne_zero {w : Fin n → F} (hw : w ≠ 0) :
    ∃ i : Fin n, uForm σ w (Pi.single (Fin.rev i) 1) ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hw
  refine ⟨i, ?_⟩
  rw [uForm_single_right, Fin.rev_rev, map_ne_zero]
  simpa using hi

end Linear

section Projection

variable {F : Type*} [Field F] {σ : F ≃+* F} {n m : ℕ}

variable (σ) in
@[expose] def hypProj (P Q : Fin m → Fin n → F) (y : Fin n → F) : Fin n → F :=
  y - ∑ k, (uForm σ (Q k) y • P k + uForm σ (P k) y • Q k)

theorem uForm_hypProj_P {P Q : Fin m → Fin n → F} (hPP : ∀ i j, uForm σ (P i) (P j) = 0)
    (hPQ : ∀ i j, uForm σ (P i) (Q j) = if i = j then 1 else 0) (y : Fin n → F) (j : Fin m) :
    uForm σ (P j) (hypProj σ P Q y) = 0 := by
  simp [hypProj, uForm_sub_right, uForm_sum_right, uForm_add_right, uForm_smul_right, hPP, hPQ]

theorem uForm_hypProj_Q (hσ : ∀ c, σ (σ c) = c) {P Q : Fin m → Fin n → F}
    (hQQ : ∀ i j, uForm σ (Q i) (Q j) = 0)
    (hPQ : ∀ i j, uForm σ (P i) (Q j) = if i = j then 1 else 0) (y : Fin n → F) (j : Fin m) :
    uForm σ (Q j) (hypProj σ P Q y) = 0 := by
  have hQP : ∀ i j, uForm σ (Q i) (P j) = if j = i then 1 else 0 := fun i j => by
    rw [← uForm_conj σ hσ, hPQ]
    split_ifs <;> simp
  simp [hypProj, uForm_sub_right, uForm_sum_right, uForm_add_right, uForm_smul_right, hQQ, hQP]

theorem uForm_hypProj_of_perp {P Q : Fin m → Fin n → F} {x : Fin n → F}
    (hxP : ∀ k, uForm σ x (P k) = 0) (hxQ : ∀ k, uForm σ x (Q k) = 0) (y : Fin n → F) :
    uForm σ x (hypProj σ P Q y) = uForm σ x y := by
  simp [hypProj, uForm_sub_right, uForm_sum_right, uForm_add_right, uForm_smul_right, hxP, hxQ]

end Projection

section Complete

variable {F : Type*} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c)
  (hnorm : ∀ d, σ d = d → ∃ l, σ l * l = d) (htr : ∀ a, σ a = a → ∃ c, c + σ c = a)
  {n m : ℕ} {P Q : Fin m → Fin n → F}
  (hPP : ∀ i j, uForm σ (P i) (P j) = 0) (hQQ : ∀ i j, uForm σ (Q i) (Q j) = 0)
  (hPQ : ∀ i j, uForm σ (P i) (Q j) = if i = j then 1 else 0)
include hσ hPP hQQ hPQ

omit hPP hQQ hPQ in
include hnorm in
theorem exists_isotropic_perp (hmn : 2 * m + 1 < n) :
    ∃ w : Fin n → F, w ≠ 0 ∧ uForm σ w w = 0 ∧ (∀ k, uForm σ (P k) w = 0) ∧
      ∀ k, uForm σ (Q k) w = 0 := by
  obtain ⟨x, hx0, hx⟩ := exists_ne_zero_forall_uForm_eq_zero σ (Sum.elim P Q)
    (by rw [Fintype.card_sum, Fintype.card_fin]; omega)
  have hPx : ∀ k, uForm σ (P k) x = 0 := fun k => hx (Sum.inl k)
  have hQx : ∀ k, uForm σ (Q k) x = 0 := fun k => hx (Sum.inr k)
  by_cases hxx : uForm σ x x = 0
  · exact ⟨x, hx0, hxx, hPx, hQx⟩
  obtain ⟨y, hy0, hy⟩ := exists_ne_zero_forall_uForm_eq_zero σ
    (fun o : Option (Fin m ⊕ Fin m) => o.elim x (Sum.elim P Q))
    (by rw [Fintype.card_option, Fintype.card_sum, Fintype.card_fin]; omega)
  have hxy : uForm σ x y = 0 := hy none
  have hyx : uForm σ y x = 0 := uForm_eq_zero_comm hσ hxy
  have hPy : ∀ k, uForm σ (P k) y = 0 := fun k => hy (some (Sum.inl k))
  have hQy : ∀ k, uForm σ (Q k) y = 0 := fun k => hy (some (Sum.inr k))
  by_cases hyy : uForm σ y y = 0
  · exact ⟨y, hy0, hyy, hPy, hQy⟩
  obtain ⟨t, ht⟩ := hnorm (-uForm σ x x / uForm σ y y) (by
    rw [map_div₀, map_neg, uForm_conj σ hσ, uForm_conj σ hσ])
  have ht' : σ t * t * uForm σ y y = -uForm σ x x := by rw [ht, div_mul_cancel₀ _ hyy]
  refine ⟨x + t • y, fun h0 => hxx ?_, ?_, fun k => ?_, fun k => ?_⟩
  · have := congrArg (uForm σ x) h0
    rwa [uForm_add_right, uForm_smul_right, hxy, mul_zero, add_zero, uForm_zero_right] at this
  · simp only [uForm_add_left, uForm_add_right, uForm_smul_left, uForm_smul_right, hxy, hyx]
    linear_combination ht'
  · rw [uForm_add_right, uForm_smul_right, hPx, hPy, mul_zero, add_zero]
  · rw [uForm_add_right, uForm_smul_right, hQx, hQy, mul_zero, add_zero]

include hnorm htr in
theorem exists_hyperbolic_pair_perp (hmn : 2 * m + 1 < n) :
    ∃ w z : Fin n → F, uForm σ w w = 0 ∧ uForm σ z z = 0 ∧ uForm σ w z = 1 ∧
      ∀ k, uForm σ (P k) w = 0 ∧ uForm σ (Q k) w = 0 ∧ uForm σ (P k) z = 0 ∧
        uForm σ (Q k) z = 0 := by
  obtain ⟨w, hw0, hww, hPw, hQw⟩ := exists_isotropic_perp hσ hnorm (P := P) (Q := Q) hmn
  obtain ⟨i, hi⟩ := exists_uForm_single_ne_zero (σ := σ) hw0
  have hwy := uForm_hypProj_of_perp (P := P) (Q := Q) (fun k => uForm_eq_zero_comm hσ (hPw k))
    (fun k => uForm_eq_zero_comm hσ (hQw k)) (Pi.single (Fin.rev i) 1)
  set y := hypProj σ P Q (Pi.single (Fin.rev i) 1) with hydef
  have hPy : ∀ k, uForm σ (P k) y = 0 := fun k => uForm_hypProj_P hPP hPQ _ k
  have hQy : ∀ k, uForm σ (Q k) y = 0 := fun k => uForm_hypProj_Q hσ hQQ hPQ _ k
  have he : uForm σ w y ≠ 0 := by rw [hwy]; exact hi
  have hwz : uForm σ w ((uForm σ w y)⁻¹ • y) = 1 := by
    rw [uForm_smul_right, inv_mul_cancel₀ he]
  have hzw : uForm σ ((uForm σ w y)⁻¹ • y) w = 1 := by
    rw [← uForm_conj σ hσ, hwz, map_one]
  obtain ⟨c, hc⟩ := htr (-uForm σ ((uForm σ w y)⁻¹ • y) ((uForm σ w y)⁻¹ • y)) (by
    rw [map_neg, uForm_conj σ hσ])
  refine ⟨w, (uForm σ w y)⁻¹ • y + c • w, hww, ?_, ?_, fun k => ⟨hPw k, hQw k, ?_, ?_⟩⟩
  · simp only [uForm_add_left, uForm_add_right, uForm_smul_left _ c w, uForm_smul_right _ c,
      hww, hzw, hwz]
    linear_combination hc
  · rw [uForm_add_right, hwz, uForm_smul_right, hww, mul_zero, add_zero]
  · rw [uForm_add_right, uForm_smul_right, uForm_smul_right, hPy, hPw, mul_zero, mul_zero,
      add_zero]
  · rw [uForm_add_right, uForm_smul_right, uForm_smul_right, hQy, hQw, mul_zero, mul_zero,
      add_zero]

include hnorm htr in
theorem exists_uForm_self_eq_one_perp (hmn : 2 * m < n) :
    ∃ u : Fin n → F, uForm σ u u = 1 ∧ ∀ k, uForm σ (P k) u = 0 ∧ uForm σ (Q k) u = 0 := by
  obtain ⟨u, hu, hPu, hQu⟩ : ∃ u : Fin n → F, uForm σ u u ≠ 0 ∧ (∀ k, uForm σ (P k) u = 0) ∧
      ∀ k, uForm σ (Q k) u = 0 := by
    obtain ⟨x, hx0, hx⟩ := exists_ne_zero_forall_uForm_eq_zero σ (Sum.elim P Q)
      (by rw [Fintype.card_sum, Fintype.card_fin]; omega)
    have hPx : ∀ k, uForm σ (P k) x = 0 := fun k => hx (Sum.inl k)
    have hQx : ∀ k, uForm σ (Q k) x = 0 := fun k => hx (Sum.inr k)
    by_cases hxx : uForm σ x x = 0
    swap
    · exact ⟨x, hxx, hPx, hQx⟩
    obtain ⟨i, hi⟩ := exists_uForm_single_ne_zero (σ := σ) hx0
    have hxy := uForm_hypProj_of_perp (P := P) (Q := Q) (fun k => uForm_eq_zero_comm hσ (hPx k))
      (fun k => uForm_eq_zero_comm hσ (hQx k)) (Pi.single (Fin.rev i) 1)
    set y := hypProj σ P Q (Pi.single (Fin.rev i) 1) with hydef
    have hPy : ∀ k, uForm σ (P k) y = 0 := fun k => uForm_hypProj_P hPP hPQ _ k
    have hQy : ∀ k, uForm σ (Q k) y = 0 := fun k => uForm_hypProj_Q hσ hQQ hPQ _ k
    have he : uForm σ x y ≠ 0 := by rw [hxy]; exact hi
    by_cases hyy : uForm σ y y = 0
    swap
    · exact ⟨y, hyy, hPy, hQy⟩
    obtain ⟨s, hs⟩ := htr 1 (map_one σ)
    have hyx : uForm σ y x = σ (uForm σ x y) := (uForm_conj σ hσ x y).symm
    have ht : s / uForm σ x y * uForm σ x y = s := div_mul_cancel₀ s he
    have ht' : σ (s / uForm σ x y) * σ (uForm σ x y) = σ s := by rw [← map_mul, ht]
    refine ⟨x + (s / uForm σ x y) • y, ?_, fun k => ?_, fun k => ?_⟩
    · simp only [uForm_add_left, uForm_add_right, uForm_smul_left, uForm_smul_right, hxx, hyy,
        hyx]
      intro h0
      have h1 : s + σ s = 0 := by linear_combination h0 - ht - ht'
      rw [hs] at h1
      exact one_ne_zero h1
    · rw [uForm_add_right, uForm_smul_right, hPx, hPy, mul_zero, add_zero]
    · rw [uForm_add_right, uForm_smul_right, hQx, hQy, mul_zero, add_zero]
  obtain ⟨l, hl⟩ := hnorm (uForm σ u u)⁻¹ (by rw [map_inv₀, uForm_conj σ hσ])
  refine ⟨l • u, ?_, fun k => ⟨?_, ?_⟩⟩
  · rw [uForm_smul_left, uForm_smul_right, ← mul_assoc, hl, inv_mul_cancel₀ hu]
  · rw [uForm_smul_right, hPu, mul_zero]
  · rw [uForm_smul_right, hQu, mul_zero]

end Complete

section Finite

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [hp : Fact p.Prime] [CharP F p]

omit hp [CharP F p] in
theorem two_le_pow_of_card (hF : Nat.card F = (p ^ f) ^ 2) : 2 ≤ p ^ f := by
  have h1 : 1 < Nat.card F := Finite.one_lt_card
  rw [hF] at h1
  by_contra h
  have h2 : p ^ f ≤ 1 := by omega
  have h3 : (p ^ f) ^ 2 ≤ 1 := by
    calc (p ^ f) ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left h2 2
      _ = 1 := one_pow 2
  omega

theorem exists_sigma_mul_self_eq (hF : Nat.card F = (p ^ f) ^ 2) {d : F}
    (hd : unitaryInvolution F p f d = d) : ∃ l : F, unitaryInvolution F p f l * l = d := by
  classical
  rcases eq_or_ne d 0 with rfl | hd0
  · exact ⟨0, by simp⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf g = Nat.card Fˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  have hcard : Nat.card Fˣ = (p ^ f) ^ 2 - 1 := by
    have : Fintype F := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hF]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg (Units.mk0 d hd0))
  have hq2 := two_le_pow_of_card hF
  set q := p ^ f with hq
  have hσ : ∀ x : F, unitaryInvolution F p f x = x ^ q := fun x => unitaryInvolution_apply F p f x
  have hdq : (Units.mk0 d hd0) ^ (q - 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    have h1 : d ^ (q - 1) * d = 1 * d := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ q), ← hσ, hd, one_mul]
    exact mul_right_cancel₀ hd0 h1
  rw [← hk, ← _root_.zpow_natCast, ← _root_.zpow_mul, ← orderOf_dvd_iff_zpow_eq_one, hord,
    hcard] at hdq
  have hdvd : ((q + 1 : ℕ) : ℤ) ∣ k := by
    have h2 : ((q ^ 2 - 1 : ℕ) : ℤ) = ((q + 1 : ℕ) : ℤ) * ((q - 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub (Nat.one_le_pow 2 q (by omega)), Nat.cast_sub (by omega : 1 ≤ q)]
      ring
    rw [h2] at hdq
    exact Int.dvd_of_mul_dvd_mul_right (by omega) hdq
  obtain ⟨m, hm⟩ := hdvd
  refine ⟨((g ^ m : Fˣ) : F), ?_⟩
  rw [hσ, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← pow_succ, ← _root_.zpow_natCast,
    ← _root_.zpow_mul, show m * ((q + 1 : ℕ) : ℤ) = k by rw [hm]; ring, hk, Units.val_mk0]

@[expose] noncomputable def wittScale (σ : F ≃+* F) {n : ℕ} [NeZero n] (l : F) (a : Fin n) : F :=
  (if a = 0 then l else 1) * (if a = Fin.rev 0 then (σ l)⁻¹ else 1)

theorem exists_su_mulVec_of_gram (hF : Nat.card F = (p ^ f) ^ 2) {n : ℕ} [NeZero n]
    (h0 : (0 : Fin n) ≠ Fin.rev 0) {col : Fin n → Fin n → F}
    (hgram : ∀ a b, uForm (unitaryInvolution F p f) (col a) (col b) =
      if b = Fin.rev a then 1 else 0) :
    ∃ (g : SU (unitaryInvolution F p f) n) (l : F), l ≠ 0 ∧ ∀ a,
      suMat _ n g *ᵥ Pi.single a 1 = wittScale (unitaryInvolution F p f) l a • col a := by
  set σ := unitaryInvolution F p f with hσdef
  have hσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hF
  set C : Matrix (Fin n) (Fin n) F := Matrix.of fun x a => col a x with hC
  have hgramC : conjTr σ C * antidiag n * C = antidiag n := by
    ext a b
    rw [conjTr_mul_antidiag_mul_apply, antidiag, Matrix.of_apply]
    exact hgram a b
  have hdetJ : (antidiag n : Matrix (Fin n) (Fin n) F).det ≠ 0 := by
    have := congrArg Matrix.det (antidiag_mul_antidiag (F := F) (n := n))
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact left_ne_zero_of_mul_eq_one this
  have hnorm : σ C.det * C.det = 1 := by
    have h := congrArg Matrix.det hgramC
    have e : (C.map σ).det = σ C.det := (RingEquiv.map_det σ C).symm
    rw [Matrix.det_mul, Matrix.det_mul, conjTr, Matrix.det_transpose, e] at h
    have h' : σ C.det * C.det * (antidiag n : Matrix (Fin n) (Fin n) F).det =
        1 * (antidiag n : Matrix (Fin n) (Fin n) F).det := by
      linear_combination h
    exact mul_right_cancel₀ hdetJ h'
  have hC0 : C.det ≠ 0 := right_ne_zero_of_mul_eq_one hnorm
  have hd : σ C.det⁻¹ * C.det⁻¹ = 1 := by
    rw [map_inv₀, ← mul_inv, hnorm, inv_one]
  obtain ⟨l, hl0, hl⟩ := exists_mul_inv_sigma_eq hF hd
  rw [← hσdef] at hl
  have hσl : σ l ≠ 0 := (map_ne_zero σ).2 hl0
  have hr0 : Fin.rev (0 : Fin n) ≠ 0 := Ne.symm h0
  have hrev : ∀ a : Fin n, Fin.rev a = 0 ↔ a = Fin.rev 0 := fun a => by
    constructor
    · intro h; rw [← h, Fin.rev_rev]
    · intro h; rw [h, Fin.rev_rev]
  have hrev' : ∀ a : Fin n, Fin.rev a = Fin.rev 0 ↔ a = 0 := fun a =>
    ⟨fun h => Fin.rev_injective h, fun h => by rw [h]⟩
  set D : Matrix (Fin n) (Fin n) F := Matrix.diagonal (wittScale σ l) with hD
  have hgramD : conjTr σ D * antidiag n * D = antidiag n := by
    ext a b
    rw [hD, conjTr, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose,
      Matrix.mul_diagonal, Matrix.diagonal_mul, antidiag, Matrix.of_apply]
    by_cases hb : b = Fin.rev a
    · subst hb
      rw [ite_eq_left rfl, mul_one]
      by_cases ha : a = 0
      · subst ha
        simp [wittScale, h0, hr0, hσl]
      · by_cases ha' : a = Fin.rev 0
        · subst ha'
          simp [wittScale, h0, hr0, Fin.rev_rev, hσ, hl0]
        · simp [wittScale, ha, ha', (hrev a).not.2 ha', (hrev' a).not.2 ha]
    · simp [hb]
  have hdetD : D.det = l * (σ l)⁻¹ := by
    rw [hD, Matrix.det_diagonal]
    simp only [wittScale, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ,
      ite_true]
  set C' := C * D with hC'
  have hgram' : conjTr σ C' * antidiag n * C' = antidiag n := by
    rw [hC', conjTr_mul, show conjTr σ D * conjTr σ C * antidiag n * (C * D) =
        conjTr σ D * (conjTr σ C * antidiag n * C) * D by simp only [Matrix.mul_assoc], hgramC,
      hgramD]
  have hdet' : C'.det = 1 := by
    rw [hC', Matrix.det_mul, hdetD, hl, mul_inv_cancel₀ hC0]
  let g0 : GL (Fin n) F :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero C' (by rw [hdet']; exact one_ne_zero)
  have hg0 : g0 ∈ SU σ n := mem_SU.2 ⟨hdet', hgram'⟩
  refine ⟨⟨g0, hg0⟩, l, hl0, fun a => ?_⟩
  change C' *ᵥ Pi.single a 1 = _
  rw [hC', ← mulVec_mulVec, hD, diagonal_mulVec_single, mulVec_smul]
  congr 1
  funext x
  simp [hC, mulVec, dotProduct, Pi.single_apply]

end Finite

section Heisenberg

variable {F : Type*} [Field F] (σ : F ≃+* F) (hσ : ∀ c, σ (σ c) = c) {n : ℕ}

@[expose] noncomputable def heisElt {i k : Fin n} (hi : i ≠ Fin.rev i) (hik : i ≠ k)
    (hk : Fin.rev k = k) {a b : F} (hab : b + σ b + σ a * a = 0) : SU σ n :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (heisenbergMatrix σ i k a b)
      (by rw [det_heisenbergMatrix σ hi hik hk]; exact one_ne_zero),
    mem_SU.2 ⟨det_heisenbergMatrix σ hi hik hk a b, heisenbergMatrix_isometry σ hσ hi hik hk hab⟩⟩

theorem suMat_heisElt {i k : Fin n} (hi : i ≠ Fin.rev i) (hik : i ≠ k) (hk : Fin.rev k = k)
    {a b : F} (hab : b + σ b + σ a * a = 0) :
    suMat σ n (heisElt σ hσ hi hik hk hab) = heisenbergMatrix σ i k a b :=
  rfl

theorem heisenbergMatrix_mulVec_single_rev {i k : Fin n} (hik : i ≠ k) (hk : Fin.rev k = k)
    (a b : F) :
    heisenbergMatrix σ i k a b *ᵥ Pi.single (Fin.rev i) 1 =
      Pi.single (Fin.rev i) 1 - σ a • Pi.single k 1 + b • Pi.single i 1 := by
  have hk' : k ≠ Fin.rev i := fun h => hik (by rw [← Fin.rev_rev i, ← h, hk])
  funext x
  simp only [heisenbergMatrix, add_mulVec, sub_mulVec, one_mulVec, single_mulVec, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Function.update_apply, Pi.zero_apply,
    Pi.single_apply, ite_eq_right hk', mul_zero]
  split_ifs <;> simp

end Heisenberg

end CFSG.Timmesfeld.LieEmbed
