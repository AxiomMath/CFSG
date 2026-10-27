module

public import CFSG.RankThree.PartTwo.KFacts.KS116ProofTools

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS116Proof

open Matrix
open scoped MatrixGroups

section Elements

variable {K : Type} [Field K]

@[expose] def uu (b : K) : SL(2, K) := ⟨!![1, b; 0, 1], by simp [det_fin_two_of]⟩

@[expose] def ll (b : K) : SL(2, K) := ⟨!![1, 0; b, 1], by simp [det_fin_two_of]⟩

@[expose] def hh (x : Kˣ) : SL(2, K) := ⟨!![(x : K), 0; 0, ((x⁻¹ : Kˣ) : K)], by simp⟩

theorem coe_uu (b : K) : (uu b : Matrix (Fin 2) (Fin 2) K) = !![1, b; 0, 1] := rfl

theorem coe_ll (b : K) : (ll b : Matrix (Fin 2) (Fin 2) K) = !![1, 0; b, 1] := rfl

theorem coe_hh (x : Kˣ) :
    (hh x : Matrix (Fin 2) (Fin 2) K) = !![(x : K), 0; 0, ((x⁻¹ : Kˣ) : K)] :=
  rfl

theorem uu_add (a b : K) : uu (a + b) = uu a * uu b := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_uu, coe_uu, coe_uu, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [add_comm]

theorem uu_zero : uu (0 : K) = 1 := by
  apply Subtype.ext
  rw [coe_uu, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem uu_injective : Function.Injective (uu : K → SL(2, K)) := by
  intro a b h
  have := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 1) h
  simpa [coe_uu] using this

theorem uu_mul_comm (a b : K) : uu a * uu b = uu b * uu a := by
  rw [← uu_add, ← uu_add, add_comm]

theorem map_uu {L : Type} [Field L] (β : K →+* L) (b : K) :
    Matrix.SpecialLinearGroup.map β (uu b) = uu (β b) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, coe_uu, coe_uu]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem map_ll {L : Type} [Field L] (β : K →+* L) (b : K) :
    Matrix.SpecialLinearGroup.map β (ll b) = ll (β b) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, coe_ll, coe_ll]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem eq_uu_mul_ll_mul_uu (A : SL(2, K)) (hc : A 1 0 ≠ 0) :
    A = uu ((A 0 0 - 1) / A 1 0) * ll (A 1 0) * uu ((A 1 1 - 1) / A 1 0) := by
  have hd : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by rw [← det_fin_two]; exact A.2
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_uu, coe_ll,
    coe_uu, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> first | ring1 | linear_combination -hd

theorem closure_uu_ll :
    Subgroup.closure (Set.range (uu : K → SL(2, K)) ∪ Set.range (ll : K → SL(2, K))) = ⊤ := by
  rw [eq_top_iff]
  intro A _
  set S := Subgroup.closure (Set.range (uu : K → SL(2, K)) ∪ Set.range (ll : K → SL(2, K)))
  have hu : ∀ b : K, uu b ∈ S := fun b => Subgroup.subset_closure (Or.inl ⟨b, rfl⟩)
  have hl : ∀ b : K, ll b ∈ S := fun b => Subgroup.subset_closure (Or.inr ⟨b, rfl⟩)
  have key : ∀ B : SL(2, K), B 1 0 ≠ 0 → B ∈ S := fun B hB => by
    rw [eq_uu_mul_ll_mul_uu B hB]
    exact S.mul_mem (S.mul_mem (hu _) (hl _)) (hu _)
  by_cases hc : A 1 0 = 0
  · have ha : A 0 0 ≠ 0 := by
      intro ha
      have hd : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by rw [← det_fin_two]; exact A.2
      rw [ha, hc] at hd
      simp at hd
    have h1 : (ll (1 : K) * A : SL(2, K)) 1 0 ≠ 0 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, coe_ll, coe_eta A, Matrix.mul_fin_two]
      simpa [hc] using ha
    have h2 := S.mul_mem (S.inv_mem (hl 1)) (key _ h1)
    rwa [inv_mul_cancel_left] at h2
  · exact key A hc

variable [CharP K 2]

@[expose] def ww : SL(2, K) :=
  ⟨!![0, 1; 1, 0], by rw [det_fin_two_of]; simp [CharTwo.neg_eq]⟩

theorem coe_ww : ((ww : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0] := rfl

theorem ww_conj_uu (b : K) : ww * uu b * ww⁻¹ = ll b := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_inv_sl, coe_ww,
    coe_uu, coe_ll, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem ww_conj_hh (x : Kˣ) : ww * hh x * ww⁻¹ = (hh x)⁻¹ := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_inv_sl, coe_inv_sl,
    coe_ww, coe_hh, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem hh_conj_uu (x : Kˣ) (b : K) : hh x * uu b * (hh x)⁻¹ = uu ((x : K) ^ 2 * b) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_inv_sl, coe_hh,
    coe_uu, coe_uu, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  ring

theorem eq_one_of_pow_three {c : K} (h : (uu (1 : K) * ll c) ^ 3 = 1) : c = 1 := by
  have h01 := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 1) h
  simp only [pow_succ, pow_zero, one_mul, Matrix.SpecialLinearGroup.coe_mul, coe_uu, coe_ll,
    Matrix.SpecialLinearGroup.coe_one, Matrix.mul_fin_two] at h01
  simp at h01
  have h2 : c ^ 2 = 1 := by
    linear_combination (norm := ring_nf) h01
    simp [ofNat_eq_mod_two]
  exact eq_one_of_sq_eq_one h2

theorem uu_one_mul_ll_one_pow_three : (uu (1 : K) * ll 1) ^ 3 = 1 := by
  apply Subtype.ext
  simp only [pow_succ, pow_zero, one_mul, Matrix.SpecialLinearGroup.coe_mul, coe_uu, coe_ll,
    Matrix.SpecialLinearGroup.coe_one, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring_nf <;> simp [ofNat_eq_mod_two]

end Elements

section Lemmas

variable {F : Type} [Field F] [CharP F 2]

theorem eq_uu_of_commute {M : SL(2, F)} (h : M * uu 1 = uu 1 * M) : M = uu (M 0 1) := by
  have h' := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F)) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uu] at h'
  rw [coe_eta M, Matrix.mul_fin_two, Matrix.mul_fin_two] at h'
  have h00 := congrFun (congrFun h' 0) 0
  have h01 := congrFun (congrFun h' 0) 1
  simp at h00 h01
  have hd := det_entries M
  rw [h00, mul_zero, add_zero] at hd
  have hps : M 0 0 = M 1 1 := by linear_combination h01
  rw [← hps, ← pow_two] at hd
  have h1 := eq_one_of_sq_eq_one hd
  apply Subtype.ext
  rw [coe_uu, coe_eta M]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h1, h00, ← hps]

theorem lowerLeft_eq_zero_of_conj {M : SL(2, F)} {c c' : F} (hc : c ≠ 0)
    (h : M * uu c * M⁻¹ = uu c') : M 1 0 = 0 := by
  have h' := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F)) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_inv_sl, coe_uu] at h'
  rw [coe_eta M, Matrix.mul_fin_two, Matrix.mul_fin_two] at h'
  have h10 := congrFun (congrFun h' 1) 0
  simp at h10
  have h2 : M 1 0 ^ 2 * c = 0 := by
    linear_combination (norm := ring_nf) h10
    simp [ofNat_eq_mod_two]
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ((mul_eq_zero.mp h2).resolve_right hc)

theorem conj_uu_of_lowerLeft {M : SL(2, F)} (hM : M 1 0 = 0) (c : F) :
    M * uu c * M⁻¹ = uu (M 0 0 ^ 2 * c) := by
  have hd := det_entries M
  rw [hM, mul_zero, add_zero] at hd
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_inv_sl, coe_uu,
    coe_uu, coe_eta M, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> (try simp [hM]) <;>
    first
    | ring1
    | linear_combination hd
    | (ring_nf; simp [ofNat_eq_mod_two])

theorem lowerLeft_uu_conj {M : SL(2, F)} (hM : M 1 0 = 0) (z : F) :
    (uu z * M * (uu z)⁻¹ : SL(2, F)) 1 0 = 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_inv_sl, coe_uu,
    coe_eta M, Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp [hM]

theorem upperLeft_uu_conj {M : SL(2, F)} (hM : M 1 0 = 0) (z : F) :
    (uu z * M * (uu z)⁻¹ : SL(2, F)) 0 0 = M 0 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_inv_sl, coe_uu,
    coe_eta M, Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp [hM]

theorem exists_conj_uu_diag {M : SL(2, F)} (hM : M 1 0 = 0) (hx : M 0 0 ^ 2 ≠ 1) :
    ∃ z : F, (uu z * M * (uu z)⁻¹ : SL(2, F)) 0 1 = 0 := by
  have hd := det_entries M
  rw [hM, mul_zero, add_zero] at hd
  have hs : M 0 0 + M 1 1 ≠ 0 := by
    intro hs
    apply hx
    have : M 1 1 = M 0 0 := by
      linear_combination (norm := ring_nf) hs
      simp [ofNat_eq_mod_two]
    rw [this] at hd
    rw [pow_two]
    exact hd
  refine ⟨M 0 1 / (M 0 0 + M 1 1), ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_inv_sl, coe_uu,
    coe_eta M, Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp [hM]
  field_simp
  ring_nf
  simp [ofNat_eq_mod_two]

theorem diag_eq_zero_of_conj {W D : SL(2, F)} (h01 : D 0 1 = 0) (h10 : D 1 0 = 0)
    (hx : D 0 0 ^ 2 ≠ 1) (h : W * D * W⁻¹ = D⁻¹) : W 0 0 = 0 ∧ W 1 1 = 0 := by
  have hd := det_entries D
  rw [h01, zero_mul, add_zero] at hd
  have hne : D 0 0 - D 1 1 ≠ 0 := by
    intro hs
    apply hx
    rw [pow_two]
    have : D 1 1 = D 0 0 := by linear_combination -hs
    rw [this] at hd
    exact hd
  have h' : W * D = D⁻¹ * W := by rw [← h]; group
  have h'' := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F)) h'
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_inv_sl] at h''
  rw [coe_eta W, coe_eta D, Matrix.mul_fin_two, Matrix.mul_fin_two] at h''
  have e00 := congrFun (congrFun h'' 0) 0
  have e11 := congrFun (congrFun h'' 1) 1
  simp [h01, h10] at e00 e11
  constructor
  · have : W 0 0 * (D 0 0 - D 1 1) = 0 := by linear_combination e00
    exact (mul_eq_zero.mp this).resolve_right hne
  · have : W 1 1 * (D 0 0 - D 1 1) = 0 := by linear_combination -e11
    exact (mul_eq_zero.mp this).resolve_right hne

theorem antidiag_conj_uu_one {W : SL(2, F)} (h00 : W 0 0 = 0) (h11 : W 1 1 = 0) :
    W * uu 1 * W⁻¹ = ll (W 1 0 ^ 2) := by
  have hd := det_entries W
  rw [h00, zero_mul, zero_add] at hd
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_inv_sl, coe_uu,
    coe_ll, coe_eta W, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h11] <;>
    first
    | ring1
    | linear_combination hd

theorem eq_ww_of_antidiag {W : SL(2, F)} (h00 : W 0 0 = 0) (h11 : W 1 1 = 0) (h10 : W 1 0 = 1) :
    W = ww := by
  have hd := det_entries W
  rw [h00, zero_mul, zero_add, h10, mul_one] at hd
  apply Subtype.ext
  rw [coe_ww, coe_eta W]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h11, h10, hd]

theorem exists_conj_eq_uu_one [Finite F] {X : SL(2, F)} (hX2 : X * X = 1) (hX1 : X ≠ 1) :
    ∃ P : SL(2, F), X = P * uu 1 * P⁻¹ := by
  have hF2 : ringChar F = 2 := ringChar.eq F 2
  have hd := det_entries X
  have htr : X 0 0 + X 1 1 = 0 := by
    by_contra htr
    have hsq := mul_self_eq X
    have h1 : ((X * X : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [hX2, Matrix.SpecialLinearGroup.coe_one]
    rw [Matrix.SpecialLinearGroup.coe_mul, hsq] at h1
    have h2 : (X 0 0 + X 1 1) • (X : Matrix (Fin 2) (Fin 2) F) = 0 := by
      have := congrArg (· + (1 : Matrix (Fin 2) (Fin 2) F)) h1
      simpa [add_assoc, matrix_add_self] using this
    have h3 := congrArg (fun A : Matrix (Fin 2) (Fin 2) F => A 0 0 * A 1 1 + A 0 1 * A 1 0) h2
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, mul_zero, add_zero] at h3
    have h4 : (X 0 0 + X 1 1) ^ 2 * (X 0 0 * X 1 1 + X 0 1 * X 1 0) = 0 := by
      linear_combination h3
    rw [hd, mul_one] at h4
    exact htr (pow_eq_zero_iff (by norm_num) |>.mp h4)
  have hs : X 1 1 = X 0 0 := by
    linear_combination (norm := ring_nf) htr
    simp [ofNat_eq_mod_two]
  rw [hs] at hd
  by_cases hr : X 1 0 = 0
  ·
    rw [hr, mul_zero, add_zero, ← pow_two] at hd
    have hp := eq_one_of_sq_eq_one hd
    have hq : X 0 1 ≠ 0 := by
      intro hq
      apply hX1
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_one, coe_eta X]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hp, hq, hr, hs]
    obtain ⟨b, hb⟩ := FiniteField.isSquare_of_char_two hF2 (X 0 1)⁻¹
    have hb2 : X 0 1 * (b * b) = 1 := by rw [← hb]; field_simp
    set P : SL(2, F) := ⟨!![X 0 1 * b, 0; 0, b], by
      rw [det_fin_two_of]; linear_combination hb2⟩ with hP
    have hPc : (P : Matrix (Fin 2) (Fin 2) F) = !![X 0 1 * b, 0; 0, b] := rfl
    refine ⟨P, ?_⟩
    rw [eq_mul_inv_iff_mul_eq]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_uu, coe_eta X,
      hPc, Matrix.mul_fin_two, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hp, hr, hs]
  · obtain ⟨a, ha⟩ := FiniteField.isSquare_of_char_two hF2 (X 1 0)⁻¹
    have ha2 : X 1 0 * (a * a) = 1 := by rw [← ha]; field_simp
    set P : SL(2, F) := ⟨!![(X 0 0 + 1) * a, a; X 1 0 * a, 0], by
      rw [det_fin_two_of]
      linear_combination (norm := ring_nf) -ha2
      simp [ofNat_eq_mod_two]⟩ with hP
    have hPc : (P : Matrix (Fin 2) (Fin 2) F) = !![(X 0 0 + 1) * a, a; X 1 0 * a, 0] := rfl
    refine ⟨P, ?_⟩
    rw [eq_mul_inv_iff_mul_eq]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_uu, coe_eta X,
      hPc, Matrix.mul_fin_two, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> (try simp [hs]) <;>
      first
      | ring1
      | linear_combination a * hd
      | (ring_nf; simp [ofNat_eq_mod_two])

end Lemmas

section Main

variable {F : Type} [Field F] [Finite F] [CharP F 2]
variable {K₀ : Type} [Field K₀] [Finite K₀] [CharP K₀ 2]

omit [Finite F] in
theorem exists_conj_eq_map_of_uu_one (hK₀ : 4 ≤ Nat.card K₀) (ι : SL(2, K₀) →* SL(2, F))
    (h1 : ι (uu 1) = uu 1) :
    ∃ (β : K₀ →+* F) (c : SL(2, F)),
      ∀ A, ι A = c * Matrix.SpecialLinearGroup.map β A * c⁻¹ := by
  set α : K₀ → F := fun b => (ι (uu b) : SL(2, F)) 0 1 with hα
  have hαu : ∀ b, ι (uu b) = uu (α b) := by
    intro b
    apply eq_uu_of_commute
    rw [← h1, ← map_mul, ← map_mul, uu_mul_comm]
  have hα_add : ∀ a b, α (a + b) = α a + α b := by
    intro a b
    apply uu_injective
    rw [← hαu, uu_add, map_mul, hαu, hαu, uu_add]
  have hα1 : α 1 = 1 := by
    apply uu_injective
    rw [← hαu, h1]
  have hα0 : α 0 = 0 := by
    apply uu_injective
    rw [← hαu, uu_zero, map_one, uu_zero]
  have hhx : ∀ x : K₀ˣ, (ι (hh x) : SL(2, F)) 1 0 = 0 := by
    intro x
    apply lowerLeft_eq_zero_of_conj (c := 1) (c' := α ((x : K₀) ^ 2 * 1)) one_ne_zero
    rw [← h1, ← map_inv, ← map_mul, ← map_mul, hh_conj_uu, hαu]
  have key : ∀ (x : K₀ˣ) (b : K₀),
      α ((x : K₀) ^ 2 * b) = (ι (hh x) : SL(2, F)) 0 0 ^ 2 * α b := by
    intro x b
    apply uu_injective
    rw [← conj_uu_of_lowerLeft (hhx x), ← hαu, ← hαu, ← map_inv, ← map_mul, ← map_mul,
      hh_conj_uu]
  have key1 : ∀ x : K₀ˣ, α ((x : K₀) ^ 2) = (ι (hh x) : SL(2, F)) 0 0 ^ 2 := by
    intro x
    have h := key x 1
    rwa [mul_one, hα1, mul_one] at h
  have hα_mul : ∀ a b, α (a * b) = α a * α b := by
    intro a b
    by_cases ha : a = 0
    · rw [ha, zero_mul, hα0, zero_mul]
    · obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K₀ 2) a
      have hr0 : r ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hr
        exact ha hr
      have h := key (Units.mk0 r hr0) b
      rw [Units.val_mk0, ← key1 (Units.mk0 r hr0), Units.val_mk0] at h
      rw [hr, ← pow_two]
      exact h
  let β : K₀ →+* F :=
    { toFun := α
      map_one' := hα1
      map_mul' := hα_mul
      map_zero' := hα0
      map_add' := hα_add }
  have hβ : ∀ b, β b = α b := fun b => rfl
  obtain ⟨x₀, hx₀⟩ : ∃ x : K₀ˣ, (x : K₀) ≠ 1 := by
    by_contra h
    push Not at h
    have hsub : Subsingleton K₀ˣ := ⟨fun a b => Units.ext ((h a).trans (h b).symm)⟩
    have hcard := Nat.card_unique (α := K₀ˣ)
    rw [Nat.card_units] at hcard
    omega
  set N₀ := ι (hh x₀) with hN₀def
  have hN₀ : N₀ 1 0 = 0 := hhx x₀
  have hN₀sq : N₀ 0 0 ^ 2 ≠ 1 := by
    intro h
    apply hx₀
    have h2 : β ((x₀ : K₀) ^ 2) = β 1 := by
      rw [hβ, key1, ← hN₀def, h, map_one]
    exact eq_one_of_sq_eq_one (β.injective h2)
  obtain ⟨z, hz⟩ := exists_conj_uu_diag hN₀ hN₀sq
  let ι₂ : SL(2, K₀) →* SL(2, F) := (MulAut.conj (uu z)).toMonoidHom.comp ι
  have hι₂ : ∀ A, ι₂ A = uu z * ι A * (uu z)⁻¹ := fun A => rfl
  have hι₂u : ∀ b, ι₂ (uu b) = uu (β b) := by
    intro b
    rw [hι₂, hαu, uu_mul_comm, mul_inv_cancel_right, hβ]
  set D := ι₂ (hh x₀) with hDdef
  have hD10 : D 1 0 = 0 := lowerLeft_uu_conj hN₀ z
  have hD01 : D 0 1 = 0 := hz
  have hD00 : D 0 0 ^ 2 ≠ 1 := by
    rw [hDdef, hι₂, upperLeft_uu_conj hN₀ z]
    exact hN₀sq
  set W := ι₂ ww with hWdef
  have hWD : W * D * W⁻¹ = D⁻¹ := by
    rw [hWdef, hDdef, ← map_inv, ← map_mul, ← map_mul, ww_conj_hh, map_inv]
  obtain ⟨hW00, hW11⟩ := diag_eq_zero_of_conj hD01 hD10 hD00 hWD
  have hl1 : ι₂ (ll 1) = ll (W 1 0 ^ 2) := by
    rw [← ww_conj_uu, map_mul, map_mul, map_inv, hι₂u, map_one, ← hWdef]
    exact antidiag_conj_uu_one hW00 hW11
  have hc : W 1 0 ^ 2 = 1 := by
    apply eq_one_of_pow_three
    have h3 := congrArg ι₂ (uu_one_mul_ll_one_pow_three (K := K₀))
    rwa [map_pow, map_mul, hι₂u, hl1, map_one, map_one] at h3
  have hWw : W = ww := eq_ww_of_antidiag hW00 hW11 (eq_one_of_sq_eq_one hc)
  have hι₂l : ∀ b, ι₂ (ll b) = ll (β b) := by
    intro b
    rw [← ww_conj_uu, map_mul, map_mul, map_inv, hι₂u, ← hWdef, hWw, ww_conj_uu]
  have hmap : ι₂ = Matrix.SpecialLinearGroup.map β := by
    apply MonoidHom.eq_of_eqOn_dense closure_uu_ll
    rintro A (⟨b, rfl⟩ | ⟨b, rfl⟩)
    · rw [hι₂u, map_uu]
    · rw [hι₂l, map_ll]
  refine ⟨β, (uu z)⁻¹, fun A => ?_⟩
  have h := DFunLike.congr_fun hmap A
  rw [hι₂] at h
  rw [← h]
  group

theorem exists_conj_eq_map (hK₀ : 4 ≤ Nat.card K₀) (ι : SL(2, K₀) →* SL(2, F))
    (hι : Function.Injective ι) :
    ∃ (β : K₀ →+* F) (c : SL(2, F)),
      ∀ A, ι A = c * Matrix.SpecialLinearGroup.map β A * c⁻¹ := by
  have hX2 : ι (uu 1) * ι (uu 1) = 1 := by
    rw [← map_mul, ← uu_add, CharTwo.add_self_eq_zero, uu_zero, map_one]
  have hX1 : ι (uu 1) ≠ 1 := by
    intro h
    rw [← map_one ι, ← uu_zero] at h
    exact one_ne_zero (uu_injective (hι h))
  obtain ⟨P, hP⟩ := exists_conj_eq_uu_one hX2 hX1
  let ι₁ : SL(2, K₀) →* SL(2, F) := (MulAut.conj P⁻¹).toMonoidHom.comp ι
  have hι₁ : ∀ A, ι₁ A = P⁻¹ * ι A * P⁻¹⁻¹ := fun A => rfl
  have h1 : ι₁ (uu 1) = uu 1 := by
    rw [hι₁, hP]
    group
  obtain ⟨β, c, hc⟩ := exists_conj_eq_map_of_uu_one hK₀ ι₁ h1
  refine ⟨β, P * c, fun A => ?_⟩
  have h := hc A
  rw [hι₁] at h
  calc ι A = P * (P⁻¹ * ι A * P⁻¹⁻¹) * P⁻¹ := by group
    _ = P * c * Matrix.SpecialLinearGroup.map β A * (P * c)⁻¹ := by rw [h]; group

end Main

end CFSG.RankThree.PartTwo.KFacts.KS116Proof
