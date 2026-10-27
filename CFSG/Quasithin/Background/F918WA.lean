module

public import CFSG.Quasithin.Background.F918V0
public import CFSG.Quasithin.Background.F918W4

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Quasithin.D35ValChk Matrix

private theorem bmul_assoc' (a b c : Nat) : bmul (bmul a b) c = bmul a (bmul b c) :=
  toM_inj (bmul_lt _ _) (bmul_lt _ _) (by simp only [toM_bmul, Matrix.mul_assoc])

private theorem bmul_idm_right {x : Nat} (hx : x < 2 ^ 36) : bmul x idm = x :=
  toM_inj (bmul_lt _ _) hx (by rw [toM_bmul, toM_idm, Matrix.mul_one])

private theorem bmul_idm_left {x : Nat} (hx : x < 2 ^ 36) : bmul idm x = x :=
  toM_inj (bmul_lt _ _) hx (by rw [toM_bmul, toM_idm, Matrix.one_mul])

private theorem bmul_idm_comm {x y : Nat} (h : bmul x y = idm) : bmul y x = idm := by
  apply toM_inj (bmul_lt _ _) (by decide)
  have := congrArg toM h
  rw [toM_bmul, toM_idm] at this
  rw [toM_bmul, toM_idm]
  exact mul_eq_one_comm.mp this

private theorem conj_mul {K : Type} [Field K] {B B' X Y : Matrix (Fin 3) (Fin 3) K} (h : B * B' = 1) :
    (B' * X * B) * (B' * Y * B) = B' * (X * Y) * B := by
  calc (B' * X * B) * (B' * Y * B) = B' * X * (B * B') * Y * B := by simp only [Matrix.mul_assoc]
    _ = B' * (X * Y) * B := by rw [h, Matrix.mul_one, Matrix.mul_assoc B' X Y]

private theorem conj_pow {K : Type} [Field K] {B B' X : Matrix (Fin 3) (Fin 3) K} (h1 : B * B' = 1)
    (h2 : B' * B = 1) (n : ℕ) : (B' * X * B) ^ n = B' * X ^ n * B := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Matrix.mul_one, h2]
  | succ n ih => rw [pow_succ, ih, pow_succ, conj_mul h1]

private theorem scalar_ne_zero {K : Type} [Field K] (g : Matrix.GeneralLinearGroup (Fin 3) K) {c : K}
    (h : ((g : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = c • (1 : Matrix (Fin 3) (Fin 3) K)) :
    c ≠ 0 := by
  intro hc
  have := g.val_inv
  rw [h, hc, zero_smul, zero_mul] at this
  exact zero_ne_one this

private theorem conj_back {K : Type} [Field K] {B B' X : Matrix (Fin 3) (Fin 3) K} (h : B * B' = 1) :
    B * (B' * X * B) * B' = X := by
  calc B * (B' * X * B) * B' = (B * B') * X * (B * B') := by simp only [Matrix.mul_assoc]
    _ = X := by rw [h, Matrix.one_mul, Matrix.mul_one]

private theorem isScalK_conj {K : Type} [Field K] (C : KCoding K) {B B' M : Matrix (Fin 3) (Fin 3) K}
    (h2 : B' * B = 1) {c : K} (hc : c ≠ 0) (hM : M = c • (1 : Matrix (Fin 3) (Fin 3) K)) :
    isScalK (C.mc (B' * M * B)) = true := by
  rw [C.mc_scalar]
  refine ⟨c, hc, ?_⟩
  rw [hM, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, h2]

private theorem mc_pow3 {K : Type} [Field K] (C : KCoding K) (P : Matrix (Fin 3) (Fin 3) K) :
    C.mc (P ^ 3) = kpow3 (C.mc P) := by
  rw [pow_three, C.mc_mul, C.mc_mul]
  rfl

private theorem mc_pow4 {K : Type} [Field K] (C : KCoding K) (P : Matrix (Fin 3) (Fin 3) K) :
    C.mc (P ^ 4) = kpow4 (C.mc P) := by
  rw [show P ^ 4 = (P * P) * (P * P) by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two], C.mc_mul, C.mc_mul]
  rfl

private theorem mc_pow5 {K : Type} [Field K] (C : KCoding K) (P : Matrix (Fin 3) (Fin 3) K) :
    C.mc (P ^ 5) = kpow5 (C.mc P) := by
  rw [pow_succ', C.mc_mul, mc_pow4]
  rfl

private theorem exists_conj_u0 (hF : D35Facts) {K : Type} [Field K] [CharP K 2] (C : KCoding K)
    {X : Matrix (Fin 3) (Fin 3) K} (h2 : X * X = 1) (h1 : X ≠ 1) :
    ∃ Bk B'k U : Matrix (Fin 3) (Fin 3) K, Bk * B'k = 1 ∧ B'k * Bk = 1 ∧ C.mc U = u0 ∧ B'k * X * Bk = U ∧
      C.mc Bk < 2 ^ 18 ∧ C.mc B'k < 2 ^ 18 := by
  obtain ⟨B, B', hB, hB', hX, hBB'⟩ := hF.conj_u0 (C.mc X) (mc_mem_tList C h2 h1)
  obtain ⟨Bk, rfl⟩ := C.mc_surj hB
  obtain ⟨B'k, rfl⟩ := C.mc_surj hB'
  obtain ⟨U, hU⟩ := C.mc_surj (show u0 < 2 ^ 18 by decide)
  have h1' : Bk * B'k = 1 := C.mc_inj (by rw [C.mc_mul, C.mc_one]; exact hBB')
  have h2' : B'k * Bk = 1 := mul_eq_one_comm.mp h1'
  have hXB : X * Bk = Bk * U := C.mc_inj (by rw [C.mc_mul, C.mc_mul, hU]; exact hX)
  refine ⟨Bk, B'k, U, h1', h2', hU, ?_, hB, hB'⟩
  calc B'k * X * Bk = B'k * (X * Bk) := by rw [Matrix.mul_assoc]
    _ = B'k * (Bk * U) := by rw [hXB]
    _ = U := by rw [← Matrix.mul_assoc, h2', Matrix.one_mul]

private theorem exists_normalization_matrix (hF : D35Facts) {K : Type} [Field K] [CharP K 2] (C : KCoding K)
    {X₁ X₂ X₃ : Matrix (Fin 3) (Fin 3) K}
    (h11 : X₁ * X₁ = 1) (h22 : X₂ * X₂ = 1) (h33 : X₃ * X₃ = 1) (h12 : X₁ ≠ X₂) (h13 : X₁ ≠ X₃)
    (h23 : X₂ ≠ X₃) (h1 : X₁ ≠ 1) (h2 : X₂ ≠ 1) (h3 : X₃ ≠ 1)
    (r12 : ∃ c : K, c ≠ 0 ∧ (X₁ * X₂) ^ 3 = c • (1 : Matrix (Fin 3) (Fin 3) K))
    (r13 : ∃ c : K, c ≠ 0 ∧ (X₁ * X₃) ^ 3 = c • (1 : Matrix (Fin 3) (Fin 3) K))
    (r23 : ∃ c : K, c ≠ 0 ∧ (X₂ * X₃) ^ 4 = c • (1 : Matrix (Fin 3) (Fin 3) K))
    (r123 : ∃ c : K, c ≠ 0 ∧ (X₁ * X₂ * X₃) ^ 5 = c • (1 : Matrix (Fin 3) (Fin 3) K)) :
    ∃ Ψ Ψ' s : Nat, Ψ < 2 ^ 36 ∧ Ψ' < 2 ^ 36 ∧ s < 2 ∧ bmul Ψ Ψ' = idm ∧ bmul Ψ' Ψ = idm ∧
      bmul (bmul Ψ (expand (C.mc X₁))) Ψ' = expand u0 ∧
      bmul (bmul Ψ (expand (C.mc X₂))) Ψ' = expand (refA s) ∧
      bmul (bmul Ψ (expand (C.mc X₃))) Ψ' = expand (refB s) := by
  obtain ⟨Bk, B'k, U, hBB, hB'B, hU, hY1, hBlt, hB'lt⟩ := exists_conj_u0 hF C h11 h1
  have hconj_sq : ∀ X : Matrix (Fin 3) (Fin 3) K, X * X = 1 → (B'k * X * Bk) * (B'k * X * Bk) = 1 := by
    intro X hX
    rw [conj_mul hBB, hX, Matrix.mul_one, hB'B]
  have hconj_ne : ∀ X : Matrix (Fin 3) (Fin 3) K, X ≠ 1 → B'k * X * Bk ≠ 1 := by
    intro X hX h
    apply hX
    rw [← conj_back (X := X) hBB, h, Matrix.mul_one, hBB]
  have hconj_inj : ∀ X Y : Matrix (Fin 3) (Fin 3) K, X ≠ Y → B'k * X * Bk ≠ B'k * Y * Bk := by
    intro X Y hXY h
    apply hXY
    rw [← conj_back (X := X) hBB, ← conj_back (X := Y) hBB, h]
  set Y₂ := B'k * X₂ * Bk with hY₂
  set Y₃ := B'k * X₃ * Bk with hY₃
  have hY₂sq : Y₂ * Y₂ = 1 := hconj_sq X₂ h22
  have hY₃sq : Y₃ * Y₃ = 1 := hconj_sq X₃ h33
  have hY₂ne : Y₂ ≠ 1 := hconj_ne X₂ h2
  have hY₃ne : Y₃ ≠ 1 := hconj_ne X₃ h3
  have hY₁₂ : U ≠ Y₂ := by rw [← hY1]; exact hconj_inj X₁ X₂ h12
  have hY₁₃ : U ≠ Y₃ := by rw [← hY1]; exact hconj_inj X₁ X₃ h13
  have hY₂₃ : Y₂ ≠ Y₃ := hconj_inj X₂ X₃ h23
  have hm2 := mc_mem_tList C hY₂sq hY₂ne
  have hm3 := mc_mem_tList C hY₃sq hY₃ne
  have hrel : ∀ (M : Matrix (Fin 3) (Fin 3) K) (c : K), c ≠ 0 → M = c • (1 : Matrix (Fin 3) (Fin 3) K) →
      isScalK (C.mc (B'k * M * Bk)) = true := fun M c hc hM => isScalK_conj C hB'B hc hM
  have hU' : C.mc U = u0 := hU
  have e12 : U * Y₂ = B'k * (X₁ * X₂) * Bk := by
    rw [← hY1, hY₂]
    exact conj_mul hBB
  have e123 : U * Y₂ * Y₃ = B'k * (X₁ * X₂ * X₃) * Bk := by
    rw [e12, hY₃]
    exact conj_mul hBB
  obtain ⟨c12, hc12, hr12⟩ := r12
  obtain ⟨c13, hc13, hr13⟩ := r13
  obtain ⟨c23, hc23, hr23⟩ := r23
  obtain ⟨c123, hc123, hr123⟩ := r123
  have s12 : isScalK (kpow3 (kmul u0 (C.mc Y₂))) = true := by
    rw [← hU', ← C.mc_mul, ← mc_pow3, e12, conj_pow hBB hB'B]
    exact hrel _ _ hc12 hr12
  have e13 : U * Y₃ = B'k * (X₁ * X₃) * Bk := by
    rw [← hY1, hY₃]
    exact conj_mul hBB
  have s13 : isScalK (kpow3 (kmul u0 (C.mc Y₃))) = true := by
    rw [← hU', ← C.mc_mul, ← mc_pow3, e13, conj_pow hBB hB'B]
    exact hrel _ _ hc13 hr13
  have e23 : Y₂ * Y₃ = B'k * (X₂ * X₃) * Bk := by
    rw [hY₂, hY₃]
    exact conj_mul hBB
  have s23 : isScalK (kpow4 (kmul (C.mc Y₂) (C.mc Y₃))) = true := by
    rw [← C.mc_mul, ← mc_pow4, e23, conj_pow hBB hB'B]
    exact hrel _ _ hc23 hr23
  have s123 : isScalK (kpow5 (kmul (kmul u0 (C.mc Y₂)) (C.mc Y₃))) = true := by
    rw [← hU', ← C.mc_mul, ← C.mc_mul, ← mc_pow5, e123, conj_pow hBB hB'B]
    exact hrel _ _ hc123 hr123
  have hne2 : C.mc Y₂ ≠ u0 := fun h => hY₁₂ (C.mc_inj (by rw [hU', h])).symm
  have hne3 : C.mc Y₃ ≠ u0 := fun h => hY₁₃ (C.mc_inj (by rw [hU', h])).symm
  have hne23 : C.mc Y₂ ≠ C.mc Y₃ := fun h => hY₂₃ (C.mc_inj h)
  obtain ⟨s, P, Q, hs, hP, hQ, hPu, hP2, hP3, hPQ⟩ :=
    hF.pair_bij (C.mc Y₂) hm2 (C.mc Y₃) hm3 hne2 hne3 hne23 s12 s13 s23 s123
  have hBB'e : bmul (expand (C.mc B'k)) (expand (C.mc Bk)) = idm := by
    rw [← expand_kmul hB'lt hBlt, ← C.mc_mul, hB'B, C.mc_one]
    decide
  have hΨΨ' : bmul (bmul P (expand (C.mc B'k))) (bmul (expand (C.mc Bk)) Q) = idm := by
    rw [bmul_assoc', ← bmul_assoc' (expand (C.mc B'k)), hBB'e, bmul_idm_left hQ, hPQ]
  have key : ∀ X : Matrix (Fin 3) (Fin 3) K,
      bmul (bmul (bmul P (expand (C.mc B'k))) (expand (C.mc X))) (bmul (expand (C.mc Bk)) Q) =
        bmul (bmul P (expand (C.mc (B'k * X * Bk)))) Q := by
    intro X
    have : expand (C.mc (B'k * X * Bk)) =
        bmul (bmul (expand (C.mc B'k)) (expand (C.mc X))) (expand (C.mc Bk)) := by
      rw [C.mc_mul, C.mc_mul, expand_kmul (kmul_lt _ _) hBlt, expand_kmul hB'lt (C.mc_lt X)]
    rw [this]
    simp only [bmul_assoc']
  refine ⟨bmul P (expand (C.mc B'k)), bmul (expand (C.mc Bk)) Q, s, bmul_lt _ _, bmul_lt _ _, hs, hΨΨ',
    bmul_idm_comm hΨΨ', ?_, ?_, ?_⟩
  · rw [key X₁, hY1, hU', hPu, bmul_assoc', hPQ, bmul_idm_right (expand_lt _)]
  · rw [key X₂, ← hY₂, hP2, bmul_assoc', hPQ, bmul_idm_right (expand_lt _)]
  · rw [key X₃, ← hY₃, hP3, bmul_assoc', hPQ, bmul_idm_right (expand_lt _)]

private theorem relator_scalar {K : Type} [Field K] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K)}
    (hcen : ∀ g ∈ Subgroup.center ↥Γ, ∃ c : K,
      (((g : ↥Γ) : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = c • 1)
    (g : ↥Γ) (hg : g ∈ Subgroup.center ↥Γ) :
    ∃ c : K, c ≠ 0 ∧ (((g : ↥Γ) : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      c • (1 : Matrix (Fin 3) (Fin 3) K) := by
  obtain ⟨c, hc⟩ := hcen g hg
  exact ⟨c, scalar_ne_zero (g : Matrix.GeneralLinearGroup (Fin 3) K) hc, hc⟩

theorem exists_normalization (hF : D35Facts) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) (C : KCoding K)
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K)} (hv : IsValentiner K Γ) {x₁ x₂ x₃ : ↥Γ}
    (h11 : x₁ * x₁ = 1) (h22 : x₂ * x₂ = 1) (h33 : x₃ * x₃ = 1) (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃)
    (h1 : x₁ ≠ 1) (h2 : x₂ ≠ 1) (h3 : x₃ ≠ 1)
    (r12 : (x₁ * x₂) ^ 3 ∈ Subgroup.center ↥Γ) (r13 : (x₁ * x₃) ^ 3 ∈ Subgroup.center ↥Γ)
    (r23 : (x₂ * x₃) ^ 4 ∈ Subgroup.center ↥Γ) (r123 : (x₁ * x₂ * x₃) ^ 5 ∈ Subgroup.center ↥Γ) :
    ∃ Ψ Ψ' s : Nat, Ψ < 2 ^ 36 ∧ Ψ' < 2 ^ 36 ∧ s < 2 ∧ bmul Ψ Ψ' = idm ∧ bmul Ψ' Ψ = idm ∧
      bmul (bmul Ψ (expand (C.mc ((x₁ : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)))) Ψ' =
        expand u0 ∧
      bmul (bmul Ψ (expand (C.mc ((x₂ : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)))) Ψ' =
        expand (refA s) ∧
      bmul (bmul Ψ (expand (C.mc ((x₃ : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)))) Ψ' =
        expand (refB s) := by
  have : CharP K 2 := charP_two_of_card_four K hK
  have hsq : ∀ x : ↥Γ, x * x = 1 →
      ((x : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((x : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := fun x h => by
    have := congrArg (fun g : ↥Γ => ((g : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h
    simpa using this
  have hne1 : ∀ x : ↥Γ, x ≠ 1 →
      ((x : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ 1 := fun x h hx =>
    h (Subtype.ext (Units.ext (by simpa using hx)))
  have hne : ∀ x y : ↥Γ, x ≠ y →
      ((x : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠
        ((y : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := fun x y h hx =>
    h (Subtype.ext (Units.ext hx))
  have hcen := hv.2.2.2
  obtain ⟨c12, hc12, e12⟩ := relator_scalar hcen _ r12
  obtain ⟨c13, hc13, e13⟩ := relator_scalar hcen _ r13
  obtain ⟨c23, hc23, e23⟩ := relator_scalar hcen _ r23
  obtain ⟨c123, hc123, e123⟩ := relator_scalar hcen _ r123
  refine exists_normalization_matrix hF C (hsq _ h11) (hsq _ h22) (hsq _ h33) (hne _ _ h12) (hne _ _ h13)
    (hne _ _ h23) (hne1 _ h1) (hne1 _ h2) (hne1 _ h3) ⟨c12, hc12, ?_⟩ ⟨c13, hc13, ?_⟩ ⟨c23, hc23, ?_⟩
    ⟨c123, hc123, ?_⟩
  · rw [← e12]; simp
  · rw [← e13]; simp
  · rw [← e23]; simp
  · rw [← e123]; simp

end CFSG.Quasithin
