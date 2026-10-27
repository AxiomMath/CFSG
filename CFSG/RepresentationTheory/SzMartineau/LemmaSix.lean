module

public import CFSG.RepresentationTheory.SzMartineau.LemmaSixWeights
public import CFSG.RepresentationTheory.SzMartineau.Normalize

public section

namespace CFSG.RepresentationTheory.SzMartineau

open CFSG.Open CFSG.RankThree.GF2n.SzExplicit CFSG.CGT.PushingUpLit.SolKNA Matrix

variable {a : ℕ}

private theorem zmod_intCast_eq_of_forall_zpow_eq {K : Type*} [Field K] [Fintype K] {A B : ℤ}
    (h : ∀ x : Kˣ, x ^ A = x ^ B) :
    (A : ZMod (Fintype.card K - 1)) = (B : ZMod (Fintype.card K - 1)) := by
  set m : ℕ := Fintype.card K - 1 with hmdef
  have hm : 0 < m := by
    have := Fintype.one_lt_card (α := K)
    omega
  have hgroup : ∀ x : Kˣ, x ^ (A - B) = 1 := by
    intro x
    have hx := h x
    rw [sub_eq_add_neg, _root_.zpow_add, _root_.zpow_neg, hx, mul_inv_cancel]
  have hxpow : ∀ x : Kˣ, x ^ m = 1 := by
    intro x
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact FiniteField.pow_card_sub_one_eq_one (x : K) (Units.ne_zero x)
  have h1 : ∀ x : Kˣ, x ^ (((A - B) % (m : ℤ)).toNat) = 1 := by
    intro x
    have hx := hgroup x
    have hx' : x ^ ((A - B) % (m : ℤ)) = 1 := by
      rw [← zpow_eq_zpow_emod' (A - B) (hxpow x)]
      exact hx
    have hnonneg : 0 ≤ (A - B) % (m : ℤ) := Int.emod_nonneg _ (by omega)
    rw [← zpow_natCast, Int.toNat_of_nonneg hnonneg]
    exact hx'
  have hdvd : m ∣ (((A - B) % (m : ℤ)).toNat) :=
    (FiniteField.forall_pow_eq_one_iff K (((A - B) % (m : ℤ)).toNat)).mp h1
  have hlt : (((A - B) % (m : ℤ)).toNat) < m := by
    have h0 : 0 ≤ (A - B) % (m : ℤ) := Int.emod_nonneg _ (by omega)
    have := Int.emod_lt_of_pos (A - B) (by omega : (0 : ℤ) < m)
    omega
  have hzero : (((A - B) % (m : ℤ)).toNat) = 0 :=
    Nat.eq_zero_of_dvd_of_lt hdvd hlt
  have hmod : (A - B) % (m : ℤ) = 0 := by
    have h0 : 0 ≤ (A - B) % (m : ℤ) := Int.emod_nonneg _ (by omega)
    have := Int.toNat_eq_zero.mp hzero
    omega
  have hz : ((A - B : ℤ) : ZMod m) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact Int.dvd_of_emod_eq_zero hmod
  push_cast at hz ⊢
  linear_combination hz

local macro "char2_norm" : tactic =>
  `(tactic| (ring_nf <;> simp only [CharTwo.ofNat_eq_mod] <;> norm_num))

private noncomputable def basis (a : ℕ) (j : Fin 4) : Fin 4 → F a :=
  fun i => if i = j then 1 else 0

private noncomputable def coef (B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a))
    (r s t : Fin 4) : F a :=
  B (basis a s) (basis a t) r

private lemma basis_self (j : Fin 4) : basis a j j = 1 := by
  simp [basis]

private lemma basis_of_ne {i j : Fin 4} (h : i ≠ j) : basis a j i = 0 := by
  simp [basis, h]

private noncomputable def torusDiag (x : (F a)ˣ) : Fin 4 → F a :=
  ![(x : F a) ^ (1 + 2 ^ a), (x : F a) ^ (2 ^ a), ((x : F a) ^ (2 ^ a))⁻¹,
    ((x : F a) ^ (1 + 2 ^ a))⁻¹]

private lemma torusMat_apply_eq (x : (F a)ˣ) (i j : Fin 4) :
    torusMat a x i j = if i = j then torusDiag x i else 0 := by
  fin_cases i <;> fin_cases j <;> simp [torusMat, torusDiag]

private lemma torusDiag_eq_zpow (x : (F a)ˣ) (i : Fin 4) :
    torusDiag x i = (x : F a) ^ szWtInt a i := by
  fin_cases i
  · simp [torusDiag]
    have h : szWtInt a 0 = ((1 + 2 ^ a : ℕ) : ℤ) := by simp [szWtInt]
    rw [h, zpow_natCast]
  · simp [torusDiag]
    have h : szWtInt a 1 = ((2 ^ a : ℕ) : ℤ) := by simp [szWtInt]
    rw [h, zpow_natCast]
  · simp [torusDiag]
    have h : szWtInt a 2 = -((2 ^ a : ℕ) : ℤ) := by simp [szWtInt]
    rw [h, _root_.zpow_neg, zpow_natCast]
  · simp [torusDiag]
    have h : szWtInt a 3 = -((1 + 2 ^ a : ℕ) : ℤ) := by simp [szWtInt]
    rw [h, _root_.zpow_neg, zpow_natCast]

private lemma torusMat_mulVec_apply (x : (F a)ˣ) (v : Fin 4 → F a) (r : Fin 4) :
    (torusMat a x *ᵥ v) r = torusDiag x r * v r := by
  rw [Matrix.mulVec_apply_eq_sum, Finset.sum_eq_single r]
  · rw [torusMat_apply_eq, if_pos rfl]
  · intro j _ hjr
    rw [torusMat_apply_eq, if_neg (Ne.symm hjr), zero_mul]
  · intro hr
    exact absurd (Finset.mem_univ r) hr

private lemma torusMat_mulVec_basis (x : (F a)ˣ) (s : Fin 4) :
    torusMat a x *ᵥ basis a s = torusDiag x s • basis a s := by
  ext i
  rw [torusMat_mulVec_apply]
  by_cases his : i = s
  · subst his
    rw [basis_self, Pi.smul_apply, basis_self, smul_eq_mul, mul_one]
  · rw [basis_of_ne his, mul_zero, Pi.smul_apply, basis_of_ne his, smul_zero]

private lemma units_val_pow_zpow (x : (F a)ˣ) (n : ℕ) (m : ℤ) :
    (((x ^ n : (F a)ˣ) : F a)) ^ m = (x : F a) ^ ((n : ℤ) * m) := by
  rw [Units.val_pow_eq_pow_val, ← zpow_natCast, ← _root_.zpow_mul]

private lemma coef_torus_eq {c₁ c₂ c₃ : ℕ}
    {B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a)}
    (hB : ∀ (g : ↥(Sz a)) (v w : Fin 4 → F a),
      B (twHom a c₁ g *ᵥ v) (twHom a c₂ g *ᵥ w) = twHom a c₃ g *ᵥ B v w)
    (x : (F a)ˣ) (r s t : Fin 4) :
    (x : F a) ^ ((2 : ℤ) ^ c₁ * szWtInt a s + (2 : ℤ) ^ c₂ * szWtInt a t) *
        coef B r s t =
      (x : F a) ^ ((2 : ℤ) ^ c₃ * szWtInt a r) * coef B r s t := by
  have h := hB (torusSz a x) (basis a s) (basis a t)
  rw [twHom_torusSz, twHom_torusSz, twHom_torusSz] at h
  rw [torusMat_mulVec_basis, torusMat_mulVec_basis] at h
  have hr := congrFun h r
  rw [torusMat_mulVec_apply] at hr
  simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul] at hr
  rw [torusDiag_eq_zpow, torusDiag_eq_zpow, torusDiag_eq_zpow] at hr
  rw [units_val_pow_zpow, units_val_pow_zpow, units_val_pow_zpow] at hr
  have hz : (x : F a) ^
        (((2 ^ c₂ : ℕ) : ℤ) * szWtInt a t + ((2 ^ c₁ : ℕ) : ℤ) * szWtInt a s) =
      (x : F a) ^
        (((2 ^ c₁ : ℕ) : ℤ) * szWtInt a s + ((2 ^ c₂ : ℕ) : ℤ) * szWtInt a t) := by
    congr 1
    ring
  rw [← mul_assoc, ← zpow_add₀ (x.ne_zero), hz] at hr
  exact hr

private lemma admTwist_of_coef_ne_zero {c₁ c₂ c₃ : ℕ}
    {B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a)}
    (hB : ∀ (g : ↥(Sz a)) (v w : Fin 4 → F a),
      B (twHom a c₁ g *ᵥ v) (twHom a c₂ g *ᵥ w) = twHom a c₃ g *ᵥ B v w)
    {r s t : Fin 4} (h : coef B r s t ≠ 0) : AdmTwist a c₁ c₂ c₃ r s t := by
  rw [AdmTwist]
  have hz : ∀ x : (F a)ˣ,
      x ^ ((2 : ℤ) ^ c₁ * szWtInt a s + (2 : ℤ) ^ c₂ * szWtInt a t) =
        x ^ ((2 : ℤ) ^ c₃ * szWtInt a r) := by
    intro x
    have hx := coef_torus_eq hB x r s t
    apply Units.ext
    rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val]
    exact mul_right_cancel₀ h hx
  letI : Fintype (F a) := Fintype.ofFinite _
  have hval := zmod_intCast_eq_of_forall_zpow_eq (K := F a) hz
  rw [show Fintype.card (F a) = 2 ^ (2 * a + 1) from by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 (2 * a + 1) (by omega)] at hval
  push_cast at hval ⊢
  rw [szWt_eq_intCast_szWtInt]
  rw [szWt_eq_intCast_szWtInt, szWt_eq_intCast_szWtInt]
  push_cast at hval
  exact hval.symm

private lemma coef_eq_zero_of_not_adm {c₁ c₂ c₃ : ℕ}
    {B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a)}
    (hB : ∀ (g : ↥(Sz a)) (v w : Fin 4 → F a),
      B (twHom a c₁ g *ᵥ v) (twHom a c₂ g *ᵥ w) = twHom a c₃ g *ᵥ B v w)
    {r s t : Fin 4} (h : ¬ AdmTwist a c₁ c₂ c₃ r s t) : coef B r s t = 0 := by
  by_contra hne
  exact h (admTwist_of_coef_ne_zero hB hne)

private lemma mulVec_basis (M : Matrix (Fin 4) (Fin 4) (F a)) (j : Fin 4) :
    M *ᵥ basis a j = fun i => M i j := by
  ext i
  rw [Matrix.mulVec_apply_eq_sum, Finset.sum_eq_single j]
  · rw [basis_self, mul_one]
  · intro k _ hkj
    rw [basis_of_ne hkj, mul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

private lemma eq_sum_smul_basis (v : Fin 4 → F a) :
    v = ∑ j, v j • basis a j := by
  ext i
  rw [Finset.sum_apply, Finset.sum_eq_single i]
  · rw [Pi.smul_apply, basis_self, smul_eq_mul, mul_one]
  · intro j _ hji
    rw [Pi.smul_apply, basis_of_ne (Ne.symm hji), smul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private lemma map_pow_eq_self_of_binary (M : Matrix (Fin 4) (Fin 4) (F a))
    (hbin : ∀ i j, M i j = 0 ∨ M i j = 1) (c : ℕ) : M.map (· ^ 2 ^ c) = M := by
  ext i j
  rw [Matrix.map_apply]
  rcases hbin i j with h | h
  · rw [h, zero_pow (Nat.two_pow_pos c).ne']
  · rw [h, one_pow]

private lemma bilin_basis_left (B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a))
    (s : Fin 4) (w : Fin 4 → F a) (r : Fin 4) :
    B (basis a s) w r = ∑ t : Fin 4, w t * coef B r s t := by
  conv_lhs => rw [eq_sum_smul_basis w]
  simp only [map_sum, LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul]
  rfl

private lemma bilin_apply_eq (B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a))
    (v w : Fin 4 → F a) (r : Fin 4) :
    B v w r = ∑ s : Fin 4, ∑ t : Fin 4, v s * w t * coef B r s t := by
  conv_lhs => rw [eq_sum_smul_basis v]
  simp only [map_sum, LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, bilin_basis_left,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

private lemma coef_coord_eq {c₁ c₂ c₃ : ℕ}
    {B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a)}
    (hB : ∀ (g : ↥(Sz a)) (v w : Fin 4 → F a),
      B (twHom a c₁ g *ᵥ v) (twHom a c₂ g *ᵥ w) = twHom a c₃ g *ᵥ B v w)
    (g : ↥(Sz a)) (M : Matrix (Fin 4) (Fin 4) (F a)) (hM : natHom a g = M)
    (hbin : ∀ i j, M i j = 0 ∨ M i j = 1) (r s' t' : Fin 4) :
    (∑ s : Fin 4, ∑ t : Fin 4, M s s' * M t t' * coef B r s t) =
      ∑ r' : Fin 4, M r r' * coef B r' s' t' := by
  have htw : ∀ c : ℕ, twHom a c g = M := by
    intro c
    rw [twHom_apply, hM, map_pow_eq_self_of_binary M hbin c]
  have h := hB g (basis a s') (basis a t')
  rw [htw c₁, htw c₂, htw c₃, mulVec_basis, mulVec_basis] at h
  have hr := congrFun h r
  have hL : B (fun i => M i s') (fun i => M i t') r =
      ∑ s : Fin 4, ∑ t : Fin 4, M s s' * M t t' * coef B r s t :=
    bilin_apply_eq B (fun i => M i s') (fun i => M i t') r
  have hR : (M *ᵥ (fun i => B (basis a s') (basis a t') i)) r =
      ∑ r' : Fin 4, M r r' * coef B r' s' t' := by
    rw [Matrix.mulVec_apply_eq_sum]
    rfl
  rw [hL, hR] at hr
  exact hr

private lemma coef_first_eq (B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a))
    (v w : Fin 4 → F a) :
    B v w 0 = ∑ s : Fin 4, ∑ t : Fin 4, v s * w t * coef B 0 s t :=
  bilin_apply_eq B v w 0

private lemma eq_zero_of_row_zero {c₁ c₂ c₃ : ℕ}
    {B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a)}
    (hB : ∀ (g : ↥(Sz a)) (v w : Fin 4 → F a),
      B (twHom a c₁ g *ᵥ v) (twHom a c₂ g *ᵥ w) = twHom a c₃ g *ᵥ B v w)
    (h0 : ∀ s t : Fin 4, coef B 0 s t = 0) (v w : Fin 4 → F a) : B v w = 0 := by
  have hfirst : ∀ v w : Fin 4 → F a, B v w 0 = 0 := by
    intro v w
    rw [coef_first_eq]
    refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun t _ => ?_
    rw [h0 s t, mul_zero]
  have htwS : ∀ (c i : ℕ), twHom a c (rootSz a 1 0 ^ i) =
      (szX₀ : Matrix (Fin 4) (Fin 4) (F a)) ^ i := by
    intro c i
    rw [map_pow, twHom_rootSz_one_zero, rootMat_one_zero_eq_szX₀]
  have E : ∀ i : ℕ, (∑ r', ((szX₀ : Matrix (Fin 4) (Fin 4) (F a)) ^ i) 0 r' *
      (B v w) r') = 0 := by
    intro i
    have h := congrFun (hB (rootSz a 1 0 ^ i) v w) 0
    rw [htwS c₁ i, htwS c₂ i, htwS c₃ i] at h
    rw [hfirst] at h
    rw [Matrix.mulVec_apply_eq_sum] at h
    exact h.symm
  have E0 : B v w 0 = 0 := hfirst v w
  have E1 : B v w 0 + B v w 1 + B v w 3 = 0 := by
    have h := E 1
    rw [pow_one] at h
    simpa [szX₀, Fin.sum_univ_four] using h
  have E2 : B v w 0 + B v w 2 + B v w 3 = 0 := by
    have h := E 2
    rw [szX₀_sq] at h
    simpa [Fin.sum_univ_four] using h
  have E3 : B v w 0 + B v w 1 + B v w 2 + B v w 3 = 0 := by
    have h := E 3
    rw [szX₀_cube] at h
    simpa [Fin.sum_univ_four] using h
  funext r
  simp only [Pi.zero_apply]
  fin_cases r
  · exact E0
  · linear_combination (norm := char2_norm) E2 + E3
  · linear_combination (norm := char2_norm) E1 + E3
  · linear_combination (norm := char2_norm) E0 + E1 + E2 + E3

private noncomputable def matJSJ : Matrix (Fin 4) (Fin 4) (F a) :=
  !![1, 0, 0, 0; 1, 1, 0, 0; 1, 1, 1, 0; 1, 0, 1, 1]

private noncomputable def matJSSJ : Matrix (Fin 4) (Fin 4) (F a) :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 1, 0, 1]

private lemma szJ_binary :
    ∀ i j, (szJ : Matrix (Fin 4) (Fin 4) (F a)) i j = 0 ∨
      (szJ : Matrix (Fin 4) (Fin 4) (F a)) i j = 1 := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [szJ]

private lemma matJSJ_binary :
    ∀ i j, (matJSJ : Matrix (Fin 4) (Fin 4) (F a)) i j = 0 ∨
      (matJSJ : Matrix (Fin 4) (Fin 4) (F a)) i j = 1 := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [matJSJ]

private lemma matJSSJ_binary :
    ∀ i j, (matJSSJ : Matrix (Fin 4) (Fin 4) (F a)) i j = 0 ∨
      (matJSSJ : Matrix (Fin 4) (Fin 4) (F a)) i j = 1 := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [matJSSJ]

private lemma szJ_mul_szX₀_mul_szJ :
    (szJ : Matrix (Fin 4) (Fin 4) (F a)) * szX₀ * szJ = matJSJ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [szJ, szX₀, matJSJ, Matrix.mul_apply, Fin.sum_univ_four, CharTwo.add_self_eq_zero]

private lemma szJ_mul_szX₀_sq_mul_szJ :
    (szJ : Matrix (Fin 4) (Fin 4) (F a)) * szX₀ ^ 2 * szJ = matJSSJ := by
  rw [szX₀_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [szJ, matJSSJ, Matrix.mul_apply, Fin.sum_univ_four, CharTwo.add_self_eq_zero]

private lemma natHom_JSJ :
    natHom a (w a * rootSz a 1 0 * w a) = (matJSJ : Matrix (Fin 4) (Fin 4) (F a)) := by
  rw [map_mul, map_mul, natHom_w, natHom_rootSz, rootMat_one_zero_eq_szX₀, wMat_eq_szJ,
    szJ_mul_szX₀_mul_szJ]

private lemma natHom_JSSJ :
    natHom a (w a * rootSz a 1 0 ^ 2 * w a) =
      (matJSSJ : Matrix (Fin 4) (Fin 4) (F a)) := by
  rw [map_mul, map_mul, map_pow, natHom_w, natHom_rootSz, rootMat_one_zero_eq_szX₀,
    wMat_eq_szJ, szJ_mul_szX₀_sq_mul_szJ]

private lemma rel_J_033 {c₁ c₂ c₃ : ℕ}
    {B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a)}
    (hB : ∀ (g : ↥(Sz a)) (v w : Fin 4 → F a),
      B (twHom a c₁ g *ᵥ v) (twHom a c₂ g *ᵥ w) = twHom a c₃ g *ᵥ B v w) :
    coef B 0 0 0 = coef B 3 3 3 := by
  have h := coef_coord_eq hB (w a) (szJ : Matrix (Fin 4) (Fin 4) (F a))
    (by rw [natHom_w, wMat_eq_szJ]) szJ_binary 0 3 3
  simpa [szJ, Fin.sum_univ_four] using h

private lemma rel_J_032 {c₁ c₂ c₃ : ℕ}
    {B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a)}
    (hB : ∀ (g : ↥(Sz a)) (v w : Fin 4 → F a),
      B (twHom a c₁ g *ᵥ v) (twHom a c₂ g *ᵥ w) = twHom a c₃ g *ᵥ B v w) :
    coef B 0 0 1 = coef B 3 3 2 := by
  have h := coef_coord_eq hB (w a) (szJ : Matrix (Fin 4) (Fin 4) (F a))
    (by rw [natHom_w, wMat_eq_szJ]) szJ_binary 0 3 2
  simpa [szJ, Fin.sum_univ_four] using h

private lemma rel_J_023 {c₁ c₂ c₃ : ℕ}
    {B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a)}
    (hB : ∀ (g : ↥(Sz a)) (v w : Fin 4 → F a),
      B (twHom a c₁ g *ᵥ v) (twHom a c₂ g *ᵥ w) = twHom a c₃ g *ᵥ B v w) :
    coef B 0 1 0 = coef B 3 2 3 := by
  have h := coef_coord_eq hB (w a) (szJ : Matrix (Fin 4) (Fin 4) (F a))
    (by rw [natHom_w, wMat_eq_szJ]) szJ_binary 0 2 3
  simpa [szJ, Fin.sum_univ_four] using h

private lemma rel_JSSJ_313 {c₁ c₂ c₃ : ℕ}
    {B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a)}
    (hB : ∀ (g : ↥(Sz a)) (v w : Fin 4 → F a),
      B (twHom a c₁ g *ᵥ v) (twHom a c₂ g *ᵥ w) = twHom a c₃ g *ᵥ B v w) :
    coef B 3 3 3 = coef B 0 1 3 + coef B 1 1 3 := by
  have h := coef_coord_eq hB (w a * rootSz a 1 0 ^ 2 * w a)
    (matJSSJ : Matrix (Fin 4) (Fin 4) (F a)) natHom_JSSJ matJSSJ_binary 3 1 3
  simp [matJSSJ, Fin.sum_univ_four] at h
  linear_combination (norm := char2_norm) h

private lemma rel_JSSJ_312 {c₁ c₂ c₃ : ℕ}
    {B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a)}
    (hB : ∀ (g : ↥(Sz a)) (v w : Fin 4 → F a),
      B (twHom a c₁ g *ᵥ v) (twHom a c₂ g *ᵥ w) = twHom a c₃ g *ᵥ B v w) :
    coef B 3 3 2 = coef B 0 1 2 + coef B 1 1 2 := by
  have h := coef_coord_eq hB (w a * rootSz a 1 0 ^ 2 * w a)
    (matJSSJ : Matrix (Fin 4) (Fin 4) (F a)) natHom_JSSJ matJSSJ_binary 3 1 2
  simp [matJSSJ, Fin.sum_univ_four] at h
  linear_combination (norm := char2_norm) h

private lemma rel_JSSJ_321 {c₁ c₂ c₃ : ℕ}
    {B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a)}
    (hB : ∀ (g : ↥(Sz a)) (v w : Fin 4 → F a),
      B (twHom a c₁ g *ᵥ v) (twHom a c₂ g *ᵥ w) = twHom a c₃ g *ᵥ B v w) :
    coef B 3 2 3 = coef B 0 2 1 + coef B 1 2 1 := by
  have h := coef_coord_eq hB (w a * rootSz a 1 0 ^ 2 * w a)
    (matJSSJ : Matrix (Fin 4) (Fin 4) (F a)) natHom_JSSJ matJSSJ_binary 3 2 1
  simp [matJSSJ, Fin.sum_univ_four] at h
  linear_combination (norm := char2_norm) h

private lemma rel_JSSJ_230 {c₁ c₂ c₃ : ℕ}
    {B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a)}
    (hB : ∀ (g : ↥(Sz a)) (v w : Fin 4 → F a),
      B (twHom a c₁ g *ᵥ v) (twHom a c₂ g *ᵥ w) = twHom a c₃ g *ᵥ B v w) :
    coef B 0 3 0 = coef B 2 3 2 + coef B 2 3 3 := by
  have h := coef_coord_eq hB (w a * rootSz a 1 0 ^ 2 * w a)
    (matJSSJ : Matrix (Fin 4) (Fin 4) (F a)) natHom_JSSJ matJSSJ_binary 2 3 0
  simp [matJSSJ, Fin.sum_univ_four] at h
  linear_combination (norm := char2_norm) h

private lemma rel_JSSJ_202 {c₁ c₂ c₃ : ℕ}
    {B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a)}
    (hB : ∀ (g : ↥(Sz a)) (v w : Fin 4 → F a),
      B (twHom a c₁ g *ᵥ v) (twHom a c₂ g *ᵥ w) = twHom a c₃ g *ᵥ B v w) :
    coef B 0 0 2 = coef B 2 2 2 + coef B 2 3 2 := by
  have h := coef_coord_eq hB (w a * rootSz a 1 0 ^ 2 * w a)
    (matJSSJ : Matrix (Fin 4) (Fin 4) (F a)) natHom_JSSJ matJSSJ_binary 2 0 2
  simp [matJSSJ, Fin.sum_univ_four] at h
  linear_combination (norm := char2_norm) h

private lemma rel_JSJ_313 {c₁ c₂ c₃ : ℕ}
    {B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a)}
    (hB : ∀ (g : ↥(Sz a)) (v w : Fin 4 → F a),
      B (twHom a c₁ g *ᵥ v) (twHom a c₂ g *ᵥ w) = twHom a c₃ g *ᵥ B v w) :
    coef B 2 1 3 = coef B 0 1 3 + coef B 3 2 3 := by
  have h := coef_coord_eq hB (w a * rootSz a 1 0 * w a)
    (matJSJ : Matrix (Fin 4) (Fin 4) (F a)) natHom_JSJ matJSJ_binary 3 1 3
  simp [matJSJ, Fin.sum_univ_four] at h
  linear_combination (norm := char2_norm) h

private lemma rel_JSSJ_211 {c₁ c₂ c₃ : ℕ}
    {B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a)}
    (hB : ∀ (g : ↥(Sz a)) (v w : Fin 4 → F a),
      B (twHom a c₁ g *ᵥ v) (twHom a c₂ g *ᵥ w) = twHom a c₃ g *ᵥ B v w) :
    coef B 0 1 1 = coef B 2 1 3 + coef B 2 3 1 + coef B 2 3 3 := by
  have h := coef_coord_eq hB (w a * rootSz a 1 0 ^ 2 * w a)
    (matJSSJ : Matrix (Fin 4) (Fin 4) (F a)) natHom_JSSJ matJSSJ_binary 2 1 1
  simp [matJSSJ, Fin.sum_univ_four] at h
  linear_combination (norm := char2_norm) h

private lemma rel_JSJ_331 {c₁ c₂ c₃ : ℕ}
    {B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a)}
    (hB : ∀ (g : ↥(Sz a)) (v w : Fin 4 → F a),
      B (twHom a c₁ g *ᵥ v) (twHom a c₂ g *ᵥ w) = twHom a c₃ g *ᵥ B v w) :
    coef B 2 3 1 = coef B 0 3 1 + coef B 3 3 2 := by
  have h := coef_coord_eq hB (w a * rootSz a 1 0 * w a)
    (matJSJ : Matrix (Fin 4) (Fin 4) (F a)) natHom_JSJ matJSJ_binary 3 3 1
  simp [matJSJ, Fin.sum_univ_four] at h
  linear_combination (norm := char2_norm) h

private lemma rel_JSSJ_220 {c₁ c₂ c₃ : ℕ}
    {B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a)}
    (hB : ∀ (g : ↥(Sz a)) (v w : Fin 4 → F a),
      B (twHom a c₁ g *ᵥ v) (twHom a c₂ g *ᵥ w) = twHom a c₃ g *ᵥ B v w) :
    coef B 0 2 0 = coef B 2 2 2 + coef B 2 2 3 := by
  have h := coef_coord_eq hB (w a * rootSz a 1 0 ^ 2 * w a)
    (matJSSJ : Matrix (Fin 4) (Fin 4) (F a)) natHom_JSSJ matJSSJ_binary 2 2 0
  simp [matJSSJ, Fin.sum_univ_four] at h
  linear_combination (norm := char2_norm) h

private lemma rel_JSSJ_203 {c₁ c₂ c₃ : ℕ}
    {B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a)}
    (hB : ∀ (g : ↥(Sz a)) (v w : Fin 4 → F a),
      B (twHom a c₁ g *ᵥ v) (twHom a c₂ g *ᵥ w) = twHom a c₃ g *ᵥ B v w) :
    coef B 0 0 3 = coef B 2 2 3 + coef B 2 3 3 := by
  have h := coef_coord_eq hB (w a * rootSz a 1 0 ^ 2 * w a)
    (matJSSJ : Matrix (Fin 4) (Fin 4) (F a)) natHom_JSSJ matJSSJ_binary 2 0 3
  simp [matJSSJ, Fin.sum_univ_four] at h
  linear_combination (norm := char2_norm) h

private lemma adm_rho {a k j : ℕ} {r s t : Fin 4} (h : Adm a k j r s t) :
    (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ j * szRho a r =
      szRho a s + (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ k * szRho a t :=
  (adm_iff_rho a k j r s t).mp h

private lemma na_01_013 (ha : 3 ≤ a) : ¬ Adm a 0 1 0 1 3 := by
  intro h
  have h := adm_rho h
  simp [szRho] at h
  have ht : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1) = 4 := by
    linear_combination (norm := ring_nf) -h
  exact two_pow_succ_ne_four ha ht

private lemma na_01_113 (ha : 3 ≤ a) : ¬ Adm a 0 1 1 1 3 := by
  intro h
  have h := adm_rho h
  simp [szRho] at h
  have ht : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1) = 0 := by
    linear_combination (norm := ring_nf) h
  exact two_pow_succ_ne_zero (by omega) ht

private lemma na_0a_012 (ha : 3 ≤ a) : ¬ Adm a 0 (a + 1) 0 1 2 := by
  intro h
  have h := adm_rho h
  simp [szRho] at h
  have ht : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1) = 0 := by
    linear_combination (norm := ring_nf) h
  exact two_pow_succ_ne_zero (by omega) ht

private lemma na_0a_112 (ha : 3 ≤ a) : ¬ Adm a 0 (a + 1) 1 1 2 := by
  intro h
  have h := adm_rho h
  simp [szRho] at h
  have ht : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1) = 2 := by
    linear_combination (norm := ring_nf) -h + 2 * two_mul_sq_two_pow a
  exact two_pow_succ_ne_two (by omega) ht

private lemma na_0a_021 (ha : 3 ≤ a) : ¬ Adm a 0 (a + 1) 0 2 1 := by
  intro h
  have h := adm_rho h
  simp [szRho] at h
  have ht : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1) = 0 := by
    linear_combination (norm := ring_nf) h
  exact two_pow_succ_ne_zero (by omega) ht

private lemma na_0a_121 (ha : 3 ≤ a) : ¬ Adm a 0 (a + 1) 1 2 1 := by
  intro h
  have h := adm_rho h
  simp [szRho] at h
  have ht : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1) = 2 := by
    linear_combination (norm := ring_nf) -h + 2 * two_mul_sq_two_pow a
  exact two_pow_succ_ne_two (by omega) ht

private lemma na_10_232 (ha : 3 ≤ a) : ¬ Adm a 1 0 2 3 2 := by
  intro h
  have h := adm_rho h
  simp [szRho] at h
  have ht : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1) = 0 := by
    linear_combination (norm := ring_nf) h
  exact two_pow_succ_ne_zero (by omega) ht

private lemma na_10_233 (ha : 3 ≤ a) : ¬ Adm a 1 0 2 3 3 := by
  intro h
  have h := adm_rho h
  simp [szRho] at h
  have ht : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1) = 4 := by
    linear_combination (norm := ring_nf) -h
  exact two_pow_succ_ne_four ha ht

private lemma na_aa_222 (ha : 3 ≤ a) : ¬ Adm a a a 2 2 2 := by
  intro h
  have h := adm_rho h
  simp [szRho] at h
  have ht : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1) = 1 := by
    linear_combination (norm := ring_nf) -h
  exact two_pow_succ_ne_one (by omega) ht

private lemma na_aa_232 (ha : 3 ≤ a) : ¬ Adm a a a 2 3 2 := by
  intro h
  have h := adm_rho h
  simp [szRho] at h
  have ht : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1) = 0 := by
    linear_combination (norm := ring_nf) (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1) * h
  exact two_pow_succ_ne_zero (by omega) ht

private lemma na_aa_013 (ha : 3 ≤ a) : ¬ Adm a a a 0 1 3 := by
  intro h
  have h := adm_rho h
  simp [szRho] at h
  have ht : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1) = 0 := by
    linear_combination (norm := ring_nf) (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1) * h
  exact two_pow_succ_ne_zero (by omega) ht

private lemma na_aa_323 (ha : 3 ≤ a) : ¬ Adm a a a 3 2 3 := by
  intro h
  have h := adm_rho h
  simp [szRho] at h
  have ht : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1) = 1 := by
    linear_combination (norm := ring_nf) -h
  exact two_pow_succ_ne_one (by omega) ht

private lemma na_aa_233 (ha : 3 ≤ a) : ¬ Adm a a a 2 3 3 := by
  intro h
  have h := adm_rho h
  simp [szRho] at h
  have ht : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1) = 0 := by
    linear_combination (norm := ring_nf) h + two_mul_sq_two_pow a
  exact two_pow_succ_ne_zero (by omega) ht

private lemma na_aa_031 (ha : 3 ≤ a) : ¬ Adm a a a 0 3 1 := by
  intro h
  have h := adm_rho h
  simp [szRho] at h
  have ht : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1) = 0 := by
    linear_combination (norm := ring_nf) h + two_mul_sq_two_pow a
  exact two_pow_succ_ne_zero (by omega) ht

private lemma na_aa_332 (ha : 3 ≤ a) : ¬ Adm a a a 3 3 2 := by
  intro h
  have h := adm_rho h
  simp [szRho] at h
  have ht : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1) = 2 := by
    linear_combination (norm := ring_nf) -h + two_mul_sq_two_pow a
  exact two_pow_succ_ne_two (by omega) ht

private lemma na_a1_031 (ha : 3 ≤ a) : ¬ Adm a (a + 1) 0 0 3 1 := by
  intro h
  have h := adm_rho h
  simp [szRho] at h
  have ht : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1) = 0 := by
    linear_combination (norm := ring_nf) h + 2 * two_mul_sq_two_pow a
  exact two_pow_succ_ne_zero (by omega) ht

private lemma na_a1_332 (ha : 3 ≤ a) : ¬ Adm a (a + 1) 0 3 3 2 := by
  intro h
  have h := adm_rho h
  simp [szRho] at h
  have ht : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1) = 2 := by
    linear_combination (norm := ring_nf) h + 2 * two_mul_sq_two_pow a
  exact two_pow_succ_ne_two (by omega) ht

private lemma na_a1_213 (ha : 3 ≤ a) : ¬ Adm a (a + 1) 0 2 1 3 := by
  intro h
  have h := adm_rho h
  simp [szRho] at h
  have ht : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1) = 2 := by
    linear_combination (norm := ring_nf) -h
  exact two_pow_succ_ne_two (by omega) ht

private lemma na_a1_233 (ha : 3 ≤ a) : ¬ Adm a (a + 1) 0 2 3 3 := by
  intro h
  have h := adm_rho h
  simp [szRho] at h
  have ht : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1) = 0 := by
    linear_combination (norm := ring_nf) (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ a * h
  exact two_pow_succ_ne_zero (by omega) ht

private lemma na_a1_222 (ha : 3 ≤ a) : ¬ Adm a (a + 1) 0 2 2 2 := by
  intro h
  have h := adm_rho h
  simp [szRho] at h
  have ht : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1) = 2 := by
    linear_combination (norm := ring_nf) h + 2 * two_mul_sq_two_pow a
  exact two_pow_succ_ne_two (by omega) ht

private lemma na_a1_223 (ha : 3 ≤ a) : ¬ Adm a (a + 1) 0 2 2 3 := by
  intro h
  have h := adm_rho h
  simp [szRho] at h
  have ht : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a + 1) = 0 := by
    linear_combination (norm := ring_nf) h
  exact two_pow_succ_ne_zero (by omega) ht

private lemma na_2a_223 (ha : 3 ≤ a) : ¬ Adm a (2 * a) (2 * a) 2 2 3 := by
  intro h
  have h := adm_rho h
  simp [szRho] at h
  have hU : ((2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ a) ^ 2 = 1 := by
    linear_combination (norm := ring_nf) -((2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ a) * h +
      (1 + (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ a -
        ((2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ a) ^ 2) * two_mul_sq_two_pow a
  have h2a : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a * 2) = 1 := by
    rw [pow_mul]
    exact hU
  have h2a' : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (a * 2) =
      (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ 0 := by
    rw [pow_zero]
    exact h2a
  rw [two_pow_eq_two_pow_iff (f := 2 * a + 1) (by omega)] at h2a'
  rw [Nat.mul_comm a 2, Nat.mod_eq_of_lt (by omega : 2 * a < 2 * a + 1),
    Nat.zero_mod] at h2a'
  omega

private lemma na_2a_233 (ha : 3 ≤ a) : ¬ Adm a (2 * a) (2 * a) 2 3 3 := by
  intro h
  have h := adm_rho h
  simp [szRho] at h
  have ht : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ a = 2 := by
    linear_combination (norm := ring_nf) -h +
      (1 - (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ a) * two_mul_sq_two_pow a
  have h2 : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ a = (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ 1 := by
    rw [pow_one]
    exact ht
  rw [two_pow_eq_two_pow_iff (f := 2 * a + 1) (by omega)] at h2
  rw [Nat.mod_eq_of_lt (by omega : a < 2 * a + 1),
    Nat.mod_eq_of_lt (by omega : 1 < 2 * a + 1)] at h2
  omega

private lemma not_admTwist_of_not_adm {a c₁ c₂ c₃ k j : ℕ} (ha : 1 ≤ a) {r s t : Fin 4}
    (hk : (c₂ + 2 * a * c₁) % (2 * a + 1) = k)
    (hj : (c₃ + 2 * a * c₁) % (2 * a + 1) = j)
    (h : ¬ Adm a k j r s t) : ¬ AdmTwist a c₁ c₂ c₃ r s t := by
  rw [admTwist_iff_adm ha, hk, hj]
  exact h

private lemma rel_JSSJ_222 {c₁ c₂ c₃ : ℕ}
    {B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a)}
    (hB : ∀ (g : ↥(Sz a)) (v w : Fin 4 → F a),
      B (twHom a c₁ g *ᵥ v) (twHom a c₂ g *ᵥ w) = twHom a c₃ g *ᵥ B v w) :
    coef B 0 2 2 = 0 := by
  have h := coef_coord_eq hB (w a * rootSz a 1 0 ^ 2 * w a)
    (matJSSJ : Matrix (Fin 4) (Fin 4) (F a)) natHom_JSSJ matJSSJ_binary 2 2 2
  simpa [matJSSJ, Fin.sum_univ_four] using h

private lemma rel_JSSJ_213 {c₁ c₂ c₃ : ℕ}
    {B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a)}
    (hB : ∀ (g : ↥(Sz a)) (v w : Fin 4 → F a),
      B (twHom a c₁ g *ᵥ v) (twHom a c₂ g *ᵥ w) = twHom a c₃ g *ᵥ B v w) :
    coef B 0 1 3 = coef B 2 3 3 := by
  have h := coef_coord_eq hB (w a * rootSz a 1 0 ^ 2 * w a)
    (matJSSJ : Matrix (Fin 4) (Fin 4) (F a)) natHom_JSSJ matJSSJ_binary 2 1 3
  simp [matJSSJ, Fin.sum_univ_four] at h
  linear_combination (norm := char2_norm) h

private lemma rel_JSSJ_231 {c₁ c₂ c₃ : ℕ}
    {B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a)}
    (hB : ∀ (g : ↥(Sz a)) (v w : Fin 4 → F a),
      B (twHom a c₁ g *ᵥ v) (twHom a c₂ g *ᵥ w) = twHom a c₃ g *ᵥ B v w) :
    coef B 0 3 1 = coef B 2 3 3 := by
  have h := coef_coord_eq hB (w a * rootSz a 1 0 ^ 2 * w a)
    (matJSSJ : Matrix (Fin 4) (Fin 4) (F a)) natHom_JSSJ matJSSJ_binary 2 3 1
  simp [matJSSJ, Fin.sum_univ_four] at h
  linear_combination (norm := char2_norm) h

private lemma rel_JSSJ_023 {c₁ c₂ c₃ : ℕ}
    {B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a)}
    (hB : ∀ (g : ↥(Sz a)) (v w : Fin 4 → F a),
      B (twHom a c₁ g *ᵥ v) (twHom a c₂ g *ᵥ w) = twHom a c₃ g *ᵥ B v w) :
    coef B 0 2 3 = 0 := by
  have h := coef_coord_eq hB (w a * rootSz a 1 0 ^ 2 * w a)
    (matJSSJ : Matrix (Fin 4) (Fin 4) (F a)) natHom_JSSJ matJSSJ_binary 0 2 1
  simpa [matJSSJ, Fin.sum_univ_four] using h

private lemma rel_JSSJ_212 {c₁ c₂ c₃ : ℕ}
    {B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a)}
    (hB : ∀ (g : ↥(Sz a)) (v w : Fin 4 → F a),
      B (twHom a c₁ g *ᵥ v) (twHom a c₂ g *ᵥ w) = twHom a c₃ g *ᵥ B v w) :
    coef B 0 1 2 = coef B 2 3 2 := by
  have h := coef_coord_eq hB (w a * rootSz a 1 0 ^ 2 * w a)
    (matJSSJ : Matrix (Fin 4) (Fin 4) (F a)) natHom_JSSJ matJSSJ_binary 2 1 2
  simp [matJSSJ, Fin.sum_univ_four] at h
  linear_combination (norm := char2_norm) h

private lemma rel_JSSJ_033 {c₁ c₂ c₃ : ℕ}
    {B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a)}
    (hB : ∀ (g : ↥(Sz a)) (v w : Fin 4 → F a),
      B (twHom a c₁ g *ᵥ v) (twHom a c₂ g *ᵥ w) = twHom a c₃ g *ᵥ B v w) :
    coef B 0 3 3 = 0 := by
  have h := coef_coord_eq hB (w a * rootSz a 1 0 ^ 2 * w a)
    (matJSSJ : Matrix (Fin 4) (Fin 4) (F a)) natHom_JSSJ matJSSJ_binary 0 1 3
  simpa [matJSSJ, Fin.sum_univ_four] using h

private lemma rel_JSSJ_032 {c₁ c₂ c₃ : ℕ}
    {B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a)}
    (hB : ∀ (g : ↥(Sz a)) (v w : Fin 4 → F a),
      B (twHom a c₁ g *ᵥ v) (twHom a c₂ g *ᵥ w) = twHom a c₃ g *ᵥ B v w) :
    coef B 0 3 2 = 0 := by
  have h := coef_coord_eq hB (w a * rootSz a 1 0 ^ 2 * w a)
    (matJSSJ : Matrix (Fin 4) (Fin 4) (F a)) natHom_JSSJ matJSSJ_binary 0 1 2
  simpa [matJSSJ, Fin.sum_univ_four] using h

private lemma rel_JSSJ_221 {c₁ c₂ c₃ : ℕ}
    {B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a)}
    (hB : ∀ (g : ↥(Sz a)) (v w : Fin 4 → F a),
      B (twHom a c₁ g *ᵥ v) (twHom a c₂ g *ᵥ w) = twHom a c₃ g *ᵥ B v w) :
    coef B 0 2 1 = coef B 2 2 3 := by
  have h := coef_coord_eq hB (w a * rootSz a 1 0 ^ 2 * w a)
    (matJSSJ : Matrix (Fin 4) (Fin 4) (F a)) natHom_JSSJ matJSSJ_binary 2 2 1
  simp [matJSSJ, Fin.sum_univ_four] at h
  linear_combination (norm := char2_norm) h

private lemma row_zero_01 {c₁ c₂ c₃ : ℕ}
    {B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a)}
    (hB : ∀ (g : ↥(Sz a)) (v w : Fin 4 → F a),
      B (twHom a c₁ g *ᵥ v) (twHom a c₂ g *ᵥ w) = twHom a c₃ g *ᵥ B v w)
    (ha : 3 ≤ a) (hk : (c₂ + 2 * a * c₁) % (2 * a + 1) = 0)
    (hj : (c₃ + 2 * a * c₁) % (2 * a + 1) = 1) : coef B 0 0 0 = 0 := by
  have h013 : coef B 0 1 3 = 0 :=
    coef_eq_zero_of_not_adm hB (not_admTwist_of_not_adm (by omega) hk hj (na_01_013 ha))
  have h113 : coef B 1 1 3 = 0 :=
    coef_eq_zero_of_not_adm hB (not_admTwist_of_not_adm (by omega) hk hj (na_01_113 ha))
  have h333 : coef B 3 3 3 = 0 := by
    rw [rel_JSSJ_313 hB, h013, h113]
    ring
  rw [rel_J_033 hB]
  exact h333

private lemma row_zero_0a_001 {c₁ c₂ c₃ : ℕ}
    {B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a)}
    (hB : ∀ (g : ↥(Sz a)) (v w : Fin 4 → F a),
      B (twHom a c₁ g *ᵥ v) (twHom a c₂ g *ᵥ w) = twHom a c₃ g *ᵥ B v w)
    (ha : 3 ≤ a) (hk : (c₂ + 2 * a * c₁) % (2 * a + 1) = 0)
    (hj : (c₃ + 2 * a * c₁) % (2 * a + 1) = a + 1) : coef B 0 0 1 = 0 := by
  have h012 : coef B 0 1 2 = 0 :=
    coef_eq_zero_of_not_adm hB (not_admTwist_of_not_adm (by omega) hk hj (na_0a_012 ha))
  have h112 : coef B 1 1 2 = 0 :=
    coef_eq_zero_of_not_adm hB (not_admTwist_of_not_adm (by omega) hk hj (na_0a_112 ha))
  have h332 : coef B 3 3 2 = 0 := by
    rw [rel_JSSJ_312 hB, h012, h112]
    ring
  rw [rel_J_032 hB]
  exact h332

private lemma row_zero_0a_010 {c₁ c₂ c₃ : ℕ}
    {B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a)}
    (hB : ∀ (g : ↥(Sz a)) (v w : Fin 4 → F a),
      B (twHom a c₁ g *ᵥ v) (twHom a c₂ g *ᵥ w) = twHom a c₃ g *ᵥ B v w)
    (ha : 3 ≤ a) (hk : (c₂ + 2 * a * c₁) % (2 * a + 1) = 0)
    (hj : (c₃ + 2 * a * c₁) % (2 * a + 1) = a + 1) : coef B 0 1 0 = 0 := by
  have h021 : coef B 0 2 1 = 0 :=
    coef_eq_zero_of_not_adm hB (not_admTwist_of_not_adm (by omega) hk hj (na_0a_021 ha))
  have h121 : coef B 1 2 1 = 0 :=
    coef_eq_zero_of_not_adm hB (not_admTwist_of_not_adm (by omega) hk hj (na_0a_121 ha))
  have h323 : coef B 3 2 3 = 0 := by
    rw [rel_JSSJ_321 hB, h021, h121]
    ring
  rw [rel_J_023 hB]
  exact h323

private lemma row_zero_10 {c₁ c₂ c₃ : ℕ}
    {B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a)}
    (hB : ∀ (g : ↥(Sz a)) (v w : Fin 4 → F a),
      B (twHom a c₁ g *ᵥ v) (twHom a c₂ g *ᵥ w) = twHom a c₃ g *ᵥ B v w)
    (ha : 3 ≤ a) (hk : (c₂ + 2 * a * c₁) % (2 * a + 1) = 1)
    (hj : (c₃ + 2 * a * c₁) % (2 * a + 1) = 0) : coef B 0 3 0 = 0 := by
  have h232 : coef B 2 3 2 = 0 :=
    coef_eq_zero_of_not_adm hB (not_admTwist_of_not_adm (by omega) hk hj (na_10_232 ha))
  have h233 : coef B 2 3 3 = 0 :=
    coef_eq_zero_of_not_adm hB (not_admTwist_of_not_adm (by omega) hk hj (na_10_233 ha))
  rw [rel_JSSJ_230 hB, h232, h233]
  ring

private lemma row_zero_aa_002 {c₁ c₂ c₃ : ℕ}
    {B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a)}
    (hB : ∀ (g : ↥(Sz a)) (v w : Fin 4 → F a),
      B (twHom a c₁ g *ᵥ v) (twHom a c₂ g *ᵥ w) = twHom a c₃ g *ᵥ B v w)
    (ha : 3 ≤ a) (hk : (c₂ + 2 * a * c₁) % (2 * a + 1) = a)
    (hj : (c₃ + 2 * a * c₁) % (2 * a + 1) = a) : coef B 0 0 2 = 0 := by
  have h222 : coef B 2 2 2 = 0 :=
    coef_eq_zero_of_not_adm hB (not_admTwist_of_not_adm (by omega) hk hj (na_aa_222 ha))
  have h232 : coef B 2 3 2 = 0 :=
    coef_eq_zero_of_not_adm hB (not_admTwist_of_not_adm (by omega) hk hj (na_aa_232 ha))
  rw [rel_JSSJ_202 hB, h222, h232]
  ring

private lemma row_zero_aa_011 {c₁ c₂ c₃ : ℕ}
    {B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a)}
    (hB : ∀ (g : ↥(Sz a)) (v w : Fin 4 → F a),
      B (twHom a c₁ g *ᵥ v) (twHom a c₂ g *ᵥ w) = twHom a c₃ g *ᵥ B v w)
    (ha : 3 ≤ a) (hk : (c₂ + 2 * a * c₁) % (2 * a + 1) = a)
    (hj : (c₃ + 2 * a * c₁) % (2 * a + 1) = a) : coef B 0 1 1 = 0 := by
  have h013 : coef B 0 1 3 = 0 :=
    coef_eq_zero_of_not_adm hB (not_admTwist_of_not_adm (by omega) hk hj (na_aa_013 ha))
  have h323 : coef B 3 2 3 = 0 :=
    coef_eq_zero_of_not_adm hB (not_admTwist_of_not_adm (by omega) hk hj (na_aa_323 ha))
  have h213 : coef B 2 1 3 = 0 := by
    rw [rel_JSJ_313 hB, h013, h323]
    ring
  have h031 : coef B 0 3 1 = 0 :=
    coef_eq_zero_of_not_adm hB (not_admTwist_of_not_adm (by omega) hk hj (na_aa_031 ha))
  have h332 : coef B 3 3 2 = 0 :=
    coef_eq_zero_of_not_adm hB (not_admTwist_of_not_adm (by omega) hk hj (na_aa_332 ha))
  have h231 : coef B 2 3 1 = 0 := by
    rw [rel_JSJ_331 hB, h031, h332]
    ring
  have h233 : coef B 2 3 3 = 0 :=
    coef_eq_zero_of_not_adm hB (not_admTwist_of_not_adm (by omega) hk hj (na_aa_233 ha))
  rw [rel_JSSJ_211 hB, h213, h231, h233]
  ring

private lemma row_zero_a1_011 {c₁ c₂ c₃ : ℕ}
    {B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a)}
    (hB : ∀ (g : ↥(Sz a)) (v w : Fin 4 → F a),
      B (twHom a c₁ g *ᵥ v) (twHom a c₂ g *ᵥ w) = twHom a c₃ g *ᵥ B v w)
    (ha : 3 ≤ a) (hk : (c₂ + 2 * a * c₁) % (2 * a + 1) = a + 1)
    (hj : (c₃ + 2 * a * c₁) % (2 * a + 1) = 0) : coef B 0 1 1 = 0 := by
  have h031 : coef B 0 3 1 = 0 :=
    coef_eq_zero_of_not_adm hB (not_admTwist_of_not_adm (by omega) hk hj (na_a1_031 ha))
  have h332 : coef B 3 3 2 = 0 :=
    coef_eq_zero_of_not_adm hB (not_admTwist_of_not_adm (by omega) hk hj (na_a1_332 ha))
  have h231 : coef B 2 3 1 = 0 := by
    rw [rel_JSJ_331 hB, h031, h332]
    ring
  have h213 : coef B 2 1 3 = 0 :=
    coef_eq_zero_of_not_adm hB (not_admTwist_of_not_adm (by omega) hk hj (na_a1_213 ha))
  have h233 : coef B 2 3 3 = 0 :=
    coef_eq_zero_of_not_adm hB (not_admTwist_of_not_adm (by omega) hk hj (na_a1_233 ha))
  rw [rel_JSSJ_211 hB, h213, h231, h233]
  ring

private lemma row_zero_a1_020 {c₁ c₂ c₃ : ℕ}
    {B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a)}
    (hB : ∀ (g : ↥(Sz a)) (v w : Fin 4 → F a),
      B (twHom a c₁ g *ᵥ v) (twHom a c₂ g *ᵥ w) = twHom a c₃ g *ᵥ B v w)
    (ha : 3 ≤ a) (hk : (c₂ + 2 * a * c₁) % (2 * a + 1) = a + 1)
    (hj : (c₃ + 2 * a * c₁) % (2 * a + 1) = 0) : coef B 0 2 0 = 0 := by
  have h222 : coef B 2 2 2 = 0 :=
    coef_eq_zero_of_not_adm hB (not_admTwist_of_not_adm (by omega) hk hj (na_a1_222 ha))
  have h223 : coef B 2 2 3 = 0 :=
    coef_eq_zero_of_not_adm hB (not_admTwist_of_not_adm (by omega) hk hj (na_a1_223 ha))
  rw [rel_JSSJ_220 hB, h222, h223]
  ring

private lemma row_zero_2a_003 {c₁ c₂ c₃ : ℕ}
    {B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a)}
    (hB : ∀ (g : ↥(Sz a)) (v w : Fin 4 → F a),
      B (twHom a c₁ g *ᵥ v) (twHom a c₂ g *ᵥ w) = twHom a c₃ g *ᵥ B v w)
    (ha : 3 ≤ a) (hk : (c₂ + 2 * a * c₁) % (2 * a + 1) = 2 * a)
    (hj : (c₃ + 2 * a * c₁) % (2 * a + 1) = 2 * a) : coef B 0 0 3 = 0 := by
  have h223 : coef B 2 2 3 = 0 :=
    coef_eq_zero_of_not_adm hB (not_admTwist_of_not_adm (by omega) hk hj (na_2a_223 ha))
  have h233 : coef B 2 3 3 = 0 :=
    coef_eq_zero_of_not_adm hB (not_admTwist_of_not_adm (by omega) hk hj (na_2a_233 ha))
  rw [rel_JSSJ_203 hB, h223, h233]
  ring

private lemma row_zero_three_le {c₁ c₂ c₃ : ℕ}
    {B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a)}
    (hB : ∀ (g : ↥(Sz a)) (v w : Fin 4 → F a),
      B (twHom a c₁ g *ᵥ v) (twHom a c₂ g *ᵥ w) = twHom a c₃ g *ᵥ B v w)
    (ha : 3 ≤ a) : ∀ s t : Fin 4, coef B 0 s t = 0 := by
  have hn : 0 < 2 * a + 1 := by omega
  have h1a : 1 ≤ a := by omega
  intro s t
  by_cases hst : coef B 0 s t = 0
  · exact hst
  have hAdmTw : AdmTwist a c₁ c₂ c₃ 0 s t := admTwist_of_coef_ne_zero hB hst
  have hAdm : Adm a ((c₂ + 2 * a * c₁) % (2 * a + 1))
      ((c₃ + 2 * a * c₁) % (2 * a + 1)) 0 s t :=
    (admTwist_iff_adm h1a 0 s t).mp hAdmTw
  have hkB : (c₂ + 2 * a * c₁) % (2 * a + 1) < 2 * a + 1 := Nat.mod_lt _ hn
  have hjB : (c₃ + 2 * a * c₁) % (2 * a + 1) < 2 * a + 1 := Nat.mod_lt _ hn
  rcases adm_row_zero_of_three_le ha hkB hjB hAdm with h1 | h2 | h3 | h4 | h5 | h6
  · rcases h1 with ⟨hk, hj, hs, ht⟩
    rw [hs, ht] at hst ⊢
    exact absurd (row_zero_01 hB ha hk hj) hst
  · rcases h2 with ⟨hk, hj, hst'⟩
    rcases hst' with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · rw [hs, ht] at hst ⊢
      exact absurd (row_zero_0a_001 hB ha hk hj) hst
    · rw [hs, ht] at hst ⊢
      exact absurd (row_zero_0a_010 hB ha hk hj) hst
  · rcases h3 with ⟨hk, hj, hs, ht⟩
    rw [hs, ht] at hst ⊢
    exact absurd (row_zero_10 hB ha hk hj) hst
  · rcases h4 with ⟨hk, hj, hst'⟩
    rcases hst' with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · rw [hs, ht] at hst ⊢
      exact absurd (row_zero_aa_002 hB ha hk hj) hst
    · rw [hs, ht] at hst ⊢
      exact absurd (row_zero_aa_011 hB ha hk hj) hst
  · rcases h5 with ⟨hk, hj, hst'⟩
    rcases hst' with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · rw [hs, ht] at hst ⊢
      exact absurd (row_zero_a1_011 hB ha hk hj) hst
    · rw [hs, ht] at hst ⊢
      exact absurd (row_zero_a1_020 hB ha hk hj) hst
  · rcases h6 with ⟨hk, hj, hs, ht⟩
    rw [hs, ht] at hst ⊢
    exact absurd (row_zero_2a_003 hB ha hk hj) hst

private lemma row_zero_one {c₁ c₂ c₃ : ℕ}
    {B : (Fin 4 → F 1) →ₗ[F 1] (Fin 4 → F 1) →ₗ[F 1] (Fin 4 → F 1)}
    (hB : ∀ (g : ↥(Sz 1)) (v w : Fin 4 → F 1),
      B (twHom 1 c₁ g *ᵥ v) (twHom 1 c₂ g *ᵥ w) = twHom 1 c₃ g *ᵥ B v w) :
    ∀ s t : Fin 4, coef B 0 s t = 0 := by
  have h1a : 1 ≤ 1 := by omega
  intro s t
  by_cases hst : coef B 0 s t = 0
  · exact hst
  have hAdmTw : AdmTwist 1 c₁ c₂ c₃ 0 s t := admTwist_of_coef_ne_zero hB hst
  set k := (c₂ + 2 * 1 * c₁) % (2 * 1 + 1) with hk
  set j := (c₃ + 2 * 1 * c₁) % (2 * 1 + 1) with hj
  have hAdm : Adm 1 k j 0 s t := by
    rw [hk, hj]
    exact (admTwist_iff_adm h1a 0 s t).mp hAdmTw
  have hkB : k < 2 * 1 + 1 := by rw [hk]; exact Nat.mod_lt _ (by omega)
  have hjB : j < 2 * 1 + 1 := by rw [hj]; exact Nat.mod_lt _ (by omega)
  have hk' : (c₂ + 2 * 1 * c₁) % (2 * 1 + 1) = k := hk.symm
  have hj' : (c₃ + 2 * 1 * c₁) % (2 * 1 + 1) = j := hj.symm
  interval_cases k <;> interval_cases j
  ·
    fin_cases s <;> fin_cases t <;>
      first
      | exact absurd hAdm (by unfold Adm szWt; decide)
      | simp [rel_JSSJ_222 hB]
  ·
    have h113 : coef B 1 1 3 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    have h233 : coef B 2 3 3 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    fin_cases s <;> fin_cases t <;>
      first
      | exact absurd hAdm (by unfold Adm szWt; decide)
      | simp [rel_J_033 hB, rel_JSSJ_313 hB, rel_JSSJ_213 hB, rel_JSSJ_231 hB, h113, h233]
  ·
    have h012 : coef B 0 1 2 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    have h112 : coef B 1 1 2 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    have h021 : coef B 0 2 1 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    have h121 : coef B 1 2 1 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    fin_cases s <;> fin_cases t <;>
      first
      | exact absurd hAdm (by unfold Adm szWt; decide)
      | simp [rel_J_032 hB, rel_JSSJ_312 hB, rel_J_023 hB, rel_JSSJ_321 hB, h012, h112, h021, h121]
  ·
    have h031 : coef B 0 3 1 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    have h232 : coef B 2 3 2 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    have h233 : coef B 2 3 3 = 0 := by
      rw [← rel_JSSJ_231 hB]
      exact h031
    fin_cases s <;> fin_cases t <;>
      first
      | exact absurd hAdm (by unfold Adm szWt; decide)
      | simp [rel_JSSJ_213 hB, rel_JSSJ_230 hB, h232, h233]
  ·
    have h013 : coef B 0 1 3 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    have h222 : coef B 2 2 2 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    have h231 : coef B 2 3 1 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    have h232 : coef B 2 3 2 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    have h233 : coef B 2 3 3 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    have h323 : coef B 3 2 3 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    fin_cases s <;> fin_cases t <;>
      first
      | exact absurd hAdm (by unfold Adm szWt; decide)
      | simp [rel_JSSJ_202 hB, rel_JSJ_313 hB, rel_JSSJ_211 hB, rel_JSSJ_023 hB, h013, h222, h231,
          h232, h233, h323]
  ·
    have h232 : coef B 2 3 2 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    fin_cases s <;> fin_cases t <;>
      first
      | exact absurd hAdm (by unfold Adm szWt; decide)
      | simp [rel_JSSJ_212 hB, rel_JSSJ_033 hB, h232]
  ·
    have h031 : coef B 0 3 1 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    have h213 : coef B 2 1 3 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    have h222 : coef B 2 2 2 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    have h223 : coef B 2 2 3 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    have h233 : coef B 2 3 3 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    have h332 : coef B 3 3 2 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    fin_cases s <;> fin_cases t <;>
      first
      | exact absurd hAdm (by unfold Adm szWt; decide)
      | simp [rel_JSJ_331 hB, rel_JSSJ_211 hB, rel_JSSJ_220 hB, rel_JSSJ_032 hB, h031, h213, h222,
          h223, h233, h332]
  ·
    have h223 : coef B 2 2 3 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    fin_cases s <;> fin_cases t <;>
      first
      | exact absurd hAdm (by unfold Adm szWt; decide)
      | simp [rel_JSSJ_221 hB, rel_JSSJ_033 hB, h223]
  ·
    have h013 : coef B 0 1 3 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    have h223 : coef B 2 2 3 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    have h233 : coef B 2 3 3 = 0 := by
      rw [← rel_JSSJ_213 hB]
      exact h013
    fin_cases s <;> fin_cases t <;>
      first
      | exact absurd hAdm (by unfold Adm szWt; decide)
      | simp [rel_JSSJ_203 hB, rel_JSSJ_231 hB, h223, h233]

private lemma row_zero_two {c₁ c₂ c₃ : ℕ}
    {B : (Fin 4 → F 2) →ₗ[F 2] (Fin 4 → F 2) →ₗ[F 2] (Fin 4 → F 2)}
    (hB : ∀ (g : ↥(Sz 2)) (v w : Fin 4 → F 2),
      B (twHom 2 c₁ g *ᵥ v) (twHom 2 c₂ g *ᵥ w) = twHom 2 c₃ g *ᵥ B v w) :
    ∀ s t : Fin 4, coef B 0 s t = 0 := by
  have h1a : 1 ≤ 2 := by omega
  intro s t
  by_cases hst : coef B 0 s t = 0
  · exact hst
  have hAdmTw : AdmTwist 2 c₁ c₂ c₃ 0 s t := admTwist_of_coef_ne_zero hB hst
  set k := (c₂ + 2 * 2 * c₁) % (2 * 2 + 1) with hk
  set j := (c₃ + 2 * 2 * c₁) % (2 * 2 + 1) with hj
  have hAdm : Adm 2 k j 0 s t := by
    rw [hk, hj]
    exact (admTwist_iff_adm h1a 0 s t).mp hAdmTw
  have hkB : k < 2 * 2 + 1 := by rw [hk]; exact Nat.mod_lt _ (by omega)
  have hjB : j < 2 * 2 + 1 := by rw [hj]; exact Nat.mod_lt _ (by omega)
  have hk' : (c₂ + 2 * 2 * c₁) % (2 * 2 + 1) = k := hk.symm
  have hj' : (c₃ + 2 * 2 * c₁) % (2 * 2 + 1) = j := hj.symm
  interval_cases k <;> interval_cases j
  ·
    fin_cases s <;> fin_cases t <;>
      exact absurd hAdm (by unfold Adm szWt; decide)
  ·
    have h013 : coef B 0 1 3 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    have h113 : coef B 1 1 3 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    fin_cases s <;> fin_cases t <;>
      first
      | exact absurd hAdm (by unfold Adm szWt; decide)
      | simp [rel_J_033 hB, rel_JSSJ_313 hB, h013, h113]
  ·
    fin_cases s <;> fin_cases t <;>
      exact absurd hAdm (by unfold Adm szWt; decide)
  ·
    have h012 : coef B 0 1 2 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    have h112 : coef B 1 1 2 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    have h021 : coef B 0 2 1 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    have h121 : coef B 1 2 1 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    fin_cases s <;> fin_cases t <;>
      first
      | exact absurd hAdm (by unfold Adm szWt; decide)
      | simp [rel_J_032 hB, rel_JSSJ_312 hB, rel_J_023 hB, rel_JSSJ_321 hB, h012, h112, h021, h121]
  ·
    fin_cases s <;> fin_cases t <;>
      exact absurd hAdm (by unfold Adm szWt; decide)
  ·
    have h232 : coef B 2 3 2 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    have h233 : coef B 2 3 3 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    fin_cases s <;> fin_cases t <;>
      first
      | exact absurd hAdm (by unfold Adm szWt; decide)
      | simp [rel_JSSJ_230 hB, h232, h233]
  ·
    fin_cases s <;> fin_cases t <;>
      exact absurd hAdm (by unfold Adm szWt; decide)
  ·
    fin_cases s <;> fin_cases t <;>
      exact absurd hAdm (by unfold Adm szWt; decide)
  ·
    fin_cases s <;> fin_cases t <;>
      exact absurd hAdm (by unfold Adm szWt; decide)
  ·
    fin_cases s <;> fin_cases t <;>
      first
      | exact absurd hAdm (by unfold Adm szWt; decide)
      | simp [rel_JSSJ_032 hB]
  ·
    fin_cases s <;> fin_cases t <;>
      exact absurd hAdm (by unfold Adm szWt; decide)
  ·
    fin_cases s <;> fin_cases t <;>
      first
      | exact absurd hAdm (by unfold Adm szWt; decide)
      | simp [rel_JSSJ_032 hB]
  ·
    have h013 : coef B 0 1 3 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    have h222 : coef B 2 2 2 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    have h231 : coef B 2 3 1 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    have h232 : coef B 2 3 2 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    have h233 : coef B 2 3 3 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    have h323 : coef B 3 2 3 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    fin_cases s <;> fin_cases t <;>
      first
      | exact absurd hAdm (by unfold Adm szWt; decide)
      | simp [rel_JSSJ_202 hB, rel_JSJ_313 hB, rel_JSSJ_211 hB, h013, h222, h231, h232, h233, h323]
  ·
    fin_cases s <;> fin_cases t <;>
      exact absurd hAdm (by unfold Adm szWt; decide)
  ·
    fin_cases s <;> fin_cases t <;>
      exact absurd hAdm (by unfold Adm szWt; decide)
  ·
    have h031 : coef B 0 3 1 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    have h213 : coef B 2 1 3 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    have h222 : coef B 2 2 2 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    have h223 : coef B 2 2 3 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    have h233 : coef B 2 3 3 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    have h332 : coef B 3 3 2 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    fin_cases s <;> fin_cases t <;>
      first
      | exact absurd hAdm (by unfold Adm szWt; decide)
      | simp [rel_JSJ_331 hB, rel_JSSJ_211 hB, rel_JSSJ_220 hB, h031, h213, h222, h223, h233, h332]
  ·
    fin_cases s <;> fin_cases t <;>
      exact absurd hAdm (by unfold Adm szWt; decide)
  ·
    fin_cases s <;> fin_cases t <;>
      exact absurd hAdm (by unfold Adm szWt; decide)
  ·
    fin_cases s <;> fin_cases t <;>
      exact absurd hAdm (by unfold Adm szWt; decide)
  ·
    fin_cases s <;> fin_cases t <;>
      first
      | exact absurd hAdm (by unfold Adm szWt; decide)
      | simp [rel_JSSJ_023 hB]
  ·
    fin_cases s <;> fin_cases t <;>
      exact absurd hAdm (by unfold Adm szWt; decide)
  ·
    fin_cases s <;> fin_cases t <;>
      exact absurd hAdm (by unfold Adm szWt; decide)
  ·
    fin_cases s <;> fin_cases t <;>
      exact absurd hAdm (by unfold Adm szWt; decide)
  ·
    fin_cases s <;> fin_cases t <;>
      first
      | exact absurd hAdm (by unfold Adm szWt; decide)
      | simp [rel_JSSJ_023 hB]
  ·
    have h223 : coef B 2 2 3 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    have h233 : coef B 2 3 3 = 0 := by
      apply coef_eq_zero_of_not_adm hB
      rw [admTwist_iff_adm h1a, hk', hj']
      unfold Adm szWt
      decide
    fin_cases s <;> fin_cases t <;>
      first
      | exact absurd hAdm (by unfold Adm szWt; decide)
      | simp [rel_JSSJ_203 hB, h223, h233]

theorem bilin_eq_zero_of_twisted_equivariant {a : ℕ} (ha : 1 ≤ a) (c₁ c₂ c₃ : ℕ)
    (B : (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a) →ₗ[F a] (Fin 4 → F a))
    (hB : ∀ (g : ↥(Sz a)) (v w : Fin 4 → F a),
      B (twHom a c₁ g *ᵥ v) (twHom a c₂ g *ᵥ w) = twHom a c₃ g *ᵥ B v w) :
    B = 0 := by
  by_cases h3 : 3 ≤ a
  · refine LinearMap.ext fun v => LinearMap.ext fun w => ?_
    exact eq_zero_of_row_zero hB (row_zero_three_le hB h3) v w
  · have h12 : a = 1 ∨ a = 2 := by omega
    rcases h12 with rfl | rfl
    · refine LinearMap.ext fun v => LinearMap.ext fun w => ?_
      exact eq_zero_of_row_zero hB (row_zero_one hB) v w
    · refine LinearMap.ext fun v => LinearMap.ext fun w => ?_
      exact eq_zero_of_row_zero hB (row_zero_two hB) v w

end CFSG.RepresentationTheory.SzMartineau
