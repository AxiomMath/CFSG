module

public import CFSG.RankThree.GF2n.Smith81.OrthTensorNormFix
public import CFSG.RankThree.GF2n.Smith81.OrthTensorNormRank
public import CFSG.RankThree.GF2n.Smith81.OrthTensorNormCube
public import CFSG.RankThree.GF2n.Smith81.OrthTensorNormFactors

public section

open scoped Matrix

namespace CFSG.RankThree.GF2n.Smith81.OrthTN

section Heart

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def cubeRk (x : Cube 3 K ≃ₗ[K] Cube 3 K) : ℕ :=
  Module.finrank K (LinearMap.range ((x : Cube 3 K →ₗ[K] Cube 3 K) - LinearMap.id))

theorem cubeRk_conj (g x : Cube 3 K ≃ₗ[K] Cube 3 K) : cubeRk (g * x * g⁻¹) = cubeRk x := by
  unfold cubeRk
  have h1 : (((g * x * g⁻¹ : Cube 3 K ≃ₗ[K] Cube 3 K)) : Cube 3 K →ₗ[K] Cube 3 K) - LinearMap.id =
      (g : Cube 3 K →ₗ[K] Cube 3 K) ∘ₗ (((x : Cube 3 K →ₗ[K] Cube 3 K) - LinearMap.id) ∘ₗ
        (g⁻¹ : Cube 3 K ≃ₗ[K] Cube 3 K).toLinearMap) := by
    refine LinearMap.ext fun v => ?_
    simp
  rw [h1, LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top]
  · exact LinearEquiv.finrank_map_eq g _
  · exact LinearMap.range_eq_top.mpr (g⁻¹).surjective

theorem b7b_heart_data (hq : 4 ≤ Nat.card K) (T : Cube 3 K ≃ₗ[K] Cube 3 K)
    (hE : ∀ x ∈ cubeE 3 K, T * x * T⁻¹ ∈ cubeE 3 K)
    (hE' : ∀ x ∈ cubeE 3 K, T⁻¹ * x * T ∈ cubeE 3 K)
    (hU' : ∀ x ∈ cubeU 3 K, T⁻¹ * x * T ∈ cubeU 3 K)
    (hT2 : T * T ∈ cubeU 3 K) :
    ∃ (π : Equiv.Perm (Fin 3)) (h : Fin 3 → Matrix (Fin 2) (Fin 2) K), π * π = 1 ∧
      (∀ i, IsUnit (h i).det) ∧ (∀ i, h i 1 0 = 0) ∧
      ∀ v, T v = kronMap h (permMap π v) := by
  have hF := threeFactors hq (K := K)
  obtain ⟨π, hπ⟩ := hF.exists_perm T hE hE'
  have hL3 : ∀ i : Fin 3, ∀ A : Matrix (Fin 2) (Fin 2) K, A.det = 1 →
      ∃ A' : Matrix (Fin 2) (Fin 2) K, A'.det = 1 ∧
        ∀ v, T (actMap i A v) = actMap (π i) A' (T v) := by
    intro i A hA
    have hx := actSL_mem i (mkSL A hA)
    have h1 := (hπ i _).mp hx
    obtain ⟨A', hA', hv⟩ := mem_cubeF.mp h1
    refine ⟨A', hA', fun v => ?_⟩
    have h2 := hv (T v)
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      show T⁻¹ (T v) = v from T.symm_apply_apply v, actSL_apply] at h2
    exact h2
  obtain ⟨h, hunit, hTh⟩ := exists_kron_perm T π hL3
  refine ⟨π, h, ?_, hunit, ?_, hTh⟩
  · have heE : T * T ∈ cubeE 3 K := cubeU_le_cubeE hT2
    refine Equiv.ext fun i => ?_
    by_contra hne
    have hne' : i ≠ π (π i) := fun h' => hne h'.symm
    apply hF.ne hne'
    refine Subgroup.ext fun g => ?_
    have e1 : T * (T * g * T⁻¹) * T⁻¹ = (T * T) * g * (T * T)⁻¹ := by group
    rw [hπ i g, hπ (π i) (T * g * T⁻¹), e1, ← hF.conj_iff (π (π i)) heE g]
  · have hfix : ∀ g ∈ cubeU 3 K, g (T (cubeZero 3 K)) = T (cubeZero 3 K) := by
      intro g hg
      obtain ⟨β, hβ⟩ := mem_cubeU.mp (hU' g hg)
      have h1 : (T⁻¹ * g * T) (cubeZero 3 K) = cubeZero 3 K := by
        rw [hβ, kronMap_uni_cubeZero]
      have h2 := congrArg T h1
      simpa using h2
    obtain ⟨c, hc⟩ := fixed_of_cubeU (T (cubeZero 3 K)) hfix
    refine upper_of_kron_cubeZero h hunit c ?_
    have hz : T (cubeZero 3 K) = kronMap h (cubeZero 3 K) := by
      rw [hTh, permMap_cubeZero]
    rw [← hz]
    exact hc

theorem b7b_card_eq_two_pow (hq : 4 ≤ Nat.card K) : ∃ k : ℕ, 2 ≤ k ∧ Nat.card K = 2 ^ k := by
  haveI := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  refine ⟨(n : ℕ), ?_, by rw [Nat.card_eq_fintype_card, hn]⟩
  by_contra hlt
  have hn1 : (n : ℕ) ≤ 1 := by omega
  have : 2 ^ (n : ℕ) ≤ 2 := by
    calc 2 ^ (n : ℕ) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn1
      _ = 2 := by norm_num
  rw [Nat.card_eq_fintype_card, hn] at hq
  omega

theorem b7b_pow_upper_entries (A : Matrix (Fin 2) (Fin 2) K) (h10 : A 1 0 = 0) (m : ℕ) :
    (A ^ m) 1 0 = 0 ∧ (A ^ m) 0 0 = (A 0 0) ^ m ∧ (A ^ m) 1 1 = (A 1 1) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [pow_succ]
    refine ⟨?_, ?_, ?_⟩
    · simp [Matrix.mul_apply, Fin.sum_univ_two, h1, h10]
    · simp [Matrix.mul_apply, Fin.sum_univ_two, h2, h10, pow_succ]
    · simp [Matrix.mul_apply, Fin.sum_univ_two, h1, h3, h10, pow_succ]

theorem b7b_upper_pow_card_sub_one (A : Matrix (Fin 2) (Fin 2) K) (h10 : A 1 0 = 0)
    (hdet : IsUnit A.det) :
    A ^ (Nat.card K - 1) = uniMat ((A ^ (Nat.card K - 1)) 0 1) := by
  haveI := Fintype.ofFinite K
  obtain ⟨e1, e2, e3⟩ := b7b_pow_upper_entries A h10 (Nat.card K - 1)
  have hd : A.det = A 0 0 * A 1 1 := by
    rw [Matrix.det_fin_two, h10]; ring
  have ha : A 0 0 ≠ 0 := fun h => hdet.ne_zero (by rw [hd, h, zero_mul])
  have hd' : A 1 1 ≠ 0 := fun h => hdet.ne_zero (by rw [hd, h, mul_zero])
  have hq : Nat.card K - 1 = Fintype.card K - 1 := by rw [Nat.card_eq_fintype_card]
  rw [hq] at e1 e2 e3 ⊢
  rw [FiniteField.pow_card_sub_one_eq_one _ ha] at e2
  rw [FiniteField.pow_card_sub_one_eq_one _ hd'] at e3
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uniMat, e1, e2, e3]

theorem b7b_kronMap_pow_apply (T : Cube 3 K ≃ₗ[K] Cube 3 K) (h : Fin 3 → Matrix (Fin 2) (Fin 2) K)
    (hTh : ∀ v, T v = kronMap h v) (m : ℕ) (v : Cube 3 K) :
    (T ^ m) v = kronMap (fun i => (h i) ^ m) v := by
  induction m generalizing v with
  | zero =>
    rw [pow_zero]
    have : (fun i => (h i) ^ 0) = (1 : Fin 3 → Matrix (Fin 2) (Fin 2) K) := by
      funext i; simp
    rw [this, kronMap_one]
    rfl
  | succ m ih =>
    rw [pow_succ, LinearEquiv.mul_apply, hTh, ih]
    have : (fun i => (h i) ^ (m + 1)) = (fun i => (h i) ^ m) * h := by
      funext i; simp [pow_succ]
    rw [this, kronMap_mul]
    rfl

theorem b7b_mem_cubeU_of_upper (hq : 4 ≤ Nat.card K) (T : Cube 3 K ≃ₗ[K] Cube 3 K)
    (h : Fin 3 → Matrix (Fin 2) (Fin 2) K) (hunit : ∀ i, IsUnit (h i).det)
    (hup : ∀ i, h i 1 0 = 0) (hTh : ∀ v, T v = kronMap h v)
    (hT2 : T * T ∈ cubeU 3 K) : T ∈ cubeU 3 K := by
  have hpow : T ^ (Nat.card K - 1) ∈ cubeU 3 K := by
    refine mem_cubeU.mpr ⟨fun i => ((h i) ^ (Nat.card K - 1)) 0 1, fun v => ?_⟩
    rw [b7b_kronMap_pow_apply T h hTh]
    congr 2
    funext i
    exact b7b_upper_pow_card_sub_one (h i) (hup i) (hunit i)
  have h4 : T ^ 4 = 1 := by
    have := cubeU_mul_self hT2
    calc T ^ 4 = (T * T) * (T * T) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := this
  obtain ⟨k, hk, hqk⟩ := b7b_card_eq_two_pow hq
  have hmod : Nat.card K - 1 = 4 * (2 ^ (k - 2) - 1) + 3 := by
    have h1 : 2 ^ k = 4 * 2 ^ (k - 2) := by
      have : k = (k - 2) + 2 := by omega
      conv_lhs => rw [this]
      rw [pow_add]; ring
    have h2 : 1 ≤ 2 ^ (k - 2) := Nat.one_le_two_pow
    rw [hqk, h1]
    omega
  rw [hmod, pow_add, pow_mul, h4, one_pow, one_mul] at hpow
  have h3 : T ^ 3 = T⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    calc T ^ 3 * T = T ^ 4 := by group
      _ = 1 := h4
  rw [h3] at hpow
  exact (inv_mem_iff).mp hpow

theorem b7b_diag_rel {π : Equiv.Perm (Fin 3)} (hππ : π * π = 1)
    {h : Fin 3 → Matrix (Fin 2) (Fin 2) K}
    (hup : ∀ i, h i 1 0 = 0) {T : Cube 3 K ≃ₗ[K] Cube 3 K}
    (hTh : ∀ v, T v = kronMap h (permMap π v)) (hT2 : T * T ∈ cubeU 3 K)
    (y : Fin 3 → Fin 2) : ∏ i, (h i (y i) (y i) * h (π i) (y i) (y i)) = 1 := by
  obtain ⟨β, hβ⟩ := mem_cubeU.mp hT2
  have h1 : kronMap (fun i => h i * h (π i)) (Pi.single y 1) y =
      kronMap (fun i => uniMat (β i)) (Pi.single y 1) y := by
    rw [← sq_eq_kron π hππ h T hTh, hβ]
  rw [kronMap_basis, kronMap_basis] at h1
  have h2 : ∏ i, uniMat (β i) (y i) (y i) = 1 :=
    Finset.prod_eq_one fun i _ => uniMat_diag _ _
  rw [h2] at h1
  rw [← h1]
  exact Finset.prod_congr rfl fun i _ => (mul_diag_of_upper (hup i) (hup (π i)) (y i)).symm

theorem b7b_diag_rel_i {π : Equiv.Perm (Fin 3)} {h : Fin 3 → Matrix (Fin 2) (Fin 2) K}
    (hrel : ∀ y : Fin 3 → Fin 2, ∏ i, (h i (y i) (y i) * h (π i) (y i) (y i)) = 1)
    (i : Fin 3) : h i 0 0 * h (π i) 0 0 = h i 1 1 * h (π i) 1 1 := by
  have h0 := hrel (fun _ => 0)
  have h1 := hrel (Function.update (fun _ => 0) i 1)
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)] at h0 h1
  simp only [Function.update_self] at h1
  have hP : ∏ j ∈ Finset.univ.erase i,
      (h j (Function.update (fun _ : Fin 3 => (0 : Fin 2)) i 1 j)
          (Function.update (fun _ : Fin 3 => (0 : Fin 2)) i 1 j) *
        h (π j) (Function.update (fun _ : Fin 3 => (0 : Fin 2)) i 1 j)
          (Function.update (fun _ : Fin 3 => (0 : Fin 2)) i 1 j)) =
      ∏ j ∈ Finset.univ.erase i, (h j 0 0 * h (π j) 0 0) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hP] at h1
  have hP0 : ∏ j ∈ Finset.univ.erase i, (h j 0 0 * h (π j) 0 0) ≠ 0 := by
    intro h'
    rw [h', mul_zero] at h0
    exact zero_ne_one h0
  exact mul_right_cancel₀ hP0 (h0.trans h1.symm)

theorem b7b_heart_normal_form (T : Cube 3 K ≃ₗ[K] Cube 3 K) (π : Equiv.Perm (Fin 3))
    (hππ : π * π = 1) (h : Fin 3 → Matrix (Fin 2) (Fin 2) K) (hunit : ∀ i, IsUnit (h i).det)
    (hup : ∀ i, h i 1 0 = 0) (hTh : ∀ v, T v = kronMap h (permMap π v))
    (hT2 : T * T ∈ cubeU 3 K) :
    ∃ g' ∈ cubeU 3 K, ∀ v, (g'⁻¹ * T) v =
      kronMap (fun i => dgMat (h i 0 0) (h i 1 1)) (permMap π v) := by
  obtain ⟨g', hg'U, hg'⟩ := exists_cubeU_apply (fun i => h i 0 1 / h i 1 1)
  refine ⟨g', hg'U, fun v => ?_⟩
  have e1 : h = (fun i => uniMat (h i 0 1 / h i 1 1)) * (fun i => dgMat (h i 0 0) (h i 1 1)) := by
    funext i
    exact upper_eq_uni_mul_dg (h i) (hup i) (upper_ne_zero (hup i) (hunit i)).2
  have e2 : T v = g' (kronMap (fun i => dgMat (h i 0 0) (h i 1 1)) (permMap π v)) := by
    rw [hTh, hg']
    conv_lhs => rw [e1]
    rw [kronMap_mul]
    rfl
  rw [LinearEquiv.mul_apply, e2]
  exact g'.symm_apply_apply _

theorem b7b_heart_sq_one (T : Cube 3 K ≃ₗ[K] Cube 3 K) (π : Equiv.Perm (Fin 3))
    (hππ : π * π = 1) (h : Fin 3 → Matrix (Fin 2) (Fin 2) K)
    (hrel : ∀ y : Fin 3 → Fin 2, ∏ i, (h i (y i) (y i) * h (π i) (y i) (y i)) = 1)
    (X : Cube 3 K ≃ₗ[K] Cube 3 K)
    (hX : ∀ v, X v = kronMap (fun i => dgMat (h i 0 0) (h i 1 1)) (permMap π v)) :
    X * X = 1 := by
  refine LinearEquiv.ext fun v => ?_
  rw [sq_eq_kron π hππ (fun i => dgMat (h i 0 0) (h i 1 1)) X hX v]
  have hκ := b7b_diag_rel_i hrel
  have e1 : (fun i => dgMat (h i 0 0) (h i 1 1) * dgMat (h (π i) 0 0) (h (π i) 1 1)) =
      fun i => (h i 0 0 * h (π i) 0 0) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    funext i
    rw [dgMat_mul, ← hκ i, dgMat_scalar]
  have e2 := kronMap_smul_pi
    (fun i => dgMat (h i 0 0) (h i 1 1) * dgMat (h (π i) 0 0) (h (π i) 1 1))
    (fun _ => (1 : Matrix (Fin 2) (Fin 2) K)) (fun i => h i 0 0 * h (π i) 0 0)
    (fun i => congrFun e1 i)
  have e3 : (∏ i, (h i 0 0 * h (π i) 0 0)) = 1 := hrel (fun _ => 0)
  rw [e2, e3, one_smul]
  have : (fun _ : Fin 3 => (1 : Matrix (Fin 2) (Fin 2) K)) = 1 := rfl
  rw [this, kronMap_one]
  rfl

theorem b7b_exists_labels {π : Equiv.Perm (Fin 3)} (hππ : π * π = 1) (hπ1 : π ≠ 1) :
    ∃ x a b : Fin 3, x ≠ a ∧ x ≠ b ∧ a ≠ b ∧ π x = x ∧ π a = b ∧ π b = a := by
  obtain ⟨a, ha⟩ : ∃ a, π a ≠ a := by
    by_contra hcon
    push Not at hcon
    exact hπ1 (Equiv.ext hcon)
  have hb : π (π a) = a := perm_invol hππ a
  have key : ∀ a b : Fin 3, b ≠ a → ∃ x : Fin 3, x ≠ a ∧ x ≠ b := by decide
  have exh : ∀ a b x : Fin 3, b ≠ a → x ≠ a → x ≠ b → ∀ y : Fin 3, y = a ∨ y = b ∨ y = x := by
    decide
  obtain ⟨x, hxa, hxb⟩ := key a (π a) ha
  refine ⟨x, a, π a, hxa, hxb, fun h => ha h.symm, ?_, rfl, hb⟩
  rcases exh a (π a) x ha hxa hxb (π x) with h1 | h1 | h1
  · exfalso
    apply hxb
    rw [← perm_invol hππ x, h1]
  · exfalso
    apply hxa
    rw [← perm_invol hππ x, h1, hb]
  · exact h1

theorem b7b_heart_rank (π : Equiv.Perm (Fin 3)) (hππ : π * π = 1) (hπ1 : π ≠ 1)
    (h : Fin 3 → Matrix (Fin 2) (Fin 2) K) (hunit : ∀ i, IsUnit (h i).det)
    (hup : ∀ i, h i 1 0 = 0)
    (hrel : ∀ y : Fin 3 → Fin 2, ∏ i, (h i (y i) (y i) * h (π i) (y i) (y i)) = 1)
    (X : Cube 3 K ≃ₗ[K] Cube 3 K)
    (hX : ∀ v, X v = kronMap (fun i => dgMat (h i 0 0) (h i 1 1)) (permMap π v)) :
    cubeRk X ≤ 2 := by
  obtain ⟨x, a, b, hxa, hxb, hab, hx, ha, hb⟩ := b7b_exists_labels hππ hπ1
  have hκ := b7b_diag_rel_i hrel
  have hnz := fun i => upper_ne_zero (hup i) (hunit i)
  have R1 : h x 0 0 = h x 1 1 := by
    have := hκ x
    rw [hx] at this
    exact eq_of_mul_self_eq this
  have R2 : h a 0 0 * h b 0 0 = h a 1 1 * h b 1 1 := by
    have := hκ a
    rwa [ha] at this
  have R3 : h b 0 0 * h a 0 0 = h b 1 1 * h a 1 1 := by
    have := hκ b
    rwa [hb] at this
  have R4 := hrel (fun _ => 0)
  rw [prod_fin3 hxa hxb hab, hx, ha, hb] at R4
  have R5 : (h x 0 0 * (h a 0 0 * h b 0 0)) * (h x 0 0 * (h a 0 0 * h b 0 0)) = 1 * 1 := by
    rw [one_mul]
    rw [← R4]
    ring
  have R6 : h x 0 0 * (h a 0 0 * h b 0 0) = 1 := eq_of_mul_self_eq R5
  set M : Matrix (Fin 2) (Fin 2) K := dgMat (h a 0 0) (h a 1 1) with hM
  have hMu : IsUnit M.det := by
    rw [hM, det_dgMat]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero (hnz a).1 (hnz a).2)
  let c : Cube 3 K ≃ₗ[K] Cube 3 K := actUnit a M hMu
  have key : kronMap (fun i => dgMat (h i 0 0) (h i 1 1)) ∘ₗ actMap b M = actMap a M := by
    unfold actMap
    rw [← kronMap_mul]
    let cc : Fin 3 → K := fun i =>
      if i = x then h x 0 0 else if i = b then h a 0 0 * h b 0 0 else 1
    have hcx : cc x = h x 0 0 := by simp [cc]
    have hca : cc a = 1 := by simp [cc, hxa.symm, hab]
    have hcb : cc b = h a 0 0 * h b 0 0 := by simp [cc, hxb.symm]
    have hk : ∀ i, ((fun i => dgMat (h i 0 0) (h i 1 1)) *
        (Pi.mulSingle b M : Fin 3 → Matrix (Fin 2) (Fin 2) K)) i =
        cc i • (Pi.mulSingle a M : Fin 3 → Matrix (Fin 2) (Fin 2) K) i := by
      intro i
      rcases fin3_cases hxa hxb hab i with hi | hi | hi <;> rw [hi]
      · rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne hxb, Pi.mulSingle_eq_of_ne hxa, mul_one, hcx,
          ← R1, dgMat_scalar]
      · rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne hab, Pi.mulSingle_eq_same, mul_one, hca, one_smul]
      · rw [Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (Ne.symm hab), hcb, hM,
          dgMat_mul, ← R3, mul_comm (h b 0 0), dgMat_scalar]
    rw [kronMap_smul_pi _ _ cc hk, prod_fin3 hxa hxb hab, hcx, hca, hcb, mul_one, R6, one_smul]
  have hc : ∀ v, X (c v) = c (permMap π v) := by
    intro v
    rw [hX, actUnit_apply, permMap_actMap π hππ, ha]
    exact LinearMap.congr_fun key _
  have hXc : X * c = c * permMap π := LinearEquiv.ext fun v => hc v
  have hXe : X = c * permMap π * c⁻¹ := eq_mul_inv_iff_mul_eq.mpr hXc
  rw [hXe, cubeRk_conj]
  exact rank_perm_le_two π hππ hπ1

theorem b7b_heart (hq : 4 ≤ Nat.card K) (T : Cube 3 K ≃ₗ[K] Cube 3 K)
    (hE : ∀ x ∈ cubeE 3 K, T * x * T⁻¹ ∈ cubeE 3 K)
    (hE' : ∀ x ∈ cubeE 3 K, T⁻¹ * x * T ∈ cubeE 3 K)
    (hU' : ∀ x ∈ cubeU 3 K, T⁻¹ * x * T ∈ cubeU 3 K)
    (hT2 : T * T ∈ cubeU 3 K) (hTn : T ∉ cubeU 3 K) :
    ∃ u ∈ cubeU 3 K, (T * u) * (T * u) = 1 ∧ cubeRk (T * u) ≤ 2 := by
  obtain ⟨π, h, hππ, hunit, hup, hTh⟩ := b7b_heart_data hq T hE hE' hU' hT2
  by_cases hπ1 : π = 1
  · exfalso
    apply hTn
    refine b7b_mem_cubeU_of_upper hq T h hunit hup (fun v => ?_) hT2
    rw [hTh v, hπ1, permMap_one]
    rfl
  · have hrel := b7b_diag_rel hππ hup hTh hT2
    obtain ⟨g', hg'U, hg'⟩ := b7b_heart_normal_form T π hππ h hunit hup hTh hT2
    have hXsq : (g'⁻¹ * T) * (g'⁻¹ * T) = 1 := b7b_heart_sq_one T π hππ h hrel (g'⁻¹ * T) hg'
    have hXrk : cubeRk (g'⁻¹ * T) ≤ 2 := b7b_heart_rank π hππ hπ1 h hunit hup hrel (g'⁻¹ * T) hg'
    have hTu : T * (T⁻¹ * g'⁻¹ * T) = g'⁻¹ * T := by group
    refine ⟨T⁻¹ * g'⁻¹ * T, hU' _ (inv_mem hg'U), ?_, ?_⟩
    · rw [hTu]; exact hXsq
    · rw [hTu]; exact hXrk

theorem cubeRk_cubeU_ge_three {w : Cube 3 K ≃ₗ[K] Cube 3 K} (hw : w ∈ cubeU 3 K) (hne : w ≠ 1) :
    3 ≤ cubeRk w := by
  obtain ⟨β, hβ⟩ := mem_cubeU.mp hw
  have hβ0 : β ≠ 0 := by
    rintro rfl
    apply hne
    refine LinearEquiv.ext fun v => ?_
    rw [hβ]
    have : (fun i : Fin 3 => uniMat ((0 : Fin 3 → K) i)) =
        (1 : Fin 3 → Matrix (Fin 2) (Fin 2) K) := by
      funext i
      simpa using uniMat_zero
    rw [this, kronMap_one]
    rfl
  have h3 := rank_kron_uni_ge_three β hβ0
  unfold cubeRk
  have e : (w : Cube 3 K →ₗ[K] Cube 3 K) = kronMap (fun i => uniMat (β i)) := LinearMap.ext hβ
  rw [e]
  exact h3

theorem b7b_abstract {H : Type*} [Group H] (hq : 4 ≤ Nat.card K)
    (ρ : H →* (Cube 3 K ≃ₗ[K] Cube 3 K)) (L : Subgroup H) (hker : ∀ x, ρ x = 1 → x ∈ L)
    (hcardL : Nat.card (L.map ρ) = Nat.card K ^ 3) (hLE : L.map ρ ≤ cubeE 3 K)
    (s : H) (hsL : s ∉ L) (hs2 : s * s ∈ L) (hnL' : ∀ l ∈ L, s⁻¹ * l * s ∈ L)
    (hnE : ∀ x ∈ cubeE 3 K, ρ s * x * (ρ s)⁻¹ ∈ cubeE 3 K)
    (hnE' : ∀ x ∈ cubeE 3 K, (ρ s)⁻¹ * x * ρ s ∈ cubeE 3 K) :
    ∃ l ∈ L, ρ (s * l * (s * l)) = 1 ∧ ∀ h : H, h * (s * l) * h⁻¹ ∈ L → False := by
  obtain ⟨C, hCE, hC⟩ := exists_conj_cubeU 3 K (L.map ρ) hLE hcardL
  have hmem : ∀ l ∈ L, C⁻¹ * ρ l * C ∈ cubeU 3 K := fun l hl =>
    (hC _).mp (Subgroup.mem_map_of_mem ρ hl)
  have hCx : ∀ x ∈ cubeE 3 K, C * x * C⁻¹ ∈ cubeE 3 K := fun x hx =>
    (cubeE 3 K).mul_mem ((cubeE 3 K).mul_mem hCE hx) ((cubeE 3 K).inv_mem hCE)
  have hCx' : ∀ x ∈ cubeE 3 K, C⁻¹ * x * C ∈ cubeE 3 K := fun x hx =>
    (cubeE 3 K).mul_mem ((cubeE 3 K).mul_mem ((cubeE 3 K).inv_mem hCE) hx) hCE
  have hE : ∀ x ∈ cubeE 3 K, (C⁻¹ * ρ s * C) * x * (C⁻¹ * ρ s * C)⁻¹ ∈ cubeE 3 K := by
    intro x hx
    have e : (C⁻¹ * ρ s * C) * x * (C⁻¹ * ρ s * C)⁻¹ =
        C⁻¹ * (ρ s * (C * x * C⁻¹) * (ρ s)⁻¹) * C := by group
    rw [e]
    exact hCx' _ (hnE _ (hCx x hx))
  have hE' : ∀ x ∈ cubeE 3 K, (C⁻¹ * ρ s * C)⁻¹ * x * (C⁻¹ * ρ s * C) ∈ cubeE 3 K := by
    intro x hx
    have e : (C⁻¹ * ρ s * C)⁻¹ * x * (C⁻¹ * ρ s * C) =
        C⁻¹ * ((ρ s)⁻¹ * (C * x * C⁻¹) * ρ s) * C := by group
    rw [e]
    exact hCx' _ (hnE' _ (hCx x hx))
  have hU' : ∀ x ∈ cubeU 3 K, (C⁻¹ * ρ s * C)⁻¹ * x * (C⁻¹ * ρ s * C) ∈ cubeU 3 K := by
    intro x hx
    have h1 : C * x * C⁻¹ ∈ L.map ρ := (hC _).mpr (by
      have e : C⁻¹ * (C * x * C⁻¹) * C = x := by group
      rw [e]; exact hx)
    obtain ⟨l, hl, hlx⟩ := h1
    have e : (C⁻¹ * ρ s * C)⁻¹ * x * (C⁻¹ * ρ s * C) = C⁻¹ * ρ (s⁻¹ * l * s) * C := by
      rw [map_mul, map_mul, map_inv, hlx]
      group
    rw [e]
    exact hmem _ (hnL' l hl)
  have hT2 : (C⁻¹ * ρ s * C) * (C⁻¹ * ρ s * C) ∈ cubeU 3 K := by
    have e : (C⁻¹ * ρ s * C) * (C⁻¹ * ρ s * C) = C⁻¹ * ρ (s * s) * C := by
      rw [map_mul]
      group
    rw [e]
    exact hmem _ hs2
  have hTn : C⁻¹ * ρ s * C ∉ cubeU 3 K := by
    intro hT
    have h1 : ρ s ∈ L.map ρ := (hC _).mpr hT
    obtain ⟨l, hl, hls⟩ := h1
    apply hsL
    have h2 : l⁻¹ * s ∈ L := hker _ (by rw [map_mul, map_inv, hls, inv_mul_cancel])
    have h3 := L.mul_mem hl h2
    simpa using h3
  obtain ⟨u, huU, hsq, hrk⟩ := b7b_heart hq (C⁻¹ * ρ s * C) hE hE' hU' hT2 hTn
  have h1 : C * u * C⁻¹ ∈ L.map ρ := (hC _).mpr (by
    have e : C⁻¹ * (C * u * C⁻¹) * C = u := by group
    rw [e]; exact huU)
  obtain ⟨l, hl, hlu⟩ := h1
  have hρj : ρ (s * l) = C * ((C⁻¹ * ρ s * C) * u) * C⁻¹ := by
    rw [map_mul, hlu]
    group
  refine ⟨l, hl, ?_, ?_⟩
  · rw [map_mul, hρj]
    have e : C * ((C⁻¹ * ρ s * C) * u) * C⁻¹ * (C * ((C⁻¹ * ρ s * C) * u) * C⁻¹) =
        C * (((C⁻¹ * ρ s * C) * u) * ((C⁻¹ * ρ s * C) * u)) * C⁻¹ := by group
    rw [e, hsq]
    group
  · intro h hh
    have hw : C⁻¹ * ρ (h * (s * l) * h⁻¹) * C ∈ cubeU 3 K :=
      (hC _).mp (Subgroup.mem_map_of_mem ρ hh)
    have hrk' : cubeRk (C⁻¹ * ρ (h * (s * l) * h⁻¹) * C) ≤ 2 := by
      have e1 : C⁻¹ * ρ (h * (s * l) * h⁻¹) * C = C⁻¹ * ρ (h * (s * l) * h⁻¹) * (C⁻¹)⁻¹ := by
        rw [inv_inv]
      rw [e1, cubeRk_conj, map_mul, map_mul, map_inv, cubeRk_conj, hρj, cubeRk_conj]
      exact hrk
    have hw1 : C⁻¹ * ρ (h * (s * l) * h⁻¹) * C = 1 := by
      by_contra hne
      have := cubeRk_cubeU_ge_three hw hne
      omega
    have hρ1 : ρ (h * (s * l) * h⁻¹) = 1 := by
      have e : ρ (h * (s * l) * h⁻¹) = C * (C⁻¹ * ρ (h * (s * l) * h⁻¹) * C) * C⁻¹ := by group
      rw [e, hw1]
      group
    have hsl : ρ (s * l) = 1 := by
      have h' : ρ h * ρ (s * l) * (ρ h)⁻¹ = 1 := by rwa [map_mul, map_mul, map_inv] at hρ1
      have h'' : ρ h * ρ (s * l) = ρ h := mul_inv_eq_one.mp h'
      simpa using h''
    exact hsL (by simpa using L.mul_mem (hker _ hsl) (L.inv_mem hl))
end Heart

end CFSG.RankThree.GF2n.Smith81.OrthTN

end
