module

public import CFSG.RankThree.GF2n.Smith81.OrthE1TripleCoord

public section

open scoped Matrix

open CFSG.Open CFSG.Open.StatedAPI

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

namespace Triple

variable {K : Type} [Field K]

namespace CT1

section Transport

abbrev V4 (K : Type) := Fin 2 → Fin 2 → K

@[expose] def iotaL : V4 K →ₗ[K] Tensor3 K where
  toFun x a b c := if c = 0 then x a b else 0
  map_add' x y := by
    funext a b c
    by_cases hc : c = 0 <;> simp [hc]
  map_smul' r x := by
    funext a b c
    by_cases hc : c = 0 <;> simp [hc]

@[expose] def piL : Tensor3 K →ₗ[K] V4 K where
  toFun T a b := T a b 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem iotaL_apply (x : V4 K) (a b c : Fin 2) :
    iotaL x a b c = if c = 0 then x a b else 0 := rfl

theorem piL_apply (T : Tensor3 K) (a b : Fin 2) : piL T a b = T a b 0 := rfl

theorem piL_iotaL (x : V4 K) : piL (iotaL x) = x := by
  funext a b
  simp [piL_apply, iotaL_apply]

@[expose] def resL (g : T3E K) : V4 K →ₗ[K] V4 K :=
  piL ∘ₗ g.toLinearMap ∘ₗ iotaL

theorem resL_apply (g : T3E K) (x : V4 K) : resL g x = piL (g (iotaL x)) := rfl

theorem act2E_unip_one_iotaL (x : V4 K) : act2E (unipSL (1 : K)) (iotaL x) = iotaL x := by
  funext a b c
  fin_cases c <;>
    simp [act2E_apply, tensor3Act2, Fin.sum_univ_two, unipSL_apply, iotaL_apply]

theorem eq_iotaL_of_fixed {T : Tensor3 K} (hT : act2E (unipSL (1 : K)) T = T) :
    T = iotaL (piL T) := by
  funext a b c
  have h := congrFun (congrFun (congrFun hT a) b) 0
  simp [act2E_apply, tensor3Act2, Fin.sum_univ_two, unipSL_apply] at h
  fin_cases c
  · simp [iotaL_apply, piL_apply]
  · simp [iotaL_apply, h]

theorem apply_iotaL {g : T3E K} (hg : act2E (unipSL (1 : K)) * g = g * act2E (unipSL 1))
    (x : V4 K) : g (iotaL x) = iotaL (resL g x) := by
  apply eq_iotaL_of_fixed
  rw [← LinearEquiv.mul_apply, hg, LinearEquiv.mul_apply, act2E_unip_one_iotaL]

theorem resL_mul (g : T3E K) {h : T3E K}
    (hh : act2E (unipSL (1 : K)) * h = h * act2E (unipSL 1)) :
    resL (g * h) = resL g ∘ₗ resL h := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, resL_apply, LinearEquiv.mul_apply, apply_iotaL hh]
  rfl

theorem resL_one : resL (1 : T3E K) = LinearMap.id :=
  LinearMap.ext fun x => piL_iotaL x


section Swap

variable [CharP K 2]

@[expose] def swapSL : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![0, 1; 1, 0], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩

theorem swapSL_apply : ((swapSL (K := K)) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0] := rfl

@[expose] def swapE : T3E K := act2E (swapSL (K := K))

theorem swapE_apply_zero (T : Tensor3 K) (a b : Fin 2) : swapE T a b 0 = T a b 1 := by
  simp [swapE, act2E_apply, tensor3Act2, Fin.sum_univ_two, swapSL_apply]

theorem swapE_apply_one (T : Tensor3 K) (a b : Fin 2) : swapE T a b 1 = T a b 0 := by
  simp [swapE, act2E_apply, tensor3Act2, Fin.sum_univ_two, swapSL_apply]

theorem tensor_decomp (T : Tensor3 K) : T = iotaL (piL T) + swapE (iotaL (piL (swapE T))) := by
  funext a b c
  fin_cases c <;> simp [swapE_apply_zero, swapE_apply_one, iotaL_apply, piL_apply]

end Swap

@[expose] def CC (κ : K) : Subgroup (T3E K) :=
  Ok κ ⊓ Subgroup.centralizer ((colG (K := K) : Subgroup (T3E K)) : Set (T3E K))

theorem mem_CC_iff {κ : K} {g : T3E K} :
    g ∈ CC κ ↔ g ∈ Ok κ ∧ ∀ A : Matrix.SpecialLinearGroup (Fin 2) K, act2E A * g = g * act2E A := by
  unfold CC
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun A => h2 _ ⟨A, rfl⟩⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rintro _ ⟨A, rfl⟩
    exact h2 A

theorem comm_of_mem_CC {κ : K} {g : T3E K} (hg : g ∈ CC κ)
    (A : Matrix.SpecialLinearGroup (Fin 2) K) : act2E A * g = g * act2E A :=
  (mem_CC_iff.mp hg).2 A

theorem mem_Ok_of_mem_CC {κ : K} {g : T3E K} (hg : g ∈ CC κ) : g ∈ Ok κ :=
  (mem_CC_iff.mp hg).1

section CharTwo

variable [CharP K 2]

theorem swapE_comm {g : T3E K} (hg : ∀ A, act2E A * g = g * act2E A) (S : Tensor3 K) :
    g (swapE S) = swapE (g S) := by
  have h := LinearEquiv.congr_fun (hg swapSL) S
  simpa [LinearEquiv.mul_apply, swapE] using h.symm

theorem eq_one_of_resL {g : T3E K} (hg : ∀ A, act2E A * g = g * act2E A)
    (h : resL g = LinearMap.id) : g = 1 := by
  refine LinearEquiv.ext fun T => ?_
  have hr : ∀ x, resL g x = x := fun x => by rw [h]; rfl
  change g T = T
  conv_lhs => rw [tensor_decomp T]
  rw [map_add, swapE_comm hg, apply_iotaL (hg _), apply_iotaL (hg _), hr, hr, ← tensor_decomp T]

@[expose] def omegaQ (κ : K) (x y : V4 K) : K :=
  Qk κ (iotaL x + swapE (iotaL y)) - Qk κ (iotaL x) - Qk κ (swapE (iotaL y))

theorem omegaQ_resL {κ : K} {g : T3E K} (hg : g ∈ CC κ) (x y : V4 K) :
    omegaQ κ (resL g x) (resL g y) = omegaQ κ x y := by
  have hc := comm_of_mem_CC hg
  unfold omegaQ
  have hO := mem_Ok.mp (mem_Ok_of_mem_CC hg)
  rw [← apply_iotaL (hc _), ← apply_iotaL (hc _), ← swapE_comm hc, ← map_add, hO, hO, hO]

theorem omegaQ_eq (κ : K) (x y : V4 K) :
    omegaQ κ x y = x 0 0 * y 1 1 + x 0 1 * y 1 0 + x 1 0 * y 0 1 + x 1 1 * y 0 0 +
      κ * (x 1 0 * y 1 1 + x 1 1 * y 1 0) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp [omegaQ, Qk, tensor3Form, detW, swapE_apply_zero, swapE_apply_one, iotaL_apply]
  linear_combination (-(κ * x 1 1 * y 1 0)) * h2

end CharTwo

@[expose] def lamE (κ : K) : V4 K ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K) where
  toFun x := Sum.elim ![x 0 0 + κ * x 1 0, x 0 1] ![x 1 1, x 1 0]
  invFun v := ![![v (Sum.inl 0) - κ * v (Sum.inr 1), v (Sum.inl 1)],
    ![v (Sum.inr 1), v (Sum.inr 0)]]
  map_add' x y := by
    funext i
    rcases i with i | i <;> fin_cases i <;> simp <;> ring
  map_smul' r x := by
    funext i
    rcases i with i | i <;> fin_cases i <;> simp <;> ring
  left_inv x := by
    funext a b
    fin_cases a <;> fin_cases b <;> simp
  right_inv v := by
    funext i
    rcases i with i | i <;> fin_cases i <;> simp

theorem sympPair_lamE [CharP K 2] (κ : K) (x y : V4 K) :
    sympPair 2 K (lamE κ x) (lamE κ y) = omegaQ κ x y := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [omegaQ_eq]
  simp [sympPair, lamE, dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Fin.sum_univ_two]
  linear_combination (-(κ * y 1 0 * x 1 1 + x 1 0 * y 0 1 + x 1 1 * y 0 0)) * h2

@[expose] noncomputable def psiMat (κ : K) (g : T3E K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  LinearMap.toMatrix' ((lamE κ).toLinearMap ∘ₗ resL g ∘ₗ (lamE κ).symm.toLinearMap)

theorem psiMat_mulVec (κ : K) (g : T3E K) (x : V4 K) :
    psiMat κ g *ᵥ lamE κ x = lamE κ (resL g x) := by
  rw [psiMat, LinearMap.toMatrix'_mulVec]
  simp

theorem psiMat_mul (κ : K) (g : T3E K) {h : T3E K}
    (hh : act2E (unipSL (1 : K)) * h = h * act2E (unipSL 1)) :
    psiMat κ (g * h) = psiMat κ g * psiMat κ h := by
  rw [psiMat, psiMat, psiMat, ← LinearMap.toMatrix'_mul]
  congr 1
  refine LinearMap.ext fun v => ?_
  simp [resL_mul g hh]

theorem psiMat_one (κ : K) : psiMat κ (1 : T3E K) = 1 := by
  rw [psiMat, resL_one, ← LinearMap.toMatrix'_id]
  congr 1
  refine LinearMap.ext fun v => ?_
  simp

theorem matrix_eq_of_dotProduct {ι : Type} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι K}
    (h : ∀ v w : ι → K, v ⬝ᵥ (A *ᵥ w) = v ⬝ᵥ (B *ᵥ w)) : A = B := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  simpa [Matrix.mulVec_single_one, single_one_dotProduct] using this

theorem psiMat_symp [CharP K 2] {κ : K} {g : T3E K} (hg : g ∈ CC κ) :
    (psiMat κ g)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * psiMat κ g = Matrix.fromBlocks 0 1 (-1) 0 := by
  have key : ∀ v w, sympPair 2 K (psiMat κ g *ᵥ v) (psiMat κ g *ᵥ w) = sympPair 2 K v w := by
    intro v w
    obtain ⟨x, rfl⟩ := (lamE κ).surjective v
    obtain ⟨y, rfl⟩ := (lamE κ).surjective w
    rw [psiMat_mulVec, psiMat_mulVec, sympPair_lamE, sympPair_lamE, omegaQ_resL hg]
  refine matrix_eq_of_dotProduct fun v w => ?_
  have := key v w
  simp only [sympPair] at this
  rw [← this, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

@[expose] noncomputable def psiMon (κ : K) :
    CC κ →* Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K where
  toFun g := psiMat κ g
  map_one' := psiMat_one κ
  map_mul' g h := psiMat_mul κ g (comm_of_mem_CC h.2 _)

@[expose] noncomputable def psi [CharP K 2] (κ : K) : CC κ →* StatedSp 2 K :=
  (psiMon κ).toHomUnits.codRestrict (StatedSp 2 K) fun g => mem_statedSp_iff.mpr (psiMat_symp g.2)

theorem psi_val [CharP K 2] (κ : K) (g : CC κ) :
    ((psi κ g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      psiMat κ g := rfl

theorem psi_injective [CharP K 2] (κ : K) : Function.Injective (psi κ) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hM : psiMat κ g = 1 := by
    rw [← psi_val, hg]
    rfl
  have hres : resL (g : T3E K) = LinearMap.id := by
    refine LinearMap.ext fun x => (lamE κ).injective ?_
    rw [← psiMat_mulVec, hM, Matrix.one_mulVec]
    rfl
  exact Subtype.ext (eq_one_of_resL (comm_of_mem_CC g.2) hres)

end Transport

section Element

variable [CharP K 2]

theorem resL_uf (c : K) (F : Matrix.SpecialLinearGroup (Fin 2) K) (x : V4 K) (a b : Fin 2) :
    resL (act0E (unipSL c) * act1E F) x a b =
      ∑ a', (unipSL c : Matrix (Fin 2) (Fin 2) K) a a' *
        ∑ b', (F : Matrix (Fin 2) (Fin 2) K) b b' * x a' b' := by
  simp [resL_apply, LinearEquiv.mul_apply, act0E_apply, act1E_apply, tensor3Act0, tensor3Act1,
    iotaL_apply, piL_apply]

theorem resL_uf_zero (c : K) (F : Matrix.SpecialLinearGroup (Fin 2) K) (x : V4 K) (b : Fin 2) :
    resL (act0E (unipSL c) * act1E F) x 0 b =
      ((F : Matrix (Fin 2) (Fin 2) K) *ᵥ x 0) b +
        c * ((F : Matrix (Fin 2) (Fin 2) K) *ᵥ x 1) b := by
  rw [resL_uf]
  simp [Fin.sum_univ_two, unipSL_apply, Matrix.mulVec, dotProduct]

theorem resL_uf_one (c : K) (F : Matrix.SpecialLinearGroup (Fin 2) K) (x : V4 K) (b : Fin 2) :
    resL (act0E (unipSL c) * act1E F) x 1 b = ((F : Matrix (Fin 2) (Fin 2) K) *ᵥ x 1) b := by
  rw [resL_uf]
  simp [Fin.sum_univ_two, unipSL_apply, Matrix.mulVec, dotProduct]

theorem exists_vec_of_ne_one {F : Matrix.SpecialLinearGroup (Fin 2) K} (hF : F ≠ 1) :
    ∃ r : Fin 2 → K, r 0 * ((F : Matrix (Fin 2) (Fin 2) K) *ᵥ r) 1 +
      r 1 * ((F : Matrix (Fin 2) (Fin 2) K) *ᵥ r) 0 ≠ 0 := by
  by_contra h
  push Not at h
  have h10 := h ![1, 0]
  have h01 := h ![0, 1]
  have h11 := h ![1, 1]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h10 h01 h11
  have hd := F.2
  rw [Matrix.det_fin_two] at hd
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have e : (F : Matrix (Fin 2) (Fin 2) K) 0 0 = (F : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    linear_combination h11 - h10 - h01 - (F : Matrix (Fin 2) (Fin 2) K) 1 1 * h2
  have e1 : (F : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    have hsq : ((F : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) ^ 2 = 0 := by
      linear_combination hd + (F : Matrix (Fin 2) (Fin 2) K) 0 0 * e +
        (F : Matrix (Fin 2) (Fin 2) K) 1 0 * h01 + (1 - (F : Matrix (Fin 2) (Fin 2) K) 0 0) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq)
  apply hF
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h10, h01, e1, ← e]

theorem mulVec_ne_of_form {F : Matrix (Fin 2) (Fin 2) K} {r : Fin 2 → K}
    (hr : r 0 * (F *ᵥ r) 1 + r 1 * (F *ᵥ r) 0 ≠ 0) : F *ᵥ r ≠ r := by
  intro h
  apply hr
  rw [h]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination r 0 * r 1 * h2

theorem psiMat_sub_one_mulVec (κ : K) (g : T3E K) (x : V4 K) :
    (psiMat κ g - 1) *ᵥ lamE κ x = lamE κ (resL g x - x) := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, psiMat_mulVec, map_sub]

theorem rank_psiMat_uf (κ c : K) (F : Matrix.SpecialLinearGroup (Fin 2) K) {r : Fin 2 → K}
    (hr : (F : Matrix (Fin 2) (Fin 2) K) *ᵥ r ≠ r)
    (hPP : psiMat κ (act0E (unipSL c) * act1E F) * psiMat κ (act0E (unipSL c) * act1E F) = 1) :
    (psiMat κ (act0E (unipSL c) * act1E F) - 1).rank = 2 := by
  set P := psiMat κ (act0E (unipSL c) * act1E F) with hP
  apply le_antisymm
  · have h0 : (P - 1) * (P - 1) = 0 := by
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      have e : (P - 1) * (P - 1) = (2 : K) • (1 - P) := by
        rw [sub_mul, mul_sub, mul_sub, hPP, mul_one, one_mul, one_mul, two_smul]
        abel
      rw [e, h2, zero_smul]
    have := Matrix.rank_add_rank_le_card_of_mul_eq_zero h0
    simp at this
    omega
  · obtain ⟨b0, hb0⟩ := Function.ne_iff.mp hr
    set x1 : V4 K := ![r, 0] with hx1
    set x2 : V4 K := ![0, r] with hx2
    have hli : LinearIndependent K ![(P - 1) *ᵥ lamE κ x1, (P - 1) *ᵥ lamE κ x2] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      rw [hP, psiMat_sub_one_mulVec, psiMat_sub_one_mulVec, ← map_smul, ← map_smul, ← map_add,
        (lamE κ).map_eq_zero_iff] at hst
      have h1 := congrFun (congrFun hst 1) b0
      have h0 := congrFun (congrFun hst 0) b0
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply,
        resL_uf_zero, resL_uf_one] at h1 h0
      have e10 : x1 0 = r := rfl
      have e11 : x1 1 = 0 := rfl
      have e20 : x2 0 = 0 := rfl
      have e21 : x2 1 = r := rfl
      simp only [e10, e11, e20, e21, Matrix.mulVec_zero, Pi.zero_apply, mul_zero, zero_mul,
        add_zero, zero_add, sub_zero, sub_self] at h1 h0
      have ht : t = 0 := by
        rcases mul_eq_zero.mp h1 with h | h
        · exact h
        · exact absurd (sub_eq_zero.mp h) hb0
      subst ht
      simp only [zero_mul, add_zero] at h0
      rcases mul_eq_zero.mp h0 with h | h
      · exact ⟨h, rfl⟩
      · exact absurd (sub_eq_zero.mp h) hb0
    have hspan : Submodule.span K (Set.range ![(P - 1) *ᵥ lamE κ x1, (P - 1) *ᵥ lamE κ x2]) ≤
        LinearMap.range (P - 1).mulVecLin := by
      rw [Submodule.span_le, Set.range_subset_iff]
      intro i
      fin_cases i
      · exact ⟨lamE κ x1, rfl⟩
      · exact ⟨lamE κ x2, rfl⟩
    have := Submodule.finrank_mono hspan
    rw [finrank_span_eq_card hli] at this
    simpa [Matrix.rank] using this

theorem sympPair_psiMat_uf (κ c : K) (F : Matrix.SpecialLinearGroup (Fin 2) K) (r : Fin 2 → K) :
    sympPair 2 K (lamE κ ![0, r]) (psiMat κ (act0E (unipSL c) * act1E F) *ᵥ lamE κ ![0, r]) =
      (c + κ) * (r 0 * ((F : Matrix (Fin 2) (Fin 2) K) *ᵥ r) 1 +
        r 1 * ((F : Matrix (Fin 2) (Fin 2) K) *ᵥ r) 0) := by
  rw [psiMat_mulVec, sympPair_lamE, omegaQ_eq, resL_uf_zero, resL_uf_zero, resL_uf_one,
    resL_uf_one]
  have e0 : (![0, r] : V4 K) 0 = 0 := rfl
  have e1 : (![0, r] : V4 K) 1 = r := rfl
  simp only [e0, e1, Matrix.mulVec_zero, Pi.zero_apply, zero_mul, zero_add]
  ring

theorem c_eq_kappa (hKF11a : Sp4InvolutionStatement) [Finite K] (hK : 4 ≤ Nat.card K)
    {κ c : K} {F : Matrix.SpecialLinearGroup (Fin 2) K} (hF : F ≠ 1)
    (hnO : act0E (unipSL c) * act1E F ∈ Ok κ)
    (hnn : act0E (unipSL c) * act1E F * (act0E (unipSL c) * act1E F) = 1)
    {y : T3E K} (hyCC : y ∈ CC κ) (hyn : y * (act0E (unipSL c) * act1E F) =
      act0E (unipSL c) * act1E F * y) (hy2 : NotTwoPow y) : c = κ := by
  by_contra hck
  have hnCC : act0E (unipSL c) * act1E F ∈ CC κ := by
    refine mem_CC_iff.mpr ⟨hnO, fun A => ?_⟩
    rw [← mul_assoc, ← act0E_comm_act2E, mul_assoc, ← act1E_comm_act2E, mul_assoc]
  set n : CC κ := ⟨_, hnCC⟩ with hn
  set Y : CC κ := ⟨y, hyCC⟩ with hY
  have hnn' : n * n = 1 := Subtype.ext hnn
  have hnY : n * Y = Y * n := Subtype.ext hyn.symm
  have h1 : psi κ n * psi κ n = 1 := by rw [← map_mul, hnn', map_one]
  have hPP : psiMat κ (act0E (unipSL c) * act1E F) * psiMat κ (act0E (unipSL c) * act1E F) = 1 := by
    have := congrArg (fun z : StatedSp 2 K => ((z : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) h1
    simpa [psi_val] using this
  obtain ⟨r, hr⟩ := exists_vec_of_ne_one hF
  have h2 := rank_psiMat_uf κ c F (mulVec_ne_of_form hr) hPP
  have h3 : ∃ v : Fin 2 ⊕ Fin 2 → K, sympPair 2 K v
      (((psi κ n : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) ≠ 0 := by
    refine ⟨lamE κ ![0, r], ?_⟩
    rw [psi_val, sympPair_psiMat_uf]
    refine mul_ne_zero (fun h => hck ?_) hr
    have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination h - κ * h2'
  have hP := hKF11a K hK (psi κ n) h1 (by rw [psi_val]; exact h2) h3
  have hmem : psi κ Y ∈ Subgroup.centralizer ({psi κ n} : Set (StatedSp 2 K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hnY]
  obtain ⟨k, hk⟩ := hP ⟨psi κ Y, hmem⟩
  have hk' : psi κ (Y ^ 2 ^ k) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val hk
  have := psi_injective κ (hk'.trans (map_one _).symm)
  exact hy2 k (congrArg Subtype.val this)

end Element

theorem exists_two_ne_one {G : Type*} [Group G] (H : Subgroup G) (h3 : 3 ≤ Nat.card H) :
    ∃ a ∈ H, ∃ b ∈ H, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  by_contra hcon
  push Not at hcon
  have hle : Nat.card H ≤ 2 := by
    by_cases hb : ∃ a ∈ H, a ≠ 1
    · obtain ⟨a, ha, ha1⟩ := hb
      have hsub : (H : Set G) ⊆ {1, a} := by
        intro n hn
        by_cases hn1 : n = 1
        · simp [hn1]
        · simp [hcon n hn a ha hn1 ha1]
      calc Nat.card H = (H : Set G).ncard := (Nat.card_coe_set_eq _)
        _ ≤ ({1, a} : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ ({a} : Set G).ncard + 1 := Set.ncard_insert_le _ _
        _ = 2 := by rw [Set.ncard_singleton]
    · push Not at hb
      have : H = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hb
      rw [this, Subgroup.card_bot]
      norm_num
  omega

end CT1

theorem ct1_rows (hKF11a : Sp4InvolutionStatement) [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    (κ : K) (𝒩 : Subgroup (T3E K)) (h𝒩O : 𝒩 ≤ Ok κ) (h4 : 4 ≤ Nat.card 𝒩)
    (hsplit : ∀ n ∈ 𝒩, ∃ u ∈ lineG, ∃ f ∈ rowG, n = u * f)
    (hsq : ∀ n ∈ 𝒩, n * n = 1) (hTI : 𝒩 ⊓ lineG = ⊥)
    (y : T3E K) (hyO : y ∈ Ok κ) (hyc : ∀ g ∈ colG, y * g = g * y)
    (hyn : ∀ n ∈ 𝒩, y * n = n * y) (hy2 : NotTwoPow y) :
    κ = 0 ∧ 𝒩 ≤ rowG := by
  have hyCC : y ∈ CT1.CC κ := CT1.mem_CC_iff.mpr ⟨hyO, fun A => (hyc _ ⟨A, rfl⟩).symm⟩
  have key : ∀ n ∈ 𝒩, n ≠ 1 → ∀ (c : K) (F : Matrix.SpecialLinearGroup (Fin 2) K),
      n = act0E (unipSL c) * act1E F → c = κ := by
    intro n hn hn1 c F hnF
    have hF : F ≠ 1 := by
      rintro rfl
      apply hn1
      have hmem : n ∈ 𝒩 ⊓ lineG :=
        ⟨hn, by rw [hnF, map_one, mul_one]; exact mem_lineG_iff.mpr ⟨c, rfl⟩⟩
      rw [hTI] at hmem
      exact hmem
    subst hnF
    exact CT1.c_eq_kappa hKF11a hK hF (h𝒩O hn) (hsq _ hn) hyCC (hyn _ hn) hy2
  have hdec : ∀ n ∈ 𝒩, ∃ (c : K) (F : Matrix.SpecialLinearGroup (Fin 2) K),
      n = act0E (unipSL c) * act1E F := by
    intro n hn
    obtain ⟨u, hu, f, ⟨F, rfl⟩, rfl⟩ := hsplit n hn
    obtain ⟨c, rfl⟩ := mem_lineG_iff.mp hu
    exact ⟨c, F, rfl⟩
  obtain ⟨n1, hn1, n2, hn2, h1, h2, h12⟩ := CT1.exists_two_ne_one 𝒩 (by omega)
  obtain ⟨c1, F1, rfl⟩ := hdec n1 hn1
  obtain ⟨c2, F2, rfl⟩ := hdec n2 hn2
  have e1 := key _ hn1 h1 c1 F1 rfl
  have e2 := key _ hn2 h2 c2 F2 rfl
  have hprod : act0E (unipSL c1) * act1E F1 * (act0E (unipSL c2) * act1E F2) =
      act0E (unipSL (c1 + c2)) * act1E (F1 * F2) := by
    calc act0E (unipSL c1) * act1E F1 * (act0E (unipSL c2) * act1E F2)
        = act0E (unipSL c1) * ((act1E F1 * act0E (unipSL c2)) * act1E F2) := by
          simp only [mul_assoc]
      _ = act0E (unipSL c1) * ((act0E (unipSL c2) * act1E F1) * act1E F2) := by
          rw [act0E_comm_act1E]
      _ = act0E (unipSL c1 * unipSL c2) * act1E (F1 * F2) := by
          simp only [map_mul, mul_assoc]
      _ = act0E (unipSL (c1 + c2)) * act1E (F1 * F2) := by rw [unipSL_mul]
  have h12' : act0E (unipSL c1) * act1E F1 * (act0E (unipSL c2) * act1E F2) ≠ 1 := by
    intro h
    apply h12
    have hs := hsq _ hn2
    calc act0E (unipSL c1) * act1E F1
        = act0E (unipSL c1) * act1E F1 *
            ((act0E (unipSL c2) * act1E F2) * (act0E (unipSL c2) * act1E F2)) := by
          rw [hs, mul_one]
      _ = (act0E (unipSL c1) * act1E F1 * (act0E (unipSL c2) * act1E F2)) *
            (act0E (unipSL c2) * act1E F2) := by simp only [mul_assoc]
      _ = act0E (unipSL c2) * act1E F2 := by rw [h, one_mul]
  have e3 := key _ (𝒩.mul_mem hn1 hn2) h12' (c1 + c2) (F1 * F2) hprod
  have hκ : κ = 0 := by
    rw [e1, e2] at e3
    linear_combination e3
  refine ⟨hκ, fun n hn => ?_⟩
  by_cases hn1' : n = 1
  · rw [hn1']
    exact one_mem _
  obtain ⟨c, F, rfl⟩ := hdec n hn
  have hc := key _ hn hn1' c F rfl
  rw [hc, hκ, unipSL_zero, map_one, one_mul]
  exact ⟨F, rfl⟩

end Triple

end CFSG.RankThree.GF2n.Smith81.Smith23E1
