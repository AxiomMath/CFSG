module

public import CFSG.RankThree.GF2n.Smith81.OrthE1TripleCoord

public section

open scoped Matrix

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

namespace Triple

open CFSG.Open

variable {K : Type} [Field K]

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

@[expose] def CC : Subgroup (T3E K) :=
  Ok 0 ⊓ Subgroup.centralizer ((colG : Subgroup (T3E K)) : Set (T3E K))

theorem mem_CC {g : T3E K} :
    g ∈ CC ↔ g ∈ Ok 0 ∧ ∀ h ∈ (colG : Subgroup (T3E K)), h * g = g * h := by
  rw [CC, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  rfl

theorem tensor3Act2_unip_iotaL (x : V4 K) :
    tensor3Act2 (unipSL (1 : K) : Matrix (Fin 2) (Fin 2) K) (iotaL x) = iotaL x := by
  funext a b c
  fin_cases c <;> simp [tensor3Act2, unipSL_apply, iotaL_apply, Fin.sum_univ_two]

theorem eq_iotaL_of_fixed {T : Tensor3 K}
    (h : tensor3Act2 (unipSL (1 : K) : Matrix (Fin 2) (Fin 2) K) T = T) : T = iotaL (piL T) := by
  have h1 : ∀ a b, T a b 1 = 0 := by
    intro a b
    have := congrFun (congrFun (congrFun h a) b) 0
    simpa [tensor3Act2, unipSL_apply, Fin.sum_univ_two] using this
  funext a b c
  fin_cases c
  · simp [iotaL_apply, piL_apply]
  · simp [iotaL_apply, h1]

theorem apply_iotaL (g : CC (K := K)) (x : V4 K) :
    (g : T3E K) (iotaL x) = iotaL (piL ((g : T3E K) (iotaL x))) := by
  apply eq_iotaL_of_fixed
  have hc := (mem_CC.1 g.2).2 (act2E (unipSL 1)) ⟨unipSL 1, rfl⟩
  have h := LinearEquiv.congr_fun hc (iotaL x)
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, act2E_apply, act2E_apply,
    tensor3Act2_unip_iotaL] at h
  exact h

@[expose] def resL (g : CC (K := K)) : V4 K →ₗ[K] V4 K :=
  piL ∘ₗ (g : T3E K).toLinearMap ∘ₗ iotaL

theorem resL_apply (g : CC (K := K)) (x : V4 K) : resL g x = piL ((g : T3E K) (iotaL x)) :=
  rfl

theorem apply_iotaL' (g : CC (K := K)) (x : V4 K) :
    (g : T3E K) (iotaL x) = iotaL (resL g x) :=
  apply_iotaL g x

theorem resL_one (x : V4 K) : resL (1 : CC (K := K)) x = x := piL_iotaL x

theorem resL_mul (g h : CC (K := K)) (x : V4 K) : resL (g * h) x = resL g (resL h x) := by
  rw [resL_apply, Subgroup.coe_mul, LinearEquiv.mul_apply, apply_iotaL' h, apply_iotaL' g,
    piL_iotaL]

@[expose] def lamE : V4 K ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K) where
  toFun x := Sum.elim ![x 0 0, x 0 1] ![x 1 1, x 1 0]
  invFun v := ![![v (Sum.inl 0), v (Sum.inl 1)], ![v (Sum.inr 1), v (Sum.inr 0)]]
  map_add' x y := by
    funext i
    rcases i with i | i <;> fin_cases i <;> simp
  map_smul' r x := by
    funext i
    rcases i with i | i <;> fin_cases i <;> simp
  left_inv x := by
    funext a b
    fin_cases a <;> fin_cases b <;> simp
  right_inv v := by
    funext i
    rcases i with i | i <;> fin_cases i <;> simp

@[simp] theorem lamE_inl0 (x : V4 K) : lamE x (Sum.inl 0) = x 0 0 := rfl
@[simp] theorem lamE_inl1 (x : V4 K) : lamE x (Sum.inl 1) = x 0 1 := rfl
@[simp] theorem lamE_inr0 (x : V4 K) : lamE x (Sum.inr 0) = x 1 1 := rfl
@[simp] theorem lamE_inr1 (x : V4 K) : lamE x (Sum.inr 1) = x 1 0 := rfl

@[expose] def psiLin (g : CC (K := K)) :
    (Fin 2 ⊕ Fin 2 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K) :=
  lamE.toLinearMap ∘ₗ resL g ∘ₗ lamE.symm.toLinearMap

@[expose] def psiMat : CC (K := K) →* Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K where
  toFun g := LinearMap.toMatrix' (psiLin g)
  map_one' := by
    rw [show psiLin (1 : CC (K := K)) = LinearMap.id from
      LinearMap.ext fun v => by simp [psiLin, resL_one]]
    exact LinearMap.toMatrix'_id
  map_mul' g h := by
    rw [← LinearMap.toMatrix'_mul]
    congr 1
    exact LinearMap.ext fun v => by simp [psiLin, resL_mul]

theorem psiMat_mulVec (g : CC (K := K)) (v : Fin 2 ⊕ Fin 2 → K) :
    psiMat g *ᵥ v = lamE (resL g (lamE.symm v)) :=
  LinearMap.toMatrix'_mulVec _ v

theorem psiMat_mulVec_lam (g : CC (K := K)) (x : V4 K) :
    psiMat g *ᵥ lamE x = lamE (resL g x) := by
  rw [psiMat_mulVec, LinearEquiv.symm_apply_apply]

variable [CharP K 2]

@[expose] def swapSL : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![0, 1; 1, 0], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩

theorem tensor3_decomp (T : Tensor3 K) :
    T = iotaL (piL T) + act2E swapSL (iotaL (piL (act2E swapSL T))) := by
  funext a b c
  simp only [Pi.add_apply, act2E_apply, tensor3Act2, iotaL_apply, piL_apply, Fin.sum_univ_two]
  fin_cases c <;> simp [swapSL]

theorem swap_comm (g : CC (K := K)) (T : Tensor3 K) :
    act2E swapSL ((g : T3E K) T) = (g : T3E K) (act2E swapSL T) := by
  have hw := (mem_CC.1 g.2).2 (act2E swapSL) ⟨swapSL, rfl⟩
  rw [← LinearEquiv.mul_apply, hw, LinearEquiv.mul_apply]

theorem eq_one_of_resL {g : CC (K := K)} (h : ∀ x, resL g x = x) : g = 1 := by
  have hg : ∀ x, (g : T3E K) (iotaL x) = iotaL x := fun x => by rw [apply_iotaL', h]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro T
  change (g : T3E K) T = T
  calc (g : T3E K) T
      = (g : T3E K) (iotaL (piL T) + act2E swapSL (iotaL (piL (act2E swapSL T)))) := by
        rw [← tensor3_decomp]
    _ = iotaL (piL T) + act2E swapSL (iotaL (piL (act2E swapSL T))) := by
        rw [map_add, hg, ← swap_comm, hg]
    _ = T := (tensor3_decomp T).symm

theorem psiMat_eq_one {g : CC (K := K)} (h : psiMat g = 1) : g = 1 := by
  apply eq_one_of_resL
  intro x
  apply lamE.injective
  rw [← psiMat_mulVec_lam, h, Matrix.one_mulVec]

theorem psiMat_injective : Function.Injective (psiMat (K := K)) := by
  intro g h hgh
  have : psiMat (g * h⁻¹) = 1 := by rw [map_mul, hgh, ← map_mul, mul_inv_cancel, map_one]
  exact mul_inv_eq_one.1 (psiMat_eq_one this)

@[expose] def polar0 (T T' : Tensor3 K) : K :=
  tensor3Form (T + T') - tensor3Form T - tensor3Form T'

theorem tensor3Form_of_mem_Ok {g : T3E K} (hg : g ∈ Ok 0) (T : Tensor3 K) :
    tensor3Form (g T) = tensor3Form T := by
  have := hg T
  simpa [Qk] using this

theorem polar0_of_mem_Ok {g : T3E K} (hg : g ∈ Ok 0) (T T' : Tensor3 K) :
    polar0 (g T) (g T') = polar0 T T' := by
  simp only [polar0, ← map_add, tensor3Form_of_mem_Ok hg]

@[expose] def omegaV (x y : V4 K) : K :=
  x 0 0 * y 1 1 + x 0 1 * y 1 0 + x 1 0 * y 0 1 + x 1 1 * y 0 0

theorem polar0_iotaL_swap (x y : V4 K) :
    polar0 (iotaL x) (act2E swapSL (iotaL y)) = omegaV x y := by
  simp only [polar0, tensor3Form, Pi.add_apply, act2E_apply, tensor3Act2, iotaL_apply,
    Fin.sum_univ_two]
  simp [swapSL, omegaV]
  ring

theorem omegaV_resL (g : CC (K := K)) (x y : V4 K) :
    omegaV (resL g x) (resL g y) = omegaV x y := by
  rw [← polar0_iotaL_swap, ← polar0_iotaL_swap, ← apply_iotaL', ← apply_iotaL', swap_comm,
    polar0_of_mem_Ok (mem_CC.1 g.2).1]

theorem sympPair_lamE (x y : V4 K) : sympPair 2 K (lamE x) (lamE y) = omegaV x y := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp [sympPair, dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Fin.sum_univ_two,
    Matrix.fromBlocks, omegaV, Matrix.one_apply]
  linear_combination (-(x 1 1 * y 0 0 + x 1 0 * y 0 1)) * h2

theorem psiMat_sympPair (g : CC (K := K)) (v w : Fin 2 ⊕ Fin 2 → K) :
    sympPair 2 K (psiMat g *ᵥ v) (psiMat g *ᵥ w) = sympPair 2 K v w := by
  obtain ⟨x, rfl⟩ := lamE.surjective v
  obtain ⟨y, rfl⟩ := lamE.surjective w
  rw [psiMat_mulVec_lam, psiMat_mulVec_lam, sympPair_lamE, sympPair_lamE, omegaV_resL]

theorem gram_of_sympPair {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (h : ∀ v w, sympPair 2 K (M *ᵥ v) (M *ᵥ w) = sympPair 2 K v w) :
    Mᵀ * Matrix.fromBlocks 0 1 (-1) 0 * M = Matrix.fromBlocks 0 1 (-1) 0 := by
  ext i j
  have key : ∀ X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K,
      X i j = Pi.single i 1 ⬝ᵥ (X *ᵥ Pi.single j 1) := by
    intro X
    rw [Matrix.mulVec_single_one, single_one_dotProduct]
    rfl
  have hij := h (Pi.single i 1) (Pi.single j 1)
  simp only [sympPair] at hij
  rw [key (Mᵀ * _ * M), key (Matrix.fromBlocks 0 1 (-1) 0), ← hij, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

@[expose] def psiGL : CC (K := K) →* GL (Fin 2 ⊕ Fin 2) K := (psiMat (K := K)).toHomUnits

theorem psiGL_mem (g : CC (K := K)) : psiGL g ∈ StatedSp 2 K :=
  CFSG.Open.StatedAPI.mem_statedSp_iff.2 (gram_of_sympPair (psiMat_sympPair g))

@[expose] def psi : CC (K := K) →* StatedSp 2 K :=
  (psiGL (K := K)).codRestrict (StatedSp 2 K) psiGL_mem

theorem psi_coe (g : CC (K := K)) :
    (((psi g : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = psiMat g := rfl

theorem psi_injective : Function.Injective (psi (K := K)) := by
  intro g h hgh
  apply psiMat_injective
  rw [← psi_coe, ← psi_coe, hgh]

@[expose] def rowCC (A : Matrix.SpecialLinearGroup (Fin 2) K) : CC (K := K) :=
  ⟨act1E A, mem_CC.2 ⟨act1E_mem_Ok 0 A, by
    rintro _ ⟨B, rfl⟩
    exact (act1E_comm_act2E A B).symm⟩⟩

theorem resL_of_act1E {g : CC (K := K)} {A : Matrix.SpecialLinearGroup (Fin 2) K}
    (hg : (g : T3E K) = act1E A) (x : V4 K) (a b : Fin 2) :
    resL g x a b = ∑ b', (A : Matrix (Fin 2) (Fin 2) K) b b' * x a b' := by
  rw [resL_apply, hg, act1E_apply, piL_apply]
  simp [tensor3Act1, iotaL_apply]

theorem resL_of_act0E {g : CC (K := K)} {A : Matrix.SpecialLinearGroup (Fin 2) K}
    (hg : (g : T3E K) = act0E A) (x : V4 K) (a b : Fin 2) :
    resL g x a b = ∑ a', (A : Matrix (Fin 2) (Fin 2) K) a a' * x a' b := by
  rw [resL_apply, hg, act0E_apply, piL_apply]
  simp [tensor3Act0, iotaL_apply]

theorem psiMat_rowCC (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    psiMat (rowCC A) = Matrix.fromBlocks (A : Matrix (Fin 2) (Fin 2) K) 0 0
      ((A : Matrix (Fin 2) (Fin 2) K)⁻¹)ᵀ := by
  set M : Matrix (Fin 2) (Fin 2) K := (A : Matrix (Fin 2) (Fin 2) K) with hM
  have hdet : M.det = 1 := A.2
  have hinv : M⁻¹ = !![M 1 1, -M 0 1; -M 1 0, M 0 0] := by
    rw [Matrix.inv_def, hdet, Ring.inverse_one, one_smul, Matrix.adjugate_fin_two]
  rw [hinv]
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  obtain ⟨x, rfl⟩ := lamE.surjective v
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, psiMat_mulVec_lam, Matrix.fromBlocks_mulVec]
  have hr := resL_of_act1E (g := rowCC A) (A := A) rfl x
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [hr, Matrix.mulVec, dotProduct, Fin.sum_univ_two, ← hM, CharTwo.neg_eq] <;> ring

@[expose] def uS (S : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  Matrix.fromBlocks 1 S 0 1

theorem uS_mul (S S' : Matrix (Fin 2) (Fin 2) K) : uS S * uS S' = uS (S + S') := by
  simp [uS, Matrix.fromBlocks_multiply, add_comm]

theorem uS_zero : uS (0 : Matrix (Fin 2) (Fin 2) K) = 1 := Matrix.fromBlocks_one

theorem uS_injective : Function.Injective (uS (K := K)) := by
  intro S S' h
  exact (Matrix.fromBlocks_inj.1 h).2.1

@[expose] def S0 : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, 0]

theorem psiMat_of_line {g : CC (K := K)} {c : K} (hg : (g : T3E K) = act0E (unipSL c)) :
    psiMat g = uS (c • S0) := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  obtain ⟨x, rfl⟩ := lamE.surjective v
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, psiMat_mulVec_lam, uS, Matrix.fromBlocks_mulVec]
  have hr := resL_of_act0E hg x
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [hr, Matrix.mulVec, dotProduct, Fin.sum_univ_two, unipSL_apply, S0, Matrix.vecHead,
      Matrix.vecTail]

end Transport

section Cases

variable [CharP K 2]

theorem lineG_ne_bot : (lineG : Subgroup (T3E K)) ≠ ⊥ := by
  intro h
  have h1 : act0E (unipSL (1 : K)) ∈ (lineG : Subgroup (T3E K)) := mem_lineG_iff.2 ⟨1, rfl⟩
  rw [h, Subgroup.mem_bot] at h1
  have h2 : unipSL (1 : K) = unipSL 0 := act0E_injective (h1.trans (by rw [unipSL_zero, map_one]))
  exact one_ne_zero (unipSL_injective h2)

@[expose] def lowSL (c : K) : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, 0; c, 1], by simp [Matrix.det_fin_two]⟩

theorem lowSL_apply (c : K) : (lowSL c : Matrix (Fin 2) (Fin 2) K) = !![1, 0; c, 1] := rfl

end Cases

end Triple

end CFSG.RankThree.GF2n.Smith81.Smith23E1
