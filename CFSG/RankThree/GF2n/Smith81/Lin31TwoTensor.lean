module

public import CFSG.RankThree.GF2n.Smith81.Lin31TwoAlg
public import CFSG.ClassicalGroups.SpecialLinear.Transitive
public import CFSG.RankThree.GF2n.Smith81.TiD2Alg

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG.Open CFSG.Open.StatedAPI
open scoped Matrix

namespace TensorStructure

variable {F : Type} [Field F]

private def colEquiv : (Fin 2 → F) × (Fin 2 → F) ≃+ Matrix (Fin 2) (Fin 2) F where
  toFun x := !![x.1 0, x.2 1; x.1 1, x.2 0]
  invFun X := (![X 0 0, X 1 0], ![X 1 1, X 0 1])
  left_inv x := by
    ext i <;> fin_cases i <;> rfl
  right_inv X := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  map_add' x y := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl

private theorem colEquiv_apply (x : (Fin 2 → F) × (Fin 2 → F)) :
    colEquiv x = !![x.1 0, x.2 1; x.1 1, x.2 0] := rfl

private theorem colEquiv_mul [CharP F 2] (A : GL (Fin 2) F)
    (hA : (A : Matrix (Fin 2) (Fin 2) F).det = 1) (v w : Fin 2 → F) :
    colEquiv ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ v,
        ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)ᵀ *ᵥ w) =
      (A : Matrix (Fin 2) (Fin 2) F) * colEquiv (v, w) := by
  have hinv : ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (A : Matrix (Fin 2) (Fin 2) F).adjugate := by
    rw [Matrix.coe_units_inv, Matrix.inv_def, hA, Ring.inverse_one, one_smul]
  rw [hinv, Matrix.adjugate_fin_two, colEquiv_apply, colEquiv_apply]
  conv_rhs => rw [Matrix.eta_fin_two (A : Matrix (Fin 2) (Fin 2) F)]
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, CharTwo.neg_eq] <;> ring

private def detPolar (X Y : Matrix (Fin 2) (Fin 2) F) : F :=
  X 0 0 * Y 1 1 + X 1 1 * Y 0 0 - X 0 1 * Y 1 0 - X 1 0 * Y 0 1

private theorem det_add_eq (X Y : Matrix (Fin 2) (Fin 2) F) :
    (X + Y).det = X.det + Y.det + detPolar X Y := by
  simp only [Matrix.det_fin_two, detPolar, Matrix.add_apply]
  ring

variable {K : Type}

private theorem vanish_vecMulVec [AddCommGroup K] (q : Matrix (Fin 2) (Fin 2) F → K)
    (b : Matrix (Fin 2) (Fin 2) F → Matrix (Fin 2) (Fin 2) F → K)
    (hinv : ∀ A X, A.det = 1 → q (A * X) = q X)
    (hadd : ∀ X Y, q (X + Y) = q X + q Y + b X Y)
    (hb : ∀ X Y Y', b X (Y + Y') = b X Y + b X Y') (hq0 : q 0 = 0)
    {t : F} (ht0 : t ≠ 0) (ht1 : 1 + t ≠ 0) (n u : Fin 2 → F) :
    q (Matrix.vecMulVec n u) = 0 := by
  set e₀ : Fin 2 → F := ![1, 0]
  have he₀ : e₀ ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [e₀] at this
  have hconst : ∀ m : Fin 2 → F, m ≠ 0 →
      q (Matrix.vecMulVec m u) = q (Matrix.vecMulVec e₀ u) := by
    intro m hm
    obtain ⟨A, hA, hAm⟩ :=
      CFSG.ClassicalGroups.SpecialLinear.exists_statedSL_mulVec_eq (le_refl 2) he₀ hm
    rw [← hAm, ← Matrix.mul_vecMulVec]
    exact hinv _ _ (det_of_mem_statedSL hA)
  have hbpair : ∀ m : Fin 2 → F, m ≠ 0 → m 0 = 0 →
      b (Matrix.vecMulVec e₀ u) (Matrix.vecMulVec m u) = -q (Matrix.vecMulVec e₀ u) := by
    intro m hm hm0
    have hne : e₀ + m ≠ 0 := by
      intro h
      have := congrFun h 0
      simp [e₀, hm0] at this
    have h := hadd (Matrix.vecMulVec e₀ u) (Matrix.vecMulVec m u)
    rw [← Matrix.add_vecMulVec, hconst _ hne, hconst _ hm, add_assoc] at h
    exact eq_neg_of_add_eq_zero_right (add_eq_left.mp h.symm)
  set m₁ : Fin 2 → F := ![0, 1]
  set m₂ : Fin 2 → F := ![0, t]
  have hm₁0 : m₁ ≠ 0 := by
    intro h
    have := congrFun h 1
    simp [m₁] at this
  have hm₂0 : m₂ ≠ 0 := by
    intro h
    have := congrFun h 1
    simp [m₂] at this
    exact ht0 this
  have hm₁₂0 : m₁ + m₂ ≠ 0 := by
    intro h
    have := congrFun h 1
    simp [m₁, m₂] at this
    exact ht1 this
  have key := hb (Matrix.vecMulVec e₀ u) (Matrix.vecMulVec m₁ u) (Matrix.vecMulVec m₂ u)
  rw [← Matrix.add_vecMulVec, hbpair _ hm₁₂0 (by simp [m₁, m₂]), hbpair _ hm₁0 (by simp [m₁]),
    hbpair _ hm₂0 (by simp [m₂])] at key
  have hν : q (Matrix.vecMulVec e₀ u) = 0 := neg_eq_zero.mp (add_eq_left.mp key.symm)
  by_cases hn : n = 0
  · rw [hn, Matrix.zero_vecMulVec, hq0]
  · rw [hconst n hn, hν]

private theorem vanish_of_det_eq_zero [AddCommGroup K] (q : Matrix (Fin 2) (Fin 2) F → K)
    (b : Matrix (Fin 2) (Fin 2) F → Matrix (Fin 2) (Fin 2) F → K)
    (hinv : ∀ A X, A.det = 1 → q (A * X) = q X)
    (hadd : ∀ X Y, q (X + Y) = q X + q Y + b X Y)
    (hb : ∀ X Y Y', b X (Y + Y') = b X Y + b X Y') (hq0 : q 0 = 0)
    {t : F} (ht0 : t ≠ 0) (ht1 : 1 + t ≠ 0) (X : Matrix (Fin 2) (Fin 2) F) (hX : X.det = 0) :
    q X = 0 := by
  by_cases h0 : X = 0
  · rw [h0, hq0]
  · obtain ⟨n, u, -, -, rfl⟩ := exists_vecMulVec_of_det_eq_zero h0 hX
    exact vanish_vecMulVec q b hinv hadd hb hq0 ht0 ht1 n u

private theorem eq_diag_det [Zero K] (q : Matrix (Fin 2) (Fin 2) F → K)
    (hinv : ∀ A X, A.det = 1 → q (A * X) = q X)
    (hsing : ∀ X : Matrix (Fin 2) (Fin 2) F, X.det = 0 → q X = 0)
    (X : Matrix (Fin 2) (Fin 2) F) : q X = q !![X.det, 0; 0, 1] := by
  set D : Matrix (Fin 2) (Fin 2) F := !![X.det, 0; 0, 1] with hD
  have hdetD : D.det = X.det := by simp [D, Matrix.det_fin_two_of]
  by_cases h : X.det = 0
  · rw [hsing X h, hsing D (hdetD.trans h)]
  · have hu : IsUnit D.det := by rw [hdetD]; exact isUnit_iff_ne_zero.mpr h
    have hA : (X * D⁻¹).det = 1 := by
      rw [Matrix.det_mul, Matrix.det_nonsing_inv, hdetD, Ring.inverse_eq_inv',
        mul_inv_cancel₀ h]
    have hXD : X * D⁻¹ * D = X := by
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul D hu, Matrix.mul_one]
    calc q X = q (X * D⁻¹ * D) := by rw [hXD]
      _ = q D := hinv _ _ hA

private theorem exists_addMonoidHom_det [AddCommGroup K] (q : Matrix (Fin 2) (Fin 2) F → K)
    (b : Matrix (Fin 2) (Fin 2) F → Matrix (Fin 2) (Fin 2) F → K)
    (hinv : ∀ A X, A.det = 1 → q (A * X) = q X)
    (hadd : ∀ X Y, q (X + Y) = q X + q Y + b X Y)
    (hb : ∀ X Y Y', b X (Y + Y') = b X Y + b X Y') (hq0 : q 0 = 0)
    {t : F} (ht0 : t ≠ 0) (ht1 : 1 + t ≠ 0) :
    ∃ f : F →+ K, (∀ X, q X = f X.det) ∧ ∀ X Y, b X Y = f (detPolar X Y) := by
  have hsing := vanish_of_det_eq_zero q b hinv hadd hb hq0 ht0 ht1
  have hdiag := eq_diag_det q hinv hsing
  have hbdiag : ∀ a : F, b !![1, 0; 0, 0] !![0, 0; 0, a] = q !![a, 0; 0, 1] := by
    intro a
    have h := hadd !![1, 0; 0, 0] !![0, 0; 0, a]
    have h1 : (!![1, 0; 0, 0] + !![0, 0; 0, a] : Matrix (Fin 2) (Fin 2) F) = !![1, 0; 0, a] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    rw [h1, hsing !![1, 0; 0, 0] (by simp [Matrix.det_fin_two_of]),
      hsing !![0, 0; 0, a] (by simp [Matrix.det_fin_two_of]), zero_add, zero_add, hdiag] at h
    rw [← h]
    simp [Matrix.det_fin_two_of]
  let f : F →+ K := AddMonoidHom.mk' (fun w => q !![w, 0; 0, 1]) (by
    intro a a'
    rw [← hbdiag, ← hbdiag, ← hbdiag, ← hb]
    congr 1
    ext i j; fin_cases i <;> fin_cases j <;> simp)
  have hf : ∀ X, q X = f X.det := fun X => hdiag X
  refine ⟨f, hf, fun X Y => ?_⟩
  have h := hadd X Y
  rw [hf, hf, hf, det_add_eq, map_add, map_add] at h
  have h' := congrArg (fun x => x - (f X.det + f Y.det)) h
  simp only [add_sub_cancel_left] at h'
  rw [h']

private theorem eq_zero_of_forall_map_mul [AddCommGroup K] (f : F →+ K) (hf : ∃ t, f t ≠ 0)
    {a : F} (ha : ∀ t, f (a * t) = 0) : a = 0 := by
  by_contra h
  obtain ⟨t, ht⟩ := hf
  apply ht
  have := ha (a⁻¹ * t)
  rwa [← mul_assoc, mul_inv_cancel₀ h, one_mul] at this

private theorem eq_smul_one_of_detPolar [Ring K] (f : F →+ K) (hf : ∃ t, f t ≠ 0) (c : K)
    (H : Matrix (Fin 2) (Fin 2) F)
    (hH : ∀ Y, f (detPolar H Y) = c * f (detPolar 1 Y)) :
    H = H 0 0 • (1 : Matrix (Fin 2) (Fin 2) F) := by
  have h01 : H 0 1 = 0 :=
    eq_zero_of_forall_map_mul f hf fun t => by simpa [detPolar] using hH !![0, 0; t, 0]
  have h10 : H 1 0 = 0 :=
    eq_zero_of_forall_map_mul f hf fun t => by simpa [detPolar] using hH !![0, t; 0, 0]
  have h11 : H 1 1 - H 0 0 = 0 := by
    refine eq_zero_of_forall_map_mul f hf fun t => ?_
    have h1 := hH !![t, 0; 0, 0]
    have h2 := hH !![0, 0; 0, t]
    simp [detPolar] at h1 h2
    rw [sub_mul, map_sub, h1, h2, sub_self]
  rw [sub_eq_zero] at h11
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01, h10, h11]

private theorem matrix_tensor_structure [Field K] [Finite F] (hKF : Nat.card K = Nat.card F)
    (q : Matrix (Fin 2) (Fin 2) F → K)
    (b : Matrix (Fin 2) (Fin 2) F → Matrix (Fin 2) (Fin 2) F → K)
    (κ : K → Matrix (Fin 2) (Fin 2) F →+ Matrix (Fin 2) (Fin 2) F)
    (hinv : ∀ A X, A.det = 1 → q (A * X) = q X)
    (hadd : ∀ X Y, q (X + Y) = q X + q Y + b X Y)
    (hb : ∀ X Y Y', b X (Y + Y') = b X Y + b X Y') (hq0 : q 0 = 0)
    (hbnd : ∃ X Y, b X Y ≠ 0) {t : F} (ht0 : t ≠ 0) (ht1 : 1 + t ≠ 0)
    (hκ : ∀ c A, A.det = 1 → ∀ X, κ c (A * X) = A * κ c X)
    (hκb : ∀ c X Y, b (κ c X) Y = c * b X Y)
    (hκadd : ∀ c c' X, κ (c + c') X = κ c X + κ c' X)
    (hκmul : ∀ c c' X, κ (c * c') X = κ c (κ c' X)) (hκone : ∀ X, κ 1 X = X) :
    ∃ (ε : K ≃+* F) (θ : F), θ ≠ 0 ∧ (∀ c X, κ c X = ε c • X) ∧
      ∀ X, ε (q X) = θ * X.det := by
  obtain ⟨f, hqf, hbf⟩ := exists_addMonoidHom_det q b hinv hadd hb hq0 ht0 ht1
  have hf : ∃ t, f t ≠ 0 := by
    obtain ⟨X, Y, h⟩ := hbnd
    exact ⟨detPolar X Y, by rwa [← hbf]⟩
  have hscal : ∀ c X, κ c X = (κ c 1) 0 0 • X := by
    intro c X
    obtain ⟨H, hH⟩ := schur_right (κ c) (hκ c)
    have h1 : κ c 1 = H := by rw [hH, Matrix.one_mul]
    have hpol : ∀ Y, f (detPolar H Y) = c * f (detPolar 1 Y) := by
      intro Y
      rw [← hbf, ← hbf, ← h1, hκb]
    have hHs := eq_smul_one_of_detPolar f hf c H hpol
    calc κ c X = X * H := hH X
      _ = X * (H 0 0 • 1) := congrArg (X * ·) hHs
      _ = H 0 0 • X := by rw [Matrix.mul_smul, Matrix.mul_one]
      _ = (κ c 1) 0 0 • X := by rw [h1]
  have hκzero : ∀ X, κ 0 X = 0 := by
    intro X
    have := hκadd 0 0 X
    rw [add_zero] at this
    simpa using this
  let εr : K →+* F :=
    { toFun := fun c => (κ c 1) 0 0
      map_one' := by simp [hκone]
      map_mul' := fun c c' => by
        rw [hκmul, hscal c (κ c' 1), Matrix.smul_apply, smul_eq_mul]
      map_zero' := by simp [hκzero]
      map_add' := fun c c' => by simp [hκadd] }
  have hεr : ∀ c, εr c = (κ c 1) 0 0 := fun c => rfl
  have hbij : Function.Bijective εr := εr.injective.bijective_of_nat_card_le hKF.ge
  have hfε : ∀ c s, f (εr c * s) = c * f s := by
    intro c s
    have := hκb c 1 !![s, 0; 0, 0]
    rw [hscal c 1, hbf, hbf, ← hεr] at this
    simpa [detPolar] using this
  have hf1 : f 1 ≠ 0 := by
    intro h
    obtain ⟨t₀, ht₀⟩ := hf
    obtain ⟨c, rfl⟩ := hbij.2 t₀
    apply ht₀
    rw [← mul_one (εr c), hfε, h, mul_zero]
  refine ⟨RingEquiv.ofBijective εr hbij, εr (f 1), (map_ne_zero εr).mpr hf1,
    fun c X => hscal c X, fun X => ?_⟩
  obtain ⟨c, hc⟩ := hbij.2 X.det
  rw [RingEquiv.ofBijective_apply, hqf, ← hc, ← mul_one (εr c), hfε, map_mul, mul_one,
    mul_comm]

end TensorStructure

theorem tensor_structure {K F E : Type} [Field K] [Finite K] [CharP K 2] [Field F] [Finite F]
    [CharP F 2] (hKF : Nat.card K = Nat.card F) (h4 : 4 ≤ Nat.card F)
    [AddCommGroup E] [Module K E] (Qf : E → K) (B : E →ₗ[K] E →ₗ[K] K)
    (hQsmul : ∀ (a : K) e, Qf (a • e) = a ^ 2 * Qf e)
    (hQadd : ∀ e f, Qf (e + f) = Qf e + Qf f + B e f) (halt : ∀ e, B e e = 0)
    (hnd : ∀ e, (∀ f, B e f = 0) → e = 0)
    {Γ : Type} [Group Γ] (ρ : Γ →* (E ≃ₗ[K] E)) (hρQ : ∀ s e, Qf (ρ s e) = Qf e)
    (g : Γ →* GL (Fin 2) F) (hg : ∀ A : GL (Fin 2) F, A ∈ StatedSL 2 F → ∃ s, g s = A)
    (hgdet : ∀ s, (g s : Matrix (Fin 2) (Fin 2) F).det = 1)
    (Φ₀ : E ≃+ (Fin 2 → F) × (Fin 2 → F))
    (hΦ₀ : ∀ s e, Φ₀ (ρ s e) = ((g s : Matrix (Fin 2) (Fin 2) F) *ᵥ (Φ₀ e).1,
      (((g s)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)ᵀ *ᵥ (Φ₀ e).2)) :
    ∃ (ε : K ≃+* F) (Φ : E ≃+ Matrix (Fin 2) (Fin 2) F),
      (∀ (c : K) e, Φ (c • e) = ε c • Φ e) ∧
      (∀ s e, Φ (ρ s e) = (g s : Matrix (Fin 2) (Fin 2) F) * Φ e) ∧
      ∀ e, ε (Qf e) = (Φ e).det := by
  obtain ⟨t, ht0, ht1⟩ := D2.exists_ne_zero_ne_one h4
  have ht1' : 1 + t ≠ 0 := fun h =>
    ht1 ((eq_neg_of_add_eq_zero_right h).trans (CharTwo.neg_eq 1))
  obtain ⟨e₁, he₁⟩ : ∃ e : E, e ≠ 0 := by
    refine ⟨Φ₀.symm (![1, 0], 0), fun h => ?_⟩
    have := congrArg (fun x => (Φ₀ x).1 0) h
    simp at this
  obtain ⟨Φ₁, hΦ₁⟩ : ∃ Φ₁ : E ≃+ Matrix (Fin 2) (Fin 2) F,
      ∀ s e, Φ₁ (ρ s e) = (g s : Matrix (Fin 2) (Fin 2) F) * Φ₁ e := by
    refine ⟨Φ₀.trans TensorStructure.colEquiv, fun s e => ?_⟩
    rw [AddEquiv.trans_apply, AddEquiv.trans_apply, hΦ₀, TensorStructure.colEquiv_mul _ (hgdet s)]
  have hsymm : ∀ A : Matrix (Fin 2) (Fin 2) F, A.det = 1 → ∀ X, ∃ s,
      (g s : Matrix (Fin 2) (Fin 2) F) = A ∧ Φ₁.symm (A * X) = ρ s (Φ₁.symm X) := by
    intro A hA X
    obtain ⟨s, hs⟩ := hg (Matrix.nonsingInvUnit A (by rw [hA]; exact isUnit_one))
      (mem_statedSL_of_det hA)
    have hs' : (g s : Matrix (Fin 2) (Fin 2) F) = A := by rw [hs]; rfl
    refine ⟨s, hs', ?_⟩
    rw [AddEquiv.symm_apply_eq, hΦ₁, hs', AddEquiv.apply_symm_apply]
  have hQ0 : Qf 0 = 0 := by simpa using hQsmul 0 0
  obtain ⟨ε, θ, hθ, hε, hεq⟩ := TensorStructure.matrix_tensor_structure hKF
    (fun X => Qf (Φ₁.symm X)) (fun X Y => B (Φ₁.symm X) (Φ₁.symm Y))
    (fun c => AddMonoidHom.mk' (fun X => Φ₁ (c • Φ₁.symm X)) (fun X Y => by simp [smul_add]))
    (fun A X hA => by
      obtain ⟨s, -, hs⟩ := hsymm A hA X
      simp only [hs, hρQ])
    (fun X Y => by simp only [map_add, hQadd])
    (fun X Y Y' => by simp only [map_add])
    (by simp only [map_zero, hQ0])
    (by
      by_contra h
      push Not at h
      exact he₁ (hnd e₁ fun f => by simpa using h (Φ₁ e₁) (Φ₁ f)))
    ht0 ht1'
    (fun c A hA X => by
      obtain ⟨s, hgs, hs⟩ := hsymm A hA X
      simp only [AddMonoidHom.mk'_apply]
      rw [hs, ← map_smul, hΦ₁, hgs])
    (fun c X Y => by
      simp only [AddMonoidHom.mk'_apply, AddEquiv.symm_apply_apply, map_smul,
        LinearMap.smul_apply, smul_eq_mul])
    (fun c c' X => by simp only [AddMonoidHom.mk'_apply, add_smul, map_add])
    (fun c c' X => by simp only [AddMonoidHom.mk'_apply, mul_smul, AddEquiv.symm_apply_apply])
    (fun X => by simp only [AddMonoidHom.mk'_apply, one_smul, AddEquiv.apply_symm_apply])
  set D : Matrix (Fin 2) (Fin 2) F := !![1, 0; 0, θ] with hD
  set D' : Matrix (Fin 2) (Fin 2) F := !![1, 0; 0, θ⁻¹] with hD'
  have hDD' : D * D' = 1 := by
    rw [hD, hD', Matrix.mul_fin_two, Matrix.one_fin_two]
    simp [hθ]
  have hD'D : D' * D = 1 := by
    rw [hD, hD', Matrix.mul_fin_two, Matrix.one_fin_two]
    simp [hθ]
  let R : Matrix (Fin 2) (Fin 2) F ≃+ Matrix (Fin 2) (Fin 2) F :=
    { toFun := fun X => X * D
      invFun := fun X => X * D'
      left_inv := fun X => by simp only [Matrix.mul_assoc, hDD', Matrix.mul_one]
      right_inv := fun X => by simp only [Matrix.mul_assoc, hD'D, Matrix.mul_one]
      map_add' := fun X Y => Matrix.add_mul X Y D }
  have hR : ∀ X, R X = X * D := fun X => rfl
  refine ⟨ε, Φ₁.trans R, fun c e => ?_, fun s e => ?_, fun e => ?_⟩
  · rw [AddEquiv.trans_apply, AddEquiv.trans_apply, hR, hR]
    have := hε c (Φ₁ e)
    simp only [AddMonoidHom.mk'_apply, AddEquiv.symm_apply_apply] at this
    rw [this, Matrix.smul_mul]
  · rw [AddEquiv.trans_apply, AddEquiv.trans_apply, hR, hR, hΦ₁, Matrix.mul_assoc]
  · rw [AddEquiv.trans_apply, hR, Matrix.det_mul]
    have := hεq (Φ₁ e)
    simp only [AddEquiv.symm_apply_apply] at this
    rw [this, hD, Matrix.det_fin_two_of]
    ring

end CFSG.RankThree.GF2n.Smith81
