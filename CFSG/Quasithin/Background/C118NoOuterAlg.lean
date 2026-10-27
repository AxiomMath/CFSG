module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellGamma

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique.Setup.Campbell CFSG.QuasithinUnique.Setup.Offender

section Action

theorem exists_perm_action {Γ W F : Type*} [Group Γ] [Group W] [Field F] (act : Γ →* MulAut W)
    (β : W →* Multiplicative (Fin 2 → F)) (hβ : Function.Surjective β)
    (hker : ∀ g u v, β u = β v → β (act g u) = β (act g v)) :
    ∃ ρ : Γ →* Equiv.Perm (Fin 2 → F),
      (∀ g x y, ρ g (x + y) = ρ g x + ρ g y) ∧
      ∀ g u, ρ g (Multiplicative.toAdd (β u)) = Multiplicative.toAdd (β (act g u)) := by
  classical
  let P : Γ → (Fin 2 → F) → (Fin 2 → F) := fun g x =>
    Multiplicative.toAdd (β (act g (Function.surjInv hβ (Multiplicative.ofAdd x))))
  have hP : ∀ g u, P g (Multiplicative.toAdd (β u)) = Multiplicative.toAdd (β (act g u)) := by
    intro g u
    have h2 : β (Function.surjInv hβ (Multiplicative.ofAdd (Multiplicative.toAdd (β u)))) =
        β u := Function.surjInv_eq hβ _
    show Multiplicative.toAdd (β (act g (Function.surjInv hβ
      (Multiplicative.ofAdd (Multiplicative.toAdd (β u)))))) = _
    rw [hker g _ u h2]
  have hex : ∀ x : Fin 2 → F, ∃ u, Multiplicative.toAdd (β u) = x := fun x => by
    obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd x)
    exact ⟨u, by rw [hu]; rfl⟩
  have hPadd : ∀ g x y, P g (x + y) = P g x + P g y := by
    intro g x y
    obtain ⟨u, rfl⟩ := hex x
    obtain ⟨v, rfl⟩ := hex y
    have e3 : Multiplicative.toAdd (β u) + Multiplicative.toAdd (β v) =
        Multiplicative.toAdd (β (u * v)) := by rw [map_mul, toAdd_mul]
    rw [e3, hP, hP, hP, map_mul, map_mul, toAdd_mul]
  have hPmul : ∀ g h x, P (g * h) x = P g (P h x) := by
    intro g h x
    obtain ⟨u, rfl⟩ := hex x
    rw [hP h u, hP g (act h u), hP (g * h) u, map_mul]
    rfl
  have hP1 : ∀ x, P 1 x = x := by
    intro x
    obtain ⟨u, rfl⟩ := hex x
    rw [hP, map_one]
    rfl
  let Pe : Γ → Equiv.Perm (Fin 2 → F) := fun g =>
    { toFun := P g
      invFun := P g⁻¹
      left_inv := fun x => by rw [← hPmul, inv_mul_cancel, hP1]
      right_inv := fun x => by rw [← hPmul, mul_inv_cancel, hP1] }
  refine ⟨{ toFun := Pe
            map_one' := Equiv.ext hP1
            map_mul' := fun g h => Equiv.ext (hPmul g h) }, hPadd, hP⟩

end Action

section Commutant

variable {F : Type*} [Field F]

@[expose] def upperSL (b : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, b; 0, 1], by simp [Matrix.det_fin_two_of]⟩

@[expose] def lowerSL (b : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, 0; b, 1], by simp [Matrix.det_fin_two_of]⟩

theorem upperSL_mulVec (b : F) (v : Fin 2 → F) :
    ((upperSL b : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec v =
      ![v 0 + b * v 1, v 1] := by
  ext i
  fin_cases i <;> simp [upperSL, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem lowerSL_mulVec (b : F) (v : Fin 2 → F) :
    ((lowerSL b : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec v =
      ![v 0, b * v 0 + v 1] := by
  ext i
  fin_cases i <;> simp [lowerSL, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem commutant_sl2 (ψ : (Fin 2 → F) → (Fin 2 → F))
    (hadd : ∀ x y, ψ (x + y) = ψ x + ψ y)
    (hcomm : ∀ (A : Matrix.SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F),
      ψ ((A : Matrix (Fin 2) (Fin 2) F).mulVec v) = (A : Matrix (Fin 2) (Fin 2) F).mulVec (ψ v)) :
    ∃ d : F, ∀ v, ψ v = d • v := by
  have hsplit : ∀ x y : F, (![x, y] : Fin 2 → F) = ![x, 0] + ![0, y] := by
    intro x y
    ext i
    fin_cases i <;> simp
  have hU : ∀ (b x y : F), ψ ![x + b * y, y] = ψ ![x, y] + ψ ![b * y, 0] := by
    intro b x y
    rw [← hadd]
    congr 1
    ext i
    fin_cases i <;> simp
  have hL : ∀ (b x y : F), ψ ![x, b * x + y] = ψ ![x, y] + ψ ![0, b * x] := by
    intro b x y
    rw [← hadd]
    congr 1
    ext i
    fin_cases i <;> simp [add_comm]
  have h1 : ∀ b x y : F, (ψ ![x + b * y, y]) 1 = (ψ ![x, y]) 1 := by
    intro b x y
    have := congrFun (hcomm (upperSL b) ![x, y]) 1
    rw [upperSL_mulVec] at this
    simpa [upperSL, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have h2 : ∀ b x y : F, (ψ ![x + b * y, y]) 0 = (ψ ![x, y]) 0 + b * (ψ ![x, y]) 1 := by
    intro b x y
    have := congrFun (hcomm (upperSL b) ![x, y]) 0
    rw [upperSL_mulVec] at this
    simpa [upperSL, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have h3 : ∀ b x y : F, (ψ ![x, b * x + y]) 0 = (ψ ![x, y]) 0 := by
    intro b x y
    have := congrFun (hcomm (lowerSL b) ![x, y]) 0
    rw [lowerSL_mulVec] at this
    simpa [lowerSL, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have q1 : ∀ b : F, (ψ ![b, 0]) 1 = 0 := by
    intro b
    have e := h1 b 0 1
    rw [hU] at e
    have : (ψ ![0, 1]) 1 + (ψ ![b * 1, 0]) 1 = (ψ ![0, 1]) 1 := by simpa using e
    simpa using this
  set d : F := (ψ ![0, 1]) 1 with hd
  have q0 : ∀ b : F, (ψ ![b, 0]) 0 = b * d := by
    intro b
    have e := h2 b 0 1
    rw [hU] at e
    have : (ψ ![0, 1]) 0 + (ψ ![b * 1, 0]) 0 = (ψ ![0, 1]) 0 + b * (ψ ![0, 1]) 1 := by
      simpa using e
    have := add_left_cancel this
    simpa using this
  have r1 : ∀ y : F, (ψ ![0, y]) 1 = y * d := by
    intro y
    have e := h2 1 0 y
    rw [hU] at e
    have : (ψ ![0, y]) 0 + (ψ ![1 * y, 0]) 0 = (ψ ![0, y]) 0 + 1 * (ψ ![0, y]) 1 := by
      simpa using e
    have h5 := add_left_cancel this
    have h6 := q0 (1 * y)
    rw [h5] at h6
    simpa using h6
  have r0 : ∀ b : F, (ψ ![0, b]) 0 = 0 := by
    intro b
    have e := h3 b 1 0
    rw [hL] at e
    have : (ψ ![1, 0]) 0 + (ψ ![0, b * 1]) 0 = (ψ ![1, 0]) 0 := by simpa using e
    simpa using this
  refine ⟨d, fun v => ?_⟩
  have hv : v = ![v 0, 0] + ![0, v 1] := by
    ext i
    fin_cases i <;> simp
  rw [hv, hadd]
  ext i
  fin_cases i
  · simp [q0, r0, mul_comm]
  · simp [q1, r1, mul_comm]

end Commutant

section Semilinear

variable {F : Type*} [Field F]

omit [Field F] in
theorem perm_inv_add (g : Equiv.Perm (Fin 2 → F)) [Add F] [Zero F]
    (hg : ∀ x y, g (x + y) = g x + g y) (x y : Fin 2 → F) :
    g⁻¹ (x + y) = g⁻¹ x + g⁻¹ y := by
  apply g.injective
  rw [hg]
  simp

theorem exists_scalar_of_normalizes (g : Equiv.Perm (Fin 2 → F))
    (hg : ∀ x y, g (x + y) = g x + g y)
    (hn : ∀ A : Matrix.SpecialLinearGroup (Fin 2) F, ∃ A' : Matrix.SpecialLinearGroup (Fin 2) F,
      ∀ v, g ((A : Matrix (Fin 2) (Fin 2) F).mulVec v) =
        (A' : Matrix (Fin 2) (Fin 2) F).mulVec (g v))
    (hn' : ∀ A : Matrix.SpecialLinearGroup (Fin 2) F, ∃ A' : Matrix.SpecialLinearGroup (Fin 2) F,
      ∀ v, g⁻¹ ((A : Matrix (Fin 2) (Fin 2) F).mulVec v) =
        (A' : Matrix (Fin 2) (Fin 2) F).mulVec (g⁻¹ v))
    (c : F) : ∃ d : F, ∀ x, g (c • x) = d • g x := by
  have hginv := perm_inv_add g hg
  have hψadd : ∀ x y, g (c • g⁻¹ (x + y)) = g (c • g⁻¹ x) + g (c • g⁻¹ y) := by
    intro x y
    rw [hginv, smul_add, hg]
  have hψcomm : ∀ (A : Matrix.SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F),
      g (c • g⁻¹ ((A : Matrix (Fin 2) (Fin 2) F).mulVec v)) =
        (A : Matrix (Fin 2) (Fin 2) F).mulVec (g (c • g⁻¹ v)) := by
    intro A v
    obtain ⟨A', hA'⟩ := hn' A
    obtain ⟨A'', hA''⟩ := hn A'
    have hAA : ∀ x, (A : Matrix (Fin 2) (Fin 2) F).mulVec x =
        (A'' : Matrix (Fin 2) (Fin 2) F).mulVec x := by
      intro x
      have := hA'' (g⁻¹ x)
      rw [← hA' x] at this
      simpa using this
    rw [hA', ← Matrix.mulVec_smul, hA'', hAA]
  obtain ⟨d, hd⟩ := commutant_sl2 (fun v => g (c • g⁻¹ v)) hψadd hψcomm
  refine ⟨d, fun x => ?_⟩
  have := hd (g x)
  simpa using this

theorem exists_semilinear_of_normalizes [Finite F] (g : Equiv.Perm (Fin 2 → F))
    (hg : ∀ x y, g (x + y) = g x + g y)
    (hn : ∀ A : Matrix.SpecialLinearGroup (Fin 2) F, ∃ A' : Matrix.SpecialLinearGroup (Fin 2) F,
      ∀ v, g ((A : Matrix (Fin 2) (Fin 2) F).mulVec v) =
        (A' : Matrix (Fin 2) (Fin 2) F).mulVec (g v))
    (hn' : ∀ A : Matrix.SpecialLinearGroup (Fin 2) F, ∃ A' : Matrix.SpecialLinearGroup (Fin 2) F,
      ∀ v, g⁻¹ ((A : Matrix (Fin 2) (Fin 2) F).mulVec v) =
        (A' : Matrix (Fin 2) (Fin 2) F).mulVec (g⁻¹ v)) :
    ∃ σ : F ≃+* F, IsSemilinearWith g σ := by
  classical
  choose σ' hσ' using exists_scalar_of_normalizes g hg hn hn'
  have g0 : g 0 = 0 := by
    have := hg 0 0
    simpa using this
  set e0 : Fin 2 → F := Pi.single 0 1 with he0
  set x₀ : Fin 2 → F := g⁻¹ e0 with hx₀
  have hgx₀ : g x₀ = e0 := by simp [hx₀]
  have he0ne : e0 ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [he0] at this
  have hcoord : ∀ a b : F, a • e0 = b • e0 → a = b := by
    intro a b h
    have := congrFun h 0
    simpa [he0] using this
  have hσadd : ∀ a b, σ' (a + b) = σ' a + σ' b := by
    intro a b
    apply hcoord
    rw [add_smul, ← hgx₀, ← hσ', ← hσ', ← hσ', ← hg, ← add_smul]
  have hσmul : ∀ a b, σ' (a * b) = σ' a * σ' b := by
    intro a b
    apply hcoord
    calc σ' (a * b) • e0 = σ' (a * b) • g x₀ := by rw [hgx₀]
      _ = g ((a * b) • x₀) := (hσ' _ _).symm
      _ = g (a • (b • x₀)) := by rw [mul_smul]
      _ = σ' a • g (b • x₀) := hσ' _ _
      _ = σ' a • σ' b • g x₀ := by rw [hσ' b x₀]
      _ = (σ' a * σ' b) • e0 := by rw [hgx₀, mul_smul]
  have hσone : σ' 1 = 1 := by
    apply hcoord
    calc σ' 1 • e0 = σ' 1 • g x₀ := by rw [hgx₀]
      _ = g ((1 : F) • x₀) := (hσ' _ _).symm
      _ = (1 : F) • e0 := by simp [hgx₀]
  have hσzero : σ' 0 = 0 := by
    have := hσadd 0 0
    simpa using this
  have hx₀ne : x₀ ≠ 0 := by
    intro h
    apply he0ne
    rw [← hgx₀, h, g0]
  let f : F →+* F :=
    { toFun := σ'
      map_one' := hσone
      map_mul' := hσmul
      map_zero' := hσzero
      map_add' := hσadd }
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have h1 : g (a • x₀) = 0 := by
      rw [hσ' a x₀]
      have : σ' a = 0 := ha
      rw [this, zero_smul]
    have h2 : a • x₀ = 0 := g.injective (h1.trans g0.symm)
    rcases smul_eq_zero.mp h2 with h | h
    · exact h
    · exact absurd h hx₀ne
  have hfbij : Function.Bijective f := Finite.injective_iff_bijective.mp hfinj
  exact ⟨RingEquiv.ofBijective f hfbij, fun c w => hσ' c w⟩

end Semilinear

section MatrixPart

variable {F : Type*} [Field F]

@[expose] def semilinMatrix (g : Equiv.Perm (Fin 2 → F)) : Matrix (Fin 2) (Fin 2) F :=
  Matrix.of fun i j => g (Pi.single j 1) i

theorem semilinMatrix_mulVec {g : Equiv.Perm (Fin 2 → F)} (hg : ∀ x y, g (x + y) = g x + g y)
    {σ : F ≃+* F} (hσ : IsSemilinearWith g σ) (w : Fin 2 → F) :
    g w = (semilinMatrix g).mulVec (fun i => σ (w i)) := by
  have hw : w = w 0 • (Pi.single 0 1 : Fin 2 → F) + w 1 • (Pi.single 1 1 : Fin 2 → F) := by
    ext i
    fin_cases i <;> simp
  ext i
  conv_lhs => rw [hw, hg, hσ, hσ]
  simp [semilinMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]

theorem semilinMatrix_det_ne_zero {g : Equiv.Perm (Fin 2 → F)} (hg : ∀ x y, g (x + y) = g x + g y)
    {σ : F ≃+* F} (hσ : IsSemilinearWith g σ) : (semilinMatrix g).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  apply hv0
  have : (fun i => σ.symm (v i)) = 0 := by
    apply g.injective
    rw [semilinMatrix_mulVec hg hσ, hσ.map_zero]
    simpa using hv
  ext i
  have h1 := congrFun this i
  simpa using h1

theorem semilinMatrix_mul {g h : Equiv.Perm (Fin 2 → F)} (hg : ∀ x y, g (x + y) = g x + g y)
    (hh : ∀ x y, h (x + y) = h x + h y) {σ τ : F ≃+* F} (hσ : IsSemilinearWith g σ)
    (hτ : IsSemilinearWith h τ) :
    semilinMatrix (g * h) = semilinMatrix g * (semilinMatrix h).map σ := by
  have hgh : ∀ x y, (g * h) (x + y) = (g * h) x + (g * h) y := by
    intro x y
    simp only [Equiv.Perm.mul_apply, hh, hg]
  have hs : IsSemilinearWith (g * h) (σ * τ) := hσ.mul hτ
  have hall : ∀ w : Fin 2 → F, (semilinMatrix (g * h)).mulVec (fun i => (σ * τ) (w i)) =
      (semilinMatrix g * (semilinMatrix h).map σ).mulVec (fun i => (σ * τ) (w i)) := by
    intro w
    rw [← semilinMatrix_mulVec hgh hs, Equiv.Perm.mul_apply, semilinMatrix_mulVec hh hτ,
      semilinMatrix_mulVec hg hσ, ← Matrix.mulVec_mulVec]
    congr 1
    ext i
    have := RingHom.map_mulVec (σ : F →+* F) (semilinMatrix h) (fun i => τ (w i)) i
    simpa using this
  ext i j
  have := congrFun (hall (fun k => (σ * τ).symm ((Pi.single j (1 : F) : Fin 2 → F) k))) i
  simpa [Matrix.mulVec_single_one] using this

theorem det_semilinMatrix_mul {g h : Equiv.Perm (Fin 2 → F)} (hg : ∀ x y, g (x + y) = g x + g y)
    (hh : ∀ x y, h (x + y) = h x + h y) {σ τ : F ≃+* F} (hσ : IsSemilinearWith g σ)
    (hτ : IsSemilinearWith h τ) :
    (semilinMatrix (g * h)).det = (semilinMatrix g).det * σ (semilinMatrix h).det := by
  rw [semilinMatrix_mul hg hh hσ hτ, Matrix.det_mul]
  congr 1
  have := RingHom.map_det (σ : F →+* F) (semilinMatrix h)
  simpa using this.symm

@[expose] def mkSL (M : Matrix (Fin 2) (Fin 2) F) (h : M.det = 1) :
    Matrix.SpecialLinearGroup (Fin 2) F := ⟨M, h⟩

theorem mkSL_coe (M : Matrix (Fin 2) (Fin 2) F) (h : M.det = 1) :
    ((mkSL M h : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = M := rfl

@[expose] def scalePerm (u : Fˣ) : Equiv.Perm (Fin 2 → F) where
  toFun x := (u : F) • x
  invFun x := ((u⁻¹ : Fˣ) : F) • x
  left_inv x := by simp [smul_smul]
  right_inv x := by simp [smul_smul]

theorem scalePerm_apply (u : Fˣ) (x : Fin 2 → F) : scalePerm u x = (u : F) • x := rfl

theorem scalePerm_inv_apply (u : Fˣ) (x : Fin 2 → F) :
    (scalePerm u)⁻¹ x = ((u⁻¹ : Fˣ) : F) • x := rfl

theorem scale_conj_apply {g : Equiv.Perm (Fin 2 → F)} {σ : F ≃+* F} (hσ : IsSemilinearWith g σ)
    (u : Fˣ) (x : Fin 2 → F) :
    (scalePerm u * g * (scalePerm u)⁻¹) x = ((u : F) * (σ (u : F))⁻¹) • g x := by
  have hσ' : ∀ (c : F) (w : Fin 2 → F), g (c • w) = σ c • g w := hσ
  simp only [Equiv.Perm.mul_apply, scalePerm_apply, scalePerm_inv_apply, hσ', smul_smul]
  congr 1
  simp

theorem scale_conj_mem_Gamma {g : Equiv.Perm (Fin 2 → F)} (hg : ∀ x y, g (x + y) = g x + g y)
    {σ : F ≃+* F} (hσ : IsSemilinearWith g σ) (u : Fˣ)
    (hdet : ((u : F) * (σ (u : F))⁻¹) ^ 2 * (semilinMatrix g).det = 1) :
    scalePerm u * g * (scalePerm u)⁻¹ ∈ Gamma F := by
  set t : F := (u : F) * (σ (u : F))⁻¹ with ht
  have hdet' : (t • semilinMatrix g).det = 1 := by
    rw [Matrix.det_smul]
    simpa using hdet
  refine ⟨mkSL (t • semilinMatrix g) hdet', σ, ?_⟩
  apply Equiv.ext
  intro x
  rw [scale_conj_apply hσ, semilinPerm_apply, Matrix.SpecialLinearGroup.smul_def, mkSL_coe,
    Matrix.smul_eq_mulVec, Matrix.smul_mulVec, ← semilinMatrix_mulVec hg hσ]

end MatrixPart

section Rescale

theorem exists_rescale {B F : Type*} [Group B] [Finite B] [Field F] [Finite F] [CharP F 2]
    (hB : IsPGroup 2 B) (hF : 1 < Nat.card F - 1) (σ : B →* (F ≃+* F)) (δ : B → F)
    (hδ0 : ∀ b, δ b ≠ 0) (hδ : ∀ b b', δ (b * b') = δ b * σ b (δ b')) :
    ∃ u : Fˣ, ∀ b, ((u : F) * (σ b (u : F))⁻¹) ^ 2 * δ b = 1 := by
  classical
  have : Fintype B := Fintype.ofFinite B
  have : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set c₁ : F := ∏ x : B, δ x with hc₁
  have hc₁0 : c₁ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun x _ => hδ0 x
  have key : ∀ b, δ b ^ Fintype.card B * σ b c₁ = c₁ := by
    intro b
    have h1 : σ b c₁ = ∏ x : B, σ b (δ x) := map_prod (σ b) _ _
    have h2 : ∀ x, σ b (δ x) = δ (b * x) / δ b := by
      intro x
      have := hδ b x
      rw [eq_div_iff (hδ0 b), this]
      ring
    have h3 : ∏ x : B, δ (b * x) = c₁ :=
      Fintype.prod_equiv (Equiv.mulLeft b) (fun x => δ (b * x)) δ (fun x => rfl)
    have h4 : σ b c₁ = c₁ / δ b ^ Fintype.card B := by
      rw [h1]
      simp_rw [h2]
      rw [Finset.prod_div_distrib, h3, Finset.prod_const, Finset.card_univ]
    rw [h4]
    have : δ b ^ Fintype.card B ≠ 0 := pow_ne_zero _ (hδ0 b)
    field_simp
  obtain ⟨a, ha⟩ := hB.exists_card_eq
  have hcardB : Fintype.card B = 2 ^ a := by rw [← Nat.card_eq_fintype_card, ha]
  obtain ⟨m, -, hm⟩ := FiniteField.card F 2
  have hcardF : Fintype.card F = 2 ^ (m : ℕ) := hm
  have hNcard : Nat.card F = Fintype.card F := Nat.card_eq_fintype_card
  have hN1 : 1 < Fintype.card F - 1 := by rw [← hNcard]; exact hF
  have hodd : Odd (Fintype.card F - 1) := by
    rw [hcardF]
    have hm1 : 1 ≤ (m : ℕ) := m.pos
    have : 2 ^ (m : ℕ) = 2 * 2 ^ ((m : ℕ) - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [this]
    have h2 : 1 ≤ 2 ^ ((m : ℕ) - 1) := Nat.one_le_two_pow
    refine ⟨2 ^ ((m : ℕ) - 1) - 1, ?_⟩
    omega
  have hcop : Nat.Coprime (Fintype.card B) (Fintype.card F - 1) := by
    rw [hcardB]
    exact Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hodd)
  obtain ⟨t, -, ht⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hN1
  have hpow : ∀ x : F, x ≠ 0 → x ^ (Fintype.card B * t) = x := by
    intro x hx
    have hx1 := FiniteField.pow_card_sub_one_eq_one x hx
    rw [← Nat.div_add_mod (Fintype.card B * t) (Fintype.card F - 1), pow_add, pow_mul, hx1,
      one_pow, one_mul, ht, pow_one]
  set c₂ : F := c₁ ^ t with hc₂
  have hc₂0 : c₂ ≠ 0 := pow_ne_zero _ hc₁0
  have hδc₂ : ∀ b, δ b = c₂ / σ b c₂ := by
    intro b
    have h1 : δ b ^ Fintype.card B = c₁ / σ b c₁ := by
      have hs : σ b c₁ ≠ 0 := by simpa using hc₁0
      rw [eq_div_iff hs]
      exact key b
    calc δ b = δ b ^ (Fintype.card B * t) := (hpow _ (hδ0 b)).symm
      _ = (δ b ^ Fintype.card B) ^ t := by rw [pow_mul]
      _ = (c₁ / σ b c₁) ^ t := by rw [h1]
      _ = c₂ / σ b c₂ := by rw [div_pow, hc₂, map_pow]
  obtain ⟨c, hc⟩ := FiniteField.isSquare_of_char_two (F := F) (ringChar.eq F 2) c₂⁻¹
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, mul_zero] at hc
    exact inv_ne_zero hc₂0 hc
  refine ⟨Units.mk0 c hc0, fun b => ?_⟩
  have hσc₂ : σ b c₂ ≠ 0 := by simpa using hc₂0
  have hσc : σ b c ≠ 0 := by simpa using hc0
  have hsq : σ b c * σ b c = (σ b c₂)⁻¹ := by
    rw [← map_mul, ← hc, map_inv₀]
  show (c * (σ b c)⁻¹) ^ 2 * δ b = 1
  rw [hδc₂ b]
  have h1 : (c * (σ b c)⁻¹) ^ 2 = c₂⁻¹ * σ b c₂ := by
    rw [mul_pow, inv_pow, sq, sq, hc, hsq]
    simp
  rw [h1]
  field_simp

end Rescale

section FieldHom

theorem exists_fieldHom {P F : Type*} [Group P] [Field F] (ρ : P →* Equiv.Perm (Fin 2 → F))
    (hadd : ∀ p x y, ρ p (x + y) = ρ p x + ρ p y)
    (hsem : ∀ p, ∃ σ : F ≃+* F, IsSemilinearWith (ρ p) σ) :
    ∃ σ : P →* (F ≃+* F), (∀ p, IsSemilinearWith (ρ p) (σ p)) ∧
      ∀ p q, (semilinMatrix (ρ (p * q))).det =
        (semilinMatrix (ρ p)).det * σ p (semilinMatrix (ρ q)).det := by
  choose σ₀ hσ₀ using hsem
  have hone : σ₀ 1 = 1 := by
    have h1 : IsSemilinearWith (ρ 1) (1 : F ≃+* F) := by
      rw [map_one]
      exact IsSemilinearWith.one_perm
    exact (hσ₀ 1).unique h1
  have hmul : ∀ p q, σ₀ (p * q) = σ₀ p * σ₀ q := by
    intro p q
    have h1 : IsSemilinearWith (ρ (p * q)) (σ₀ p * σ₀ q) := by
      rw [map_mul]
      exact (hσ₀ p).mul (hσ₀ q)
    exact (hσ₀ (p * q)).unique h1
  let σ : P →* (F ≃+* F) := { toFun := σ₀, map_one' := hone, map_mul' := hmul }
  refine ⟨σ, hσ₀, fun p q => ?_⟩
  rw [map_mul]
  exact det_semilinMatrix_mul (hadd p) (hadd q) (hσ₀ p) (hσ₀ q)

end FieldHom

end CFSG.Quasithin
