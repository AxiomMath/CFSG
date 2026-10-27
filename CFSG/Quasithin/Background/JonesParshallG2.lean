module

public import CFSG.Quasithin.Background.JonesParshallSL3

public noncomputable section

namespace CFSG.Quasithin.JonesParshall

open Matrix CFSG.Quasithin.Explicit CFSG.Open

variable {F : Type} [Field F]

@[expose] def zmk (r u₀ u₁ u₂ v₀ v₁ v₂ s : F) : quasithinZorn F :=
  (r, ![u₀, u₁, u₂], ![v₀, v₁, v₂], s)

omit [Field F] in
theorem zorn_eta (x : quasithinZorn F) :
    x = zmk x.1 (x.2.1 0) (x.2.1 1) (x.2.1 2) (x.2.2.1 0) (x.2.2.1 1) (x.2.2.1 2) x.2.2.2 := by
  obtain ⟨r, u, v, s⟩ := x
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl))
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl

omit [Field F] in
theorem zmk_inj {r u₀ u₁ u₂ v₀ v₁ v₂ s r' u₀' u₁' u₂' v₀' v₁' v₂' s' : F}
    (h : zmk r u₀ u₁ u₂ v₀ v₁ v₂ s = zmk r' u₀' u₁' u₂' v₀' v₁' v₂' s') :
    r = r' ∧ u₀ = u₀' ∧ u₁ = u₁' ∧ u₂ = u₂' ∧ v₀ = v₀' ∧ v₁ = v₁' ∧ v₂ = v₂' ∧ s = s' := by
  simp only [zmk, Prod.mk.injEq, Matrix.vecCons_inj, and_true] at h
  tauto

omit [Field F] in
theorem zmk_congr {r u₀ u₁ u₂ v₀ v₁ v₂ s r' u₀' u₁' u₂' v₀' v₁' v₂' s' : F}
    (h1 : r = r') (h2 : u₀ = u₀') (h3 : u₁ = u₁') (h4 : u₂ = u₂') (h5 : v₀ = v₀') (h6 : v₁ = v₁')
    (h7 : v₂ = v₂') (h8 : s = s') :
    zmk r u₀ u₁ u₂ v₀ v₁ v₂ s = zmk r' u₀' u₁' u₂' v₀' v₁' v₂' s' := by
  subst h1 h2 h3 h4 h5 h6 h7 h8
  rfl

theorem zmk_add (r u₀ u₁ u₂ v₀ v₁ v₂ s r' u₀' u₁' u₂' v₀' v₁' v₂' s' : F) :
    zmk r u₀ u₁ u₂ v₀ v₁ v₂ s + zmk r' u₀' u₁' u₂' v₀' v₁' v₂' s' =
      zmk (r + r') (u₀ + u₀') (u₁ + u₁') (u₂ + u₂') (v₀ + v₀') (v₁ + v₁') (v₂ + v₂') (s + s') := by
  simp [zmk]

theorem zmk_smul (c r u₀ u₁ u₂ v₀ v₁ v₂ s : F) :
    c • zmk r u₀ u₁ u₂ v₀ v₁ v₂ s =
      zmk (c * r) (c * u₀) (c * u₁) (c * u₂) (c * v₀) (c * v₁) (c * v₂) (c * s) := by
  simp [zmk]

theorem zmk_zero : zmk (0 : F) 0 0 0 0 0 0 0 = 0 := by
  simp [zmk]

theorem cayleyMul_zmk (r u₀ u₁ u₂ v₀ v₁ v₂ s t x₀ x₁ x₂ y₀ y₁ y₂ z : F) :
    cayleyMul (zmk r u₀ u₁ u₂ v₀ v₁ v₂ s) (zmk t x₀ x₁ x₂ y₀ y₁ y₂ z) =
      zmk (r * t + (u₀ * y₀ + u₁ * y₁ + u₂ * y₂))
        (r * x₀ + z * u₀ + (v₁ * y₂ - v₂ * y₁)) (r * x₁ + z * u₁ + (v₂ * y₀ - v₀ * y₂))
        (r * x₂ + z * u₂ + (v₀ * y₁ - v₁ * y₀))
        (t * v₀ + s * y₀ + (u₁ * x₂ - u₂ * x₁)) (t * v₁ + s * y₁ + (u₂ * x₀ - u₀ * x₂))
        (t * v₂ + s * y₂ + (u₀ * x₁ - u₁ * x₀)) (s * z + (v₀ * x₀ + v₁ * x₁ + v₂ * x₂)) := by
  simp only [zmk, cayleyMul, quasithinCross, Fin.sum_univ_three, Prod.mk.injEq]
  refine ⟨by simp, ?_, ?_, by simp⟩ <;> funext i <;> fin_cases i <;> simp

theorem cayleyTr_zmk (r u₀ u₁ u₂ v₀ v₁ v₂ s : F) :
    cayleyTr (zmk r u₀ u₁ u₂ v₀ v₁ v₂ s) = r + s := rfl

theorem cayleyNorm_zmk (r u₀ u₁ u₂ v₀ v₁ v₂ s : F) :
    cayleyNorm (zmk r u₀ u₁ u₂ v₀ v₁ v₂ s) = r * s + (u₀ * v₀ + u₁ * v₁ + u₂ * v₂) := by
  simp [cayleyNorm, zmk, Fin.sum_univ_three]

theorem cayleyOne_eq : cayleyOne F = zmk 1 0 0 0 0 0 0 1 := by
  rw [cayleyOne, zmk]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl)) <;> funext i <;> fin_cases i <;> rfl

@[expose] def xaFun (a : Fin 3 → F) (x : quasithinZorn F) : quasithinZorn F :=
  zmk (x.1 + (a 0 * x.2.2.1 0 + a 1 * x.2.2.1 1 + a 2 * x.2.2.1 2))
    (x.2.1 0 + (x.1 + x.2.2.2 + (a 0 * x.2.2.1 0 + a 1 * x.2.2.1 1 + a 2 * x.2.2.1 2)) * a 0)
    (x.2.1 1 + (x.1 + x.2.2.2 + (a 0 * x.2.2.1 0 + a 1 * x.2.2.1 1 + a 2 * x.2.2.1 2)) * a 1)
    (x.2.1 2 + (x.1 + x.2.2.2 + (a 0 * x.2.2.1 0 + a 1 * x.2.2.1 1 + a 2 * x.2.2.1 2)) * a 2)
    (x.2.2.1 0 + (a 1 * x.2.1 2 - a 2 * x.2.1 1)) (x.2.2.1 1 + (a 2 * x.2.1 0 - a 0 * x.2.1 2))
    (x.2.2.1 2 + (a 0 * x.2.1 1 - a 1 * x.2.1 0))
    (x.2.2.2 + (a 0 * x.2.2.1 0 + a 1 * x.2.2.1 1 + a 2 * x.2.2.1 2))

@[expose] def ybFun (b : Fin 3 → F) (x : quasithinZorn F) : quasithinZorn F :=
  zmk (x.1 + (b 0 * x.2.1 0 + b 1 * x.2.1 1 + b 2 * x.2.1 2))
    (x.2.1 0 + (b 1 * x.2.2.1 2 - b 2 * x.2.2.1 1)) (x.2.1 1 + (b 2 * x.2.2.1 0 - b 0 * x.2.2.1 2))
    (x.2.1 2 + (b 0 * x.2.2.1 1 - b 1 * x.2.2.1 0))
    (x.2.2.1 0 + (x.1 + x.2.2.2 + (b 0 * x.2.1 0 + b 1 * x.2.1 1 + b 2 * x.2.1 2)) * b 0)
    (x.2.2.1 1 + (x.1 + x.2.2.2 + (b 0 * x.2.1 0 + b 1 * x.2.1 1 + b 2 * x.2.1 2)) * b 1)
    (x.2.2.1 2 + (x.1 + x.2.2.2 + (b 0 * x.2.1 0 + b 1 * x.2.1 1 + b 2 * x.2.1 2)) * b 2)
    (x.2.2.2 + (b 0 * x.2.1 0 + b 1 * x.2.1 1 + b 2 * x.2.1 2))

theorem xaFun_zmk (a : Fin 3 → F) (r u₀ u₁ u₂ v₀ v₁ v₂ s : F) :
    xaFun a (zmk r u₀ u₁ u₂ v₀ v₁ v₂ s) =
      zmk (r + (a 0 * v₀ + a 1 * v₁ + a 2 * v₂))
        (u₀ + (r + s + (a 0 * v₀ + a 1 * v₁ + a 2 * v₂)) * a 0)
        (u₁ + (r + s + (a 0 * v₀ + a 1 * v₁ + a 2 * v₂)) * a 1)
        (u₂ + (r + s + (a 0 * v₀ + a 1 * v₁ + a 2 * v₂)) * a 2)
        (v₀ + (a 1 * u₂ - a 2 * u₁)) (v₁ + (a 2 * u₀ - a 0 * u₂)) (v₂ + (a 0 * u₁ - a 1 * u₀))
        (s + (a 0 * v₀ + a 1 * v₁ + a 2 * v₂)) := rfl

theorem ybFun_zmk (b : Fin 3 → F) (r u₀ u₁ u₂ v₀ v₁ v₂ s : F) :
    ybFun b (zmk r u₀ u₁ u₂ v₀ v₁ v₂ s) =
      zmk (r + (b 0 * u₀ + b 1 * u₁ + b 2 * u₂))
        (u₀ + (b 1 * v₂ - b 2 * v₁)) (u₁ + (b 2 * v₀ - b 0 * v₂)) (u₂ + (b 0 * v₁ - b 1 * v₀))
        (v₀ + (r + s + (b 0 * u₀ + b 1 * u₁ + b 2 * u₂)) * b 0)
        (v₁ + (r + s + (b 0 * u₀ + b 1 * u₁ + b 2 * u₂)) * b 1)
        (v₂ + (r + s + (b 0 * u₀ + b 1 * u₁ + b 2 * u₂)) * b 2)
        (s + (b 0 * u₀ + b 1 * u₁ + b 2 * u₂)) := rfl

@[expose] def xaLin (a : Fin 3 → F) : quasithinZorn F →ₗ[F] quasithinZorn F where
  toFun := xaFun a
  map_add' x y := by
    rw [zorn_eta x, zorn_eta y, zmk_add, xaFun_zmk, xaFun_zmk, xaFun_zmk, zmk_add]
    apply zmk_congr <;> ring
  map_smul' c x := by
    rw [zorn_eta x, zmk_smul, xaFun_zmk, xaFun_zmk, RingHom.id_apply, zmk_smul]
    apply zmk_congr <;> ring

@[expose] def ybLin (b : Fin 3 → F) : quasithinZorn F →ₗ[F] quasithinZorn F where
  toFun := ybFun b
  map_add' x y := by
    rw [zorn_eta x, zorn_eta y, zmk_add, ybFun_zmk, ybFun_zmk, ybFun_zmk, zmk_add]
    apply zmk_congr <;> ring
  map_smul' c x := by
    rw [zorn_eta x, zmk_smul, ybFun_zmk, ybFun_zmk, RingHom.id_apply, zmk_smul]
    apply zmk_congr <;> ring

section Char2

variable [CharP F 2]

theorem xaFun_xaFun (a : Fin 3 → F) (x : quasithinZorn F) : xaFun a (xaFun a x) = x := by
  have h : ∀ r u₀ u₁ u₂ v₀ v₁ v₂ s : F, xaFun a (xaFun a (zmk r u₀ u₁ u₂ v₀ v₁ v₂ s)) =
      zmk r u₀ u₁ u₂ v₀ v₁ v₂ s := fun r u₀ u₁ u₂ v₀ v₁ v₂ s => by
    rw [xaFun_zmk, xaFun_zmk]
    apply zmk_congr <;> ring_nf <;> reduce_mod_char!
  have := h x.1 (x.2.1 0) (x.2.1 1) (x.2.1 2) (x.2.2.1 0) (x.2.2.1 1) (x.2.2.1 2) x.2.2.2
  rwa [← zorn_eta x] at this

theorem ybFun_ybFun (b : Fin 3 → F) (x : quasithinZorn F) : ybFun b (ybFun b x) = x := by
  have h : ∀ r u₀ u₁ u₂ v₀ v₁ v₂ s : F, ybFun b (ybFun b (zmk r u₀ u₁ u₂ v₀ v₁ v₂ s)) =
      zmk r u₀ u₁ u₂ v₀ v₁ v₂ s := fun r u₀ u₁ u₂ v₀ v₁ v₂ s => by
    rw [ybFun_zmk, ybFun_zmk]
    apply zmk_congr <;> ring_nf <;> reduce_mod_char!
  have := h x.1 (x.2.1 0) (x.2.1 1) (x.2.1 2) (x.2.2.1 0) (x.2.2.1 1) (x.2.2.1 2) x.2.2.2
  rwa [← zorn_eta x] at this

theorem xaFun_mul (a : Fin 3 → F) (x y : quasithinZorn F) :
    xaFun a (cayleyMul x y) = cayleyMul (xaFun a x) (xaFun a y) := by
  rw [zorn_eta x, zorn_eta y, cayleyMul_zmk, xaFun_zmk, xaFun_zmk, xaFun_zmk, cayleyMul_zmk]
  apply zmk_congr <;> ring_nf <;> reduce_mod_char!

theorem ybFun_mul (b : Fin 3 → F) (x y : quasithinZorn F) :
    ybFun b (cayleyMul x y) = cayleyMul (ybFun b x) (ybFun b y) := by
  rw [zorn_eta x, zorn_eta y, cayleyMul_zmk, ybFun_zmk, ybFun_zmk, ybFun_zmk, cayleyMul_zmk]
  apply zmk_congr <;> ring_nf <;> reduce_mod_char!

theorem xaFun_one (a : Fin 3 → F) : xaFun a (cayleyOne F) = cayleyOne F := by
  rw [cayleyOne_eq, xaFun_zmk]
  apply zmk_congr <;> ring_nf <;> reduce_mod_char!

theorem ybFun_one (b : Fin 3 → F) : ybFun b (cayleyOne F) = cayleyOne F := by
  rw [cayleyOne_eq, ybFun_zmk]
  apply zmk_congr <;> ring_nf <;> reduce_mod_char!

theorem xaFun_tr (a : Fin 3 → F) (x : quasithinZorn F) : cayleyTr (xaFun a x) = cayleyTr x := by
  rw [zorn_eta x, xaFun_zmk, cayleyTr_zmk, cayleyTr_zmk]
  ring_nf
  reduce_mod_char!

theorem ybFun_tr (b : Fin 3 → F) (x : quasithinZorn F) : cayleyTr (ybFun b x) = cayleyTr x := by
  rw [zorn_eta x, ybFun_zmk, cayleyTr_zmk, cayleyTr_zmk]
  ring_nf
  reduce_mod_char!

theorem xaFun_norm (a : Fin 3 → F) (x : quasithinZorn F) :
    cayleyNorm (xaFun a x) = cayleyNorm x := by
  rw [zorn_eta x, xaFun_zmk, cayleyNorm_zmk, cayleyNorm_zmk]
  ring_nf
  reduce_mod_char!

theorem ybFun_norm (b : Fin 3 → F) (x : quasithinZorn F) :
    cayleyNorm (ybFun b x) = cayleyNorm x := by
  rw [zorn_eta x, ybFun_zmk, cayleyNorm_zmk, cayleyNorm_zmk]
  ring_nf
  reduce_mod_char!

@[expose] def g2X (a : Fin 3 → F) : ↥(cayleyGroup F) :=
  ⟨LinearEquiv.ofInvolutive (xaLin a) (xaFun_xaFun a),
    xaFun_one a, xaFun_mul a, xaFun_tr a, xaFun_norm a⟩

@[expose] def g2Y (b : Fin 3 → F) : ↥(cayleyGroup F) :=
  ⟨LinearEquiv.ofInvolutive (ybLin b) (ybFun_ybFun b),
    ybFun_one b, ybFun_mul b, ybFun_tr b, ybFun_norm b⟩

theorem g2X_apply (a : Fin 3 → F) (x : quasithinZorn F) :
    (g2X a : quasithinZorn F ≃ₗ[F] quasithinZorn F) x = xaFun a x := rfl

theorem g2Y_apply (b : Fin 3 → F) (x : quasithinZorn F) :
    (g2Y b : quasithinZorn F ≃ₗ[F] quasithinZorn F) x = ybFun b x := rfl

theorem g2X_mul_self (a : Fin 3 → F) : g2X a * g2X a = 1 :=
  Subtype.ext (LinearEquiv.ext fun x => xaFun_xaFun a x)

theorem g2Y_mul_self (b : Fin 3 → F) : g2Y b * g2Y b = 1 :=
  Subtype.ext (LinearEquiv.ext fun x => ybFun_ybFun b x)

end Char2

section SL3

theorem cross_mulVec (M : Matrix (Fin 3) (Fin 3) F) (u x : Fin 3 → F) :
    quasithinCross (M *ᵥ u) (M *ᵥ x) = (adjugate M)ᵀ *ᵥ quasithinCross u x := by
  funext i
  fin_cases i <;>
    simp [quasithinCross, mulVec, dotProduct, Fin.sum_univ_three, adjugate_fin_three] <;> ring

theorem cross_adj_mulVec (M : Matrix (Fin 3) (Fin 3) F) (v y : Fin 3 → F) :
    quasithinCross ((adjugate M)ᵀ *ᵥ v) ((adjugate M)ᵀ *ᵥ y) =
      M.det • (M *ᵥ quasithinCross v y) := by
  rw [cross_mulVec, ← adjugate_transpose (adjugate M), transpose_transpose,
    adjugate_adjugate M (by simp), smul_mulVec]
  simp

theorem dot_adj_mulVec (M : Matrix (Fin 3) (Fin 3) F) (u y : Fin 3 → F) :
    (M *ᵥ u) ⬝ᵥ ((adjugate M)ᵀ *ᵥ y) = M.det * (u ⬝ᵥ y) := by
  rw [dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul, ← transpose_mul, adjugate_mul,
    transpose_smul, transpose_one, vecMul_smul, vecMul_one, smul_dotProduct, smul_eq_mul]

theorem dot_mulVec_adj (M : Matrix (Fin 3) (Fin 3) F) (v x : Fin 3 → F) :
    ((adjugate M)ᵀ *ᵥ v) ⬝ᵥ (M *ᵥ x) = M.det * (v ⬝ᵥ x) := by
  rw [dotProduct_comm, dot_adj_mulVec, dotProduct_comm]

@[expose] def gAFun (A : Matrix (Fin 3) (Fin 3) F) (x : quasithinZorn F) : quasithinZorn F :=
  (x.1, A *ᵥ x.2.1, (adjugate A)ᵀ *ᵥ x.2.2.1, x.2.2.2)

@[expose] def gALin (A : Matrix (Fin 3) (Fin 3) F) : quasithinZorn F →ₗ[F] quasithinZorn F where
  toFun := gAFun A
  map_add' x y := by
    simp only [gAFun, Prod.fst_add, Prod.snd_add, mulVec_add, Prod.mk_add_mk]
  map_smul' c x := by
    simp only [gAFun, Prod.smul_fst, Prod.smul_snd, mulVec_smul, RingHom.id_apply, Prod.smul_mk]

theorem gAFun_mul_mat (A B : Matrix (Fin 3) (Fin 3) F) (x : quasithinZorn F) :
    gAFun A (gAFun B x) = gAFun (A * B) x := by
  simp only [gAFun, mulVec_mulVec, adjugate_mul_distrib, transpose_mul]

theorem gAFun_one (x : quasithinZorn F) : gAFun 1 x = x := by
  simp [gAFun]

theorem gAFun_mul {A : Matrix (Fin 3) (Fin 3) F} (hA : A.det = 1) (x y : quasithinZorn F) :
    gAFun A (cayleyMul x y) = cayleyMul (gAFun A x) (gAFun A y) := by
  obtain ⟨r, u, v, s⟩ := x
  obtain ⟨t, x', y', z⟩ := y
  have hd : ∀ (a b : Fin 3 → F), ∑ i, a i * b i = a ⬝ᵥ b := fun a b => rfl
  simp only [gAFun, cayleyMul, hd, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [dot_adj_mulVec, hA, one_mul]
  · rw [cross_adj_mulVec, hA, one_smul, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul]
  · rw [cross_mulVec, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul]
  · rw [dot_mulVec_adj, hA, one_mul]

theorem gAFun_cayleyOne (A : Matrix (Fin 3) (Fin 3) F) : gAFun A (cayleyOne F) = cayleyOne F := by
  simp [gAFun, cayleyOne]

theorem gAFun_tr (A : Matrix (Fin 3) (Fin 3) F) (x : quasithinZorn F) :
    cayleyTr (gAFun A x) = cayleyTr x := rfl

theorem gAFun_norm {A : Matrix (Fin 3) (Fin 3) F} (hA : A.det = 1) (x : quasithinZorn F) :
    cayleyNorm (gAFun A x) = cayleyNorm x := by
  have hd : ∀ (a b : Fin 3 → F), ∑ i, a i * b i = a ⬝ᵥ b := fun a b => rfl
  simp only [cayleyNorm, gAFun, hd]
  rw [dot_adj_mulVec, hA, one_mul]

theorem sl3_mul_inv_coe (A : SL3 F) :
    (A : Matrix (Fin 3) (Fin 3) F) * ((A⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
  change ((A * A⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) = ((1 : SL3 F) : Matrix (Fin 3) (Fin 3) F)
  rw [mul_inv_cancel]

theorem sl3_inv_mul_coe (A : SL3 F) :
    ((A⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) = 1 := by
  change ((A⁻¹ * A : SL3 F) : Matrix (Fin 3) (Fin 3) F) = ((1 : SL3 F) : Matrix (Fin 3) (Fin 3) F)
  rw [inv_mul_cancel]

@[expose] def gAEquiv (A : SL3 F) : quasithinZorn F ≃ₗ[F] quasithinZorn F :=
  { gALin (A : Matrix (Fin 3) (Fin 3) F) with
    invFun := gAFun ((A⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F)
    left_inv := fun x => by
      change gAFun _ (gAFun _ x) = x
      rw [gAFun_mul_mat, sl3_inv_mul_coe, gAFun_one]
    right_inv := fun x => by
      change gAFun _ (gAFun _ x) = x
      rw [gAFun_mul_mat, sl3_mul_inv_coe, gAFun_one] }

@[expose] def g2AElt (A : SL3 F) : ↥(cayleyGroup F) :=
  ⟨gAEquiv A, gAFun_cayleyOne _, gAFun_mul A.2, gAFun_tr _, gAFun_norm A.2⟩

@[expose] def g2A : SL3 F →* ↥(cayleyGroup F) where
  toFun := g2AElt
  map_one' := Subtype.ext (LinearEquiv.ext fun x => by
    change gAFun ((1 : SL3 F) : Matrix (Fin 3) (Fin 3) F) x = x
    exact gAFun_one x)
  map_mul' A B := Subtype.ext (LinearEquiv.ext fun x => by
    change gAFun ((A * B : SL3 F) : Matrix (Fin 3) (Fin 3) F) x =
      gAFun (A : Matrix (Fin 3) (Fin 3) F) (gAFun (B : Matrix (Fin 3) (Fin 3) F) x)
    exact (gAFun_mul_mat _ _ x).symm)

theorem g2A_apply (A : SL3 F) (x : quasithinZorn F) :
    (g2A A : quasithinZorn F ≃ₗ[F] quasithinZorn F) x = gAFun (A : Matrix (Fin 3) (Fin 3) F) x :=
  rfl

end SL3

section Relations

variable [CharP F 2]

omit [CharP F 2] in
theorem xaFun_vec (a : Fin 3 → F) (x : quasithinZorn F) :
    xaFun a x = (x.1 + a ⬝ᵥ x.2.2.1, x.2.1 + (x.1 + x.2.2.2 + a ⬝ᵥ x.2.2.1) • a,
      x.2.2.1 + quasithinCross a x.2.1, x.2.2.2 + a ⬝ᵥ x.2.2.1) := by
  simp only [xaFun, zmk, dotProduct, Fin.sum_univ_three, Prod.mk.injEq]
  refine ⟨trivial, ?_, ?_, trivial⟩ <;> funext i <;> fin_cases i <;> simp [quasithinCross]

omit [CharP F 2] in
theorem ybFun_vec (b : Fin 3 → F) (x : quasithinZorn F) :
    ybFun b x = (x.1 + b ⬝ᵥ x.2.1, x.2.1 + quasithinCross b x.2.2.1,
      x.2.2.1 + (x.1 + x.2.2.2 + b ⬝ᵥ x.2.1) • b, x.2.2.2 + b ⬝ᵥ x.2.1) := by
  simp only [ybFun, zmk, dotProduct, Fin.sum_univ_three, Prod.mk.injEq]
  refine ⟨trivial, ?_, ?_, trivial⟩ <;> funext i <;> fin_cases i <;> simp [quasithinCross]

theorem g2A_mul_g2X (A : SL3 F) (a : Fin 3 → F) :
    g2A A * g2X a = g2X ((A : Matrix (Fin 3) (Fin 3) F) *ᵥ a) * g2A A := by
  refine Subtype.ext (LinearEquiv.ext fun x => ?_)
  change gAFun (A : Matrix (Fin 3) (Fin 3) F) (xaFun a x) =
    xaFun ((A : Matrix (Fin 3) (Fin 3) F) *ᵥ a) (gAFun (A : Matrix (Fin 3) (Fin 3) F) x)
  have hA : (A : Matrix (Fin 3) (Fin 3) F).det = 1 := A.2
  rw [xaFun_vec, xaFun_vec]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · simp only [gAFun]
    rw [dot_adj_mulVec, hA, one_mul]
  · simp only [gAFun]
    rw [dot_adj_mulVec, hA, one_mul, mulVec_add, mulVec_smul]
  · simp only [gAFun]
    rw [cross_mulVec, mulVec_add]
  · simp only [gAFun]
    rw [dot_adj_mulVec, hA, one_mul]

theorem g2A_mul_g2Y (A : SL3 F) (b : Fin 3 → F) :
    g2A A * g2Y b = g2Y ((adjugate (A : Matrix (Fin 3) (Fin 3) F))ᵀ *ᵥ b) * g2A A := by
  refine Subtype.ext (LinearEquiv.ext fun x => ?_)
  change gAFun (A : Matrix (Fin 3) (Fin 3) F) (ybFun b x) =
    ybFun ((adjugate (A : Matrix (Fin 3) (Fin 3) F))ᵀ *ᵥ b)
      (gAFun (A : Matrix (Fin 3) (Fin 3) F) x)
  have hA : (A : Matrix (Fin 3) (Fin 3) F).det = 1 := A.2
  rw [ybFun_vec, ybFun_vec]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · simp only [gAFun]
    rw [dot_mulVec_adj, hA, one_mul]
  · simp only [gAFun]
    rw [cross_adj_mulVec, hA, one_smul, mulVec_add]
  · simp only [gAFun]
    rw [dot_mulVec_adj, hA, one_mul, mulVec_add, mulVec_smul]
  · simp only [gAFun]
    rw [dot_mulVec_adj, hA, one_mul]

end Relations

end CFSG.Quasithin.JonesParshall
