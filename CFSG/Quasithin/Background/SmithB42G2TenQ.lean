module

public import CFSG.Quasithin.Vol2.Ch11G2Q8Uni
public import CFSG.Quasithin.Vol2.Ch11G2Q8Comm

public noncomputable section

namespace CFSG.Quasithin.B42G2Ten

open Matrix CFSG.Open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.Ch11.G2Q8

variable {F : Type} [Field F]

section Rep

variable [CharP F 2]

@[expose] def linQ (g : ↥(cayleyGroup F)) : (Ix3 → F) →ₗ[F] (Ix3 → F) where
  toFun := g2Act g
  map_add' := map_add (g2Act g)
  map_smul' c w := JonesParshall.g2Act_smul g c w

theorem linQ_apply (g : ↥(cayleyGroup F)) (w : Ix3 → F) : linQ g w = g2Act g w := rfl

@[expose] def repQ : ↥(cayleyGroup F) →* Matrix Ix3 Ix3 F where
  toFun g := LinearMap.toMatrix' (linQ g)
  map_one' := by
    have e : linQ (1 : ↥(cayleyGroup F)) = LinearMap.id := LinearMap.ext fun w => by
      rw [linQ_apply, map_one]
      rfl
    rw [e, LinearMap.toMatrix'_id]
  map_mul' g h := by
    have e : linQ (g * h) = (linQ g).comp (linQ h) := LinearMap.ext fun w => by
      rw [linQ_apply, map_mul]
      rfl
    rw [e, LinearMap.toMatrix'_comp]

theorem repQ_mulVec (g : ↥(cayleyGroup F)) (w : Ix3 → F) : (repQ g).mulVec w = g2Act g w :=
  LinearMap.toMatrix'_mulVec (linQ g) w

theorem repQ_apply (g : ↥(cayleyGroup F)) (i j : Ix3) :
    repQ g i j = g2Act g (Pi.single j 1) i := by
  rw [← repQ_mulVec, Matrix.mulVec_single_one]
  rfl

end Rep

@[expose] def swapFun (x : quasithinZorn F) : quasithinZorn F := (x.2.2.2, x.2.2.1, x.2.1, x.1)

omit [Field F] in
theorem swapFun_swapFun (x : quasithinZorn F) : swapFun (swapFun x) = x := rfl

@[expose] def swapLin : quasithinZorn F →ₗ[F] quasithinZorn F where
  toFun := swapFun
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem swapFun_one : swapFun (cayleyOne F) = cayleyOne F := rfl

theorem swapFun_mul (x y : quasithinZorn F) :
    swapFun (cayleyMul x y) = cayleyMul (swapFun x) (swapFun y) := by
  simp only [swapFun, cayleyMul]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl)) <;> dsimp only <;> abel

theorem swapFun_tr (x : quasithinZorn F) : cayleyTr (swapFun x) = cayleyTr x := by
  simp only [swapFun, cayleyTr]
  ring

theorem swapFun_norm (x : quasithinZorn F) : cayleyNorm (swapFun x) = cayleyNorm x := by
  simp only [swapFun, cayleyNorm]
  rw [mul_comm]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

@[expose] def g2Sw : ↥(cayleyGroup F) :=
  ⟨LinearEquiv.ofInvolutive swapLin swapFun_swapFun, swapFun_one, swapFun_mul, swapFun_tr,
    swapFun_norm⟩

theorem g2Sw_apply (x : quasithinZorn F) :
    ((g2Sw : ↥(cayleyGroup F)) : quasithinZorn F ≃ₗ[F] quasithinZorn F) x = swapFun x := rfl

theorem g2Sw_mul_self : (g2Sw : ↥(cayleyGroup F)) * g2Sw = 1 :=
  Subtype.ext (LinearEquiv.ext fun x => swapFun_swapFun x)

section Swap

variable [CharP F 2]

theorem g2Act_g2Sw (w : Ix3 → F) : g2Act g2Sw w = fun i => w i.swap := by
  funext i
  rw [g2Act_apply]
  rcases i with i | i <;> fin_cases i <;> rfl

@[expose] def formQ (F : Type) [Field F] : Matrix Ix3 Ix3 F :=
  Matrix.of fun i j => if j = i.swap then 1 else 0

omit [CharP F 2] in
theorem formQ_apply (i j : Ix3) : formQ F i j = if j = i.swap then (1 : F) else 0 := rfl

theorem repQ_g2Sw : repQ (g2Sw : ↥(cayleyGroup F)) = formQ F := by
  ext i j
  rw [repQ_apply, g2Act_g2Sw, formQ_apply]
  simp only [Pi.single_apply]
  exact if_congr eq_comm rfl rfl

omit [CharP F 2] in
theorem formQ_mul {κ : Type*} (M : Matrix Ix3 κ F) : formQ F * M = M.submatrix Sum.swap id := by
  ext i b
  rw [Matrix.mul_apply]
  simp [formQ_apply]

omit [CharP F 2] in
theorem bilQ_eq_sum (w w' : Ix3 → F) : bilQ w w' = ∑ i, w i * w' i.swap := by
  simp only [bilQ, Fintype.sum_sum_type, Fin.sum_univ_three, Sum.swap_inl, Sum.swap_inr]
  ring

omit [CharP F 2] in
theorem dotProduct_formQ (w w' : Ix3 → F) : w ⬝ᵥ (formQ F).mulVec w' = bilQ w w' := by
  rw [bilQ_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  simp only [Matrix.mulVec, dotProduct, formQ_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem repQ_transpose_formQ (g : ↥(cayleyGroup F)) :
    (repQ g)ᵀ * formQ F * repQ g = formQ F := by
  ext a b
  have h := bilQ_g2Act g (Pi.single a 1) (Pi.single b 1)
  rw [bilQ_eq_sum, bilQ_eq_sum] at h
  rw [Matrix.mul_assoc, formQ_mul, Matrix.mul_apply]
  simp only [Matrix.transpose_apply, Matrix.submatrix_apply, id]
  simp only [← repQ_apply] at h
  rw [h, formQ_apply, Finset.sum_eq_single a]
  · simp only [Pi.single_eq_same, one_mul, Pi.single_apply]
    exact if_congr eq_comm rfl rfl
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi, zero_mul]
  · intro h'
    exact absurd (Finset.mem_univ a) h'

theorem formQ_mul_repQ (g : ↥(cayleyGroup F)) :
    formQ F * repQ g = (repQ g⁻¹)ᵀ * formQ F := by
  have h := repQ_transpose_formQ (F := F) g⁻¹
  have e : repQ g⁻¹ * repQ g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  calc formQ F * repQ g = (repQ g⁻¹)ᵀ * formQ F * repQ g⁻¹ * repQ g := by rw [h]
    _ = (repQ g⁻¹)ᵀ * formQ F := by rw [Matrix.mul_assoc, e, Matrix.mul_one]

theorem formQ_mul_self : formQ F * formQ F = 1 := by
  rw [← repQ_g2Sw, ← map_mul, g2Sw_mul_self, map_one]

end Swap

section U0

variable [CharP F 2]

omit [CharP F 2] in
theorem inF_single_succ (j : Ix3) : InF (ht j + 1) (Pi.single j (1 : F)) := by
  intro i hi
  rw [Pi.single_apply, ite_eq_right]
  rintro rfl
  omega

theorem repQ_U0_apply {u : ↥(cayleyGroup F)} (hu : u ∈ U0 F) {i j : Ix3} (hij : ht j ≤ ht i) :
    repQ u i j = if i = j then 1 else 0 := by
  have h := (mem_U0.mp hu) (ht j) (Pi.single j 1) (inF_single_succ j) i hij
  rw [Pi.sub_apply, sub_eq_zero] at h
  rw [repQ_apply, h, Pi.single_apply]

theorem g2Act_U0_single_u0 {u : ↥(cayleyGroup F)} (hu : u ∈ U0 F) :
    g2Act u (Pi.single (.inl 0) 1) = Pi.single (.inl 0) (1 : F) := by
  funext i
  have h := repQ_U0_apply hu (i := i) (j := .inl 0) (Nat.zero_le _)
  rw [repQ_apply] at h
  rw [h, Pi.single_apply]

end U0

end CFSG.Quasithin.B42G2Ten
