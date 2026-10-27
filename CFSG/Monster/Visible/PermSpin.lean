module

public import CFSG.Monster.Visible.PermBeta
public import CFSG.Monster.Spin.Extraspecial

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Visible

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.Lifts Matrix

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

private theorem two_eq_zero' : (2 : ZMod 2) = 0 := rfl

private theorem one_add_one' : (1 : ZMod 2) + 1 = 0 := rfl

private theorem sgn_one' : sgn 1 = -1 := rfl

theorem matrix_eq_of_Fvec_vecMul {M N : Matrix SpinIdx SpinIdx ℚ}
    (h : ∀ u : C, Fvec u ᵥ* M = Fvec u ᵥ* N) : M = N := by
  have key : toLin' Mᵀ = toLin' Nᵀ := Fbasis.ext fun u => by
    rw [toLin'_apply, toLin'_apply, mulVec_transpose, mulVec_transpose, coe_Fbasis, h]
  have := congrArg transpose (toLin'.injective key)
  rwa [transpose_transpose, transpose_transpose] at this

theorem E_eq_Fvec (η : ZMod 2) (c : C₀) :
    E η c = (1 / 2 : ℚ) • (Fvec (c : C) + sgn η • Fvec ((c : C) + ΩC)) := by
  rcases zmod2_cases η with rfl | rfl
  · rw [E_zero_eq, sgn_zero, one_smul]
  · rw [E_one_eq, sgn_one', neg_one_smul, ← sub_eq_add_neg]

private theorem combo (c' : C₀) (η ε t : ZMod 2) :
    (1 / 2 : ℚ) • ((E 0 c' + sgn t • E 1 c') + sgn η • sgn ε • (E 0 c' + sgn (t + 1) • E 1 c')) =
      sgn ((η + ε) * t) • E (η + ε) c' := by
  rcases zmod2_cases η with rfl | rfl <;> rcases zmod2_cases ε with rfl | rfl <;>
    rcases zmod2_cases t with rfl | rfl <;>
    simp only [sgn_zero, sgn_one', one_add_one', zero_add, add_zero, mul_zero, mul_one,
      one_smul, neg_one_smul] <;>
    module

private theorem E_vecMul_smat_aux (p : AutPerm) (η : ZMod 2) (c c' : C₀) (t : ZMod 2)
    (hu : permC p (c : C) = (c' : C) + t • ΩC) :
    E η c ᵥ* smat p = sgn (kappaP p c + (η + kappaP p ΩC) * t) • E (η + kappaP p ΩC) c' := by
  have hu' : permC p ((c : C) + ΩC) = (c' : C) + (t + 1) • ΩC := by
    rw [map_add, permC_ΩC, hu, add_smul, one_smul, add_assoc]
  rw [E_eq_Fvec η c, smul_vecMul, add_vecMul, smul_vecMul, Fvec_vecMul_smat p (c : C),
    Fvec_vecMul_smat p ((c : C) + ΩC), kappaP_add_ΩC p c, hu, hu', Fvec_add_smul_ΩC c' t,
    Fvec_add_smul_ΩC c' (t + 1), sgn_add (kappaP p c) (kappaP p ΩC),
    sgn_add (kappaP p c) ((η + kappaP p ΩC) * t),
    mul_smul (sgn (kappaP p c)) _ (E (η + kappaP p ΩC) c'), ← combo c' η (kappaP p ΩC) t]
  module

theorem E_vecMul_smat (p : AutPerm) (η : ZMod 2) (c : C₀) :
    E η c ᵥ* smat p = sgn (kappaP p c + (η + kappaP p ΩC) * μ₀ (permC p c)) •
      E (η + kappaP p ΩC) (π₀ (permC p c)) :=
  E_vecMul_smat_aux p η c (π₀ (permC p c)) (μ₀ (permC p c)) (π₀_add_μ₀ _).symm

@[expose] def sPerm (p : AutPerm) (i : SpinIdx) : SpinIdx :=
  (i.1 + kappaP p ΩC, π₀ (permC p i.2))

@[expose] def sSign (p : AutPerm) (i : SpinIdx) : ZMod 2 :=
  kappaP p i.2 + (i.1 + kappaP p ΩC) * μ₀ (permC p i.2)

theorem smat_eq_spm (p : AutPerm) : smat p = spm ℚ (sPerm p) (sSign p) := by
  ext i j
  have h := congrFun (E_vecMul_smat p i.1 i.2) j
  rw [E, single_one_vecMul] at h
  rw [spm_apply]
  have hi : (i.1, i.2) = i := rfl
  rw [hi, row_apply] at h
  rw [h, Pi.smul_apply, E, Pi.single_apply, smul_eq_mul, sgnR_rat]
  have hσ : (i.1 + kappaP p ΩC, π₀ (permC p i.2)) = sPerm p i := rfl
  rw [hσ]
  by_cases hj : j = sPerm p i
  · rw [ite_eq_left hj, ite_eq_left hj, mul_one]
    rfl
  · rw [ite_eq_right hj, ite_eq_right hj, mul_zero]

theorem π₀_permC_inv_π₀_permC (p : AutPerm) (c : C₀) :
    π₀ (permC p⁻¹ (π₀ (permC p c) : C)) = c := by
  rw [coe_π₀, map_add, map_smul, ← permC_symm_apply, LinearEquiv.symm_apply_apply,
    permC_ΩC, map_add, map_smul, π₀_coe, π₀_ΩC, smul_zero, add_zero]

theorem sPerm_bijective (p : AutPerm) : Function.Bijective (sPerm p) := by
  refine Finite.injective_iff_bijective.1 fun i j h => ?_
  have h1 := congrArg Prod.fst h
  have h2 := congrArg (fun x : SpinIdx => π₀ (permC p⁻¹ (x.2 : C))) h
  simp only [sPerm, add_left_inj] at h1
  simp only [sPerm, π₀_permC_inv_π₀_permC] at h2
  exact Prod.ext h1 h2

theorem Dmat_mul_smat (p : AutPerm) (δ : Cocode) :
    Dmat δ * smat p = smat p * Dmat (permD p δ) := by
  refine matrix_eq_of_Fvec_vecMul fun u => ?_
  rw [← vecMul_vecMul, ← vecMul_vecMul, Fvec_vecMul_Dmat u δ, smul_vecMul,
    Fvec_vecMul_smat p u, smul_vecMul, Fvec_vecMul_Dmat (permC p u) (permD p δ), smul_smul,
    smul_smul, pair_permC_permD, mul_comm]

private theorem sgn_smul_smul_eq {V : Type*} [AddCommGroup V] [Module ℚ V] {x y z w v : ZMod 2}
    (F : V) (h : x + y = z + w + v) : sgn x • sgn y • F = sgn z • sgn w • sgn v • F := by
  rw [smul_smul, smul_smul, smul_smul, ← sgn_add, ← sgn_add, ← sgn_add, h]

theorem Xmat_smat_sign (p : AutPerm) (e : Parker) (u : C) :
    e.sign + P (e.code : Fin 24 → ZMod 2) + θ e.code u + kappaP p (u + e.code) =
      kappaP p e.code + kappaP p u +
        (e.sign + P (permC p e.code : Fin 24 → ZMod 2) + θ (permC p e.code) (permC p u)) := by
  have hk := kappaP_add p u e.code
  have h1 := θ_add_θ_swap e.code u
  have h2 := θ_add_θ_swap (permC p e.code) (permC p u)
  rw [coe_permC, coe_permC, K_permWord] at h2
  have hP : P (permC p e.code : Fin 24 → ZMod 2) = P (e.code : Fin 24 → ZMod 2) := by
    rw [coe_permC, P_permWord]
  rw [hP]
  unfold betaP at hk
  linear_combination hk + h1 - h2 +
    (θ (permC p u) (permC p e.code) - kappaP p u - kappaP p e.code) * two_eq_zero'

theorem Xmat_mul_smat (p : AutPerm) (e : Parker) :
    Xmat e * smat p = sgn (kappaP p e.code) • (smat p * Xmat ⟨permC p e.code, e.sign⟩) := by
  refine matrix_eq_of_Fvec_vecMul fun u => ?_
  have hX : Fvec (permC p u) ᵥ* Xmat ⟨permC p e.code, e.sign⟩ =
      sgn (e.sign + P (permC p e.code : Fin 24 → ZMod 2) + θ (permC p e.code) (permC p u)) •
        Fvec (permC p u + permC p e.code) := Fvec_vecMul_Xmat _ _
  rw [← vecMul_vecMul, vecMul_smul, ← vecMul_vecMul, Fvec_vecMul_Xmat u e, smul_vecMul,
    Fvec_vecMul_smat p (u + e.code), Fvec_vecMul_smat p u, smul_vecMul, hX, map_add]
  exact sgn_smul_smul_eq _ (Xmat_smat_sign p e u)

theorem zmat_pow_val (k : ZMod 2) : zmat ^ k.val = sgn k • (1 : Matrix SpinIdx SpinIdx ℚ) := by
  rcases zmod2_cases k with rfl | rfl
  · rw [ZMod.val_zero, pow_zero, sgn_zero, one_smul]
  · rw [ZMod.val_one, pow_one, zmat, sgn_one', neg_one_smul]

theorem smat_transpose_mul_Dmat_mul_smat (p : AutPerm) (δ : Cocode) :
    (smat p)ᵀ * Dmat δ * smat p = Dmat (permD p δ) := by
  rw [Matrix.mul_assoc, Dmat_mul_smat, ← Matrix.mul_assoc, smat_transpose_mul_self,
    Matrix.one_mul]

theorem smat_transpose_mul_Xmat_mul_smat (p : AutPerm) (e : Parker) :
    (smat p)ᵀ * Xmat e * smat p = sgn (kappaP p e.code) • Xmat ⟨permC p e.code, e.sign⟩ := by
  rw [Matrix.mul_assoc, Xmat_mul_smat, Matrix.mul_smul, ← Matrix.mul_assoc,
    smat_transpose_mul_self, Matrix.one_mul]

theorem coe_sU_inv (p : AutPerm) :
    (((sU p)⁻¹ : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) = (smat p)ᵀ := rfl

theorem sU_conj_DU (p : AutPerm) (δ : Cocode) : (sU p)⁻¹ * DU δ * sU p = DU (permD p δ) :=
  Units.ext (smat_transpose_mul_Dmat_mul_smat p δ)

theorem sU_conj_XU (p : AutPerm) (e : Parker) :
    (sU p)⁻¹ * XU e * sU p = zU ^ (kappaP p e.code).val * XU ⟨permC p e.code, e.sign⟩ := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_sU_inv, coe_sU, coe_XU, coe_XU, coe_zU_pow,
    smat_transpose_mul_Xmat_mul_smat, zmat_pow_val, Matrix.smul_mul, Matrix.one_mul]

@[expose] def conjGL (s : GL SpinIdx ℚ) : GL SpinIdx ℚ →* GL SpinIdx ℚ :=
  MonoidHom.mk' (fun r => s⁻¹ * r * s) fun a b => by
    simp only [mul_assoc, mul_inv_cancel_left]

theorem conjGL_apply (s r : GL SpinIdx ℚ) : conjGL s r = s⁻¹ * r * s := rfl

theorem conjGL_injective (s : GL SpinIdx ℚ) : Function.Injective (conjGL s) := fun a b h => by
  simpa only [conjGL_apply, mul_left_inj, mul_right_inj] using h

theorem map_conjGL_sU_le (p : AutPerm) : Q.map (conjGL (sU p)) ≤ Q := by
  have e : Q.map (conjGL (sU p)) =
      Subgroup.closure (conjGL (sU p) '' (Set.range XU ∪ Set.range DU)) :=
    MonoidHom.map_closure _ _
  rw [e, Subgroup.closure_le]
  rintro _ ⟨x, hx | hx, rfl⟩
  · obtain ⟨f, rfl⟩ := hx
    have h : zU ^ (kappaP p f.code).val * XU ⟨permC p f.code, f.sign⟩ ∈ Q :=
      Q.mul_mem (Q.pow_mem zU_mem_Q _) (XU_mem_Q _)
    exact (congrArg (· ∈ Q) (sU_conj_XU p f)).mpr h
  · obtain ⟨δ, rfl⟩ := hx
    exact (congrArg (· ∈ Q) (sU_conj_DU p δ)).mpr (DU_mem_Q _)

theorem map_conjGL_sU (p : AutPerm) : Q.map (conjGL (sU p)) = Q := by
  have : Finite Q := Nat.finite_of_card_ne_zero (by rw [natCard_Q]; positivity)
  refine Subgroup.eq_of_le_of_card_ge (map_conjGL_sU_le p) ?_
  rw [Subgroup.card_map_of_injective (conjGL_injective _)]

theorem sU_conj_mem_Q_iff (p : AutPerm) (r : GL SpinIdx ℚ) : r ∈ Q ↔ (sU p)⁻¹ * r * sU p ∈ Q := by
  constructor
  · intro hr
    exact map_conjGL_sU_le p ⟨r, hr, rfl⟩
  · intro hr
    rw [← map_conjGL_sU p] at hr
    obtain ⟨r₀, hr₀, he⟩ := hr
    rw [conjGL_injective _ (he.trans (conjGL_apply _ _).symm)] at hr₀
    exact hr₀

theorem image_sU_conj_Q (p : AutPerm) :
    (fun r => (sU p)⁻¹ * r * sU p) '' (Q : Set (GL SpinIdx ℚ)) = Q := by
  have h := congrArg (fun H : Subgroup (GL SpinIdx ℚ) => (H : Set (GL SpinIdx ℚ)))
    (map_conjGL_sU p)
  simp only [Subgroup.coe_map] at h
  exact h

end CFSG.Monster.Visible
