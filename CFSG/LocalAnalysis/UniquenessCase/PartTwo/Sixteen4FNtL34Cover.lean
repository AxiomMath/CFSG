module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtCover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtTwoGen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtL34Gen
public import CFSG.Quasithin.Background.SmithB45Sp4Herm
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtL34CoverAux2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.Quasithin.JonesParshall CFSG.Fischer Matrix
open CFSG.Quasithin.H13.Ch9.Herm9 CFSG.Quasithin.H CFSG.Quasithin.H.L3W9 CFSG.Quasithin.H.L3Nine

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

private theorem w183_l34_sec_sq_one {K : Type} [Field K] [CharP K 2] :
    ∀ y : ↥(hermSub 1 (Fin 3) K), y * y = 1 := by
  intro y
  apply Subtype.ext
  show (y : Multiplicative (Matrix (Fin 3) (Fin 3) K)) * y = 1
  rw [show (y : Multiplicative (Matrix (Fin 3) (Fin 3) K)) * y =
    Multiplicative.ofAdd (Multiplicative.toAdd
        (y : Multiplicative (Matrix (Fin 3) (Fin 3) K)) +
      Multiplicative.toAdd (y : Multiplicative (Matrix (Fin 3) (Fin 3) K))) from rfl]
  rw [show Multiplicative.toAdd (y : Multiplicative (Matrix (Fin 3) (Fin 3) K)) +
      Multiplicative.toAdd (y : Multiplicative (Matrix (Fin 3) (Fin 3) K)) = 0 from by
    ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero _]
  rfl

private theorem w183_l34_mod_sq_one {K : Type} [Field K] [CharP K 2] :
    ∀ x : (FFModel.twistTensor 1 (StatedSL 3 K)).Mod, x * x = 1 := by
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  have h : y * y = 1 := w183_l34_sec_sq_one y
  have h1 : ((y * y : ↥(FFModel.twistTensor 1 (StatedSL 3 K)).sec) :
      (FFModel.twistTensor 1 (StatedSL 3 K)).Mod) = 1 := by rw [h]; rfl
  exact h1

noncomputable instance w183_l34_module {K : Type} [Field K] [CharP K 2] :
    Module (ZMod 2) (Additive (FFModel.twistTensor 1 (StatedSL 3 K)).Mod) :=
  AddCommGroup.zmodModule (fun a => by
    apply Multiplicative.ofAdd.injective
    show Additive.toMul a ^ 2 = 1
    rw [sq]
    exact w183_l34_mod_sq_one (K := K) (Additive.toMul a))

noncomputable def w183_l34Rep {K : Type} [Field K] [CharP K 2]
    (hD : (FFModel.twistTensor 1 (StatedSL 3 K)).IsActionModel) :
    Representation (ZMod 2) ↥(StatedSL 3 K)
      (Additive (FFModel.twistTensor 1 (StatedSL 3 K)).Mod) :=
  { toFun := fun γ =>
      AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditive (hD.modAct γ : _ →* _))
    map_one' := by
      ext x
      exact congrArg Additive.ofMul
        (congrArg (fun f : MulAut _ => f (Additive.toMul x)) (map_one hD.modAct))
    map_mul' γ δ := by
      ext x
      exact congrArg Additive.ofMul
        (congrArg (fun f : MulAut _ => f (Additive.toMul x)) (map_mul hD.modAct γ δ)) }

noncomputable def w183_l34ModEquiv {K : Type} [Field K] [CharP K 2] :
    (FFModel.twistTensor 1 (StatedSL 3 K)).Mod ≃*
      Multiplicative (Additive (FFModel.twistTensor 1 (StatedSL 3 K)).Mod) :=
  (AddEquiv.refl (Additive (FFModel.twistTensor 1 (StatedSL 3 K)).Mod)).toMultiplicativeRight

private theorem w183_l34_F4_root_cases :
    ∀ x : F4, x ^ 2 + x + 1 = 0 → x = F4.ω ∨ x = F4.ω ^ 2 := by
  intro x hx
  obtain ⟨c⟩ := x
  fin_cases c
  · exfalso
    rw [pow_two, F4.mul_def, F4.add_def, F4.mk.injEq] at hx
    exact absurd hx (by decide)
  · exfalso
    rw [pow_two, F4.mul_def, F4.add_def, F4.mk.injEq] at hx
    exact absurd hx (by decide)
  · left; rfl
  · right
    rw [pow_two, F4.mul_def, F4.mk.injEq]
    decide

private noncomputable def w183_l34_linEquiv {K : Type} [Field K] [Finite K] [CharP K 2]
    (φ : K ≃+* F4) :
    Additive (FFModel.twistTensor 1 (StatedSL 3 K)).Mod ≃ₗ[ZMod 2] (Fin 9 → ZMod 2) := by
  let e : Additive (FFModel.twistTensor 1 (StatedSL 3 K)).Mod ≃+ (Fin 9 → ZMod 2) :=
    (MulEquiv.toAdditive (w183_l34Aux2_modEquiv (K := K) φ)).trans
      (AddEquiv.additiveMultiplicative (Fin 9 → ZMod 2))
  exact e.toLinearEquiv fun c x => ZMod.map_smul e.toAddMonoidHom c x

private theorem w183_l34_linEquiv_apply {K : Type} [Field K] [Finite K] [CharP K 2]
    (φ : K ≃+* F4) (x : Additive (FFModel.twistTensor 1 (StatedSL 3 K)).Mod) :
    w183_l34_linEquiv (K := K) φ x =
      Multiplicative.toAdd ((w183_l34Aux2_modEquiv (K := K) φ) (Additive.toMul x)) := rfl

private theorem w183_l34_toMul_rep {K : Type} [Field K] [CharP K 2]
    (hD : (FFModel.twistTensor 1 (StatedSL 3 K)).IsActionModel)
    (γ : ↥(StatedSL 3 K)) (x : Additive (FFModel.twistTensor 1 (StatedSL 3 K)).Mod) :
    Additive.toMul (w183_l34Rep (K := K) hD γ x) = hD.modAct γ (Additive.toMul x) := rfl

private theorem w183_l34_linEquiv_intertwine {K : Type} [Field K] [Finite K] [CharP K 2]
    (hD : (FFModel.twistTensor 1 (StatedSL 3 K)).IsActionModel)
    (hK : Nat.card K = 4) (φ : K ≃+* F4) (γ : ↥(StatedSL 3 K)) :
    ∀ x : Additive (FFModel.twistTensor 1 (StatedSL 3 K)).Mod,
      w183_l34_linEquiv (K := K) φ (w183_l34Rep (K := K) hD γ x) =
        (w183_l34Aux2_colMat (cols ((mapGLF φ γ : GL (Fin 3) F4) :
          Matrix (Fin 3) (Fin 3) F4))).mulVecLin
          (w183_l34_linEquiv (K := K) φ x) := by
  intro x
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
  have hx : x = Additive.ofMul (QuotientGroup.mk m) := by
    rw [hm]
    exact (ofMul_toMul x).symm
  rw [hx, w183_l34_linEquiv_apply, w183_l34_toMul_rep]
  simp only [toMul_ofMul]
  rw [w183_l34Aux2_intertwine (K := K) hD hK φ γ m]
  rw [w183_l34_linEquiv_apply, toMul_ofMul, w183_l34Aux2_toAdd_rho9,
    Matrix.mulVecLin_apply]

private theorem w183_l34_mulVecLin_pow (C : Matrix (Fin 9) (Fin 9) (ZMod 2)) (n : ℕ) :
    (C ^ n).mulVecLin = C.mulVecLin ^ n := by
  induction n with
  | zero =>
      rw [pow_zero, pow_zero, Matrix.mulVecLin_one]
      rfl
  | succ n ih =>
      rw [pow_succ, pow_succ, Matrix.mulVecLin_mul, ih]
      rfl

private theorem w183_l34_sum_mulVecLin (C : Matrix (Fin 9) (Fin 9) (ZMod 2)) (n : ℕ) :
    (∑ i ∈ Finset.range n, C ^ i).mulVecLin = ∑ i ∈ Finset.range n, C.mulVecLin ^ i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Matrix.mulVecLin_add,
        w183_l34_mulVecLin_pow, ih]

private theorem w183_l34_sum_range_three (C : Matrix (Fin 9) (Fin 9) (ZMod 2)) :
    (∑ i ∈ Finset.range 3, C ^ i) = 1 + C + C ^ 2 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  simp

private theorem w183_l34_finrank_norm_three (C : Matrix (Fin 9) (Fin 9) (ZMod 2)) :
    Module.finrank (ZMod 2)
        (LinearMap.range (∑ i ∈ Finset.range 3, C.mulVecLin ^ i)) =
      (1 + C + C ^ 2).rank := by
  rw [← w183_l34_sum_mulVecLin, w183_l34_sum_range_three,
    w183_l34Aux2_finrank_range_mulVecLin]

private theorem w183_l34_dualMap_mulVecLin_apply {n : ℕ}
    (C : Matrix (Fin n) (Fin n) (ZMod 2)) (v : Fin n → ZMod 2) :
    (C.mulVecLin).dualMap (dotProductEquiv (ZMod 2) (Fin n) v) =
      dotProductEquiv (ZMod 2) (Fin n) ((Cᵀ).mulVec v) := by
  apply LinearMap.ext
  intro w
  rw [LinearMap.dualMap_apply, Matrix.mulVecLin_apply]
  show (dotProductEquiv (ZMod 2) (Fin n) v) (C.mulVec w) =
    (dotProductEquiv (ZMod 2) (Fin n) ((Cᵀ).mulVec v)) w
  simp only [dotProductEquiv_apply_apply]
  calc v ⬝ᵥ (C.mulVec w)
      = v ⬝ᵥ ((Cᵀ)ᵀ.mulVec w) := by rw [Matrix.transpose_transpose]
    _ = w ⬝ᵥ ((Cᵀ).mulVec v) := Matrix.dotProduct_transpose_mulVec Cᵀ v w
    _ = ((Cᵀ).mulVec v) ⬝ᵥ w := dotProduct_comm _ _

private theorem w183_l34_fix_vec_to_dual (C₁ C₂ : Matrix (Fin 9) (Fin 9) (ZMod 2))
    (hfix : ∀ f : Fin 9 → ZMod 2, (C₁ᵀ).mulVec f = f → (C₂ᵀ).mulVec f = f → f = 0) :
    ∀ f : (Fin 9 → ZMod 2) →ₗ[ZMod 2] ZMod 2,
      (C₁.mulVecLin).dualMap f = f → (C₂.mulVecLin).dualMap f = f → f = 0 := by
  intro f hf₁ hf₂
  set v : Fin 9 → ZMod 2 := (dotProductEquiv (ZMod 2) (Fin 9)).symm f with hv_def
  have hv₁ : (C₁ᵀ).mulVec v = v := by
    apply (dotProductEquiv (ZMod 2) (Fin 9)).injective
    rw [← w183_l34_dualMap_mulVecLin_apply]
    rw [hv_def, LinearEquiv.apply_symm_apply]
    exact hf₁
  have hv₂ : (C₂ᵀ).mulVec v = v := by
    apply (dotProductEquiv (ZMod 2) (Fin 9)).injective
    rw [← w183_l34_dualMap_mulVecLin_apply]
    rw [hv_def, LinearEquiv.apply_symm_apply]
    exact hf₂
  have h0 := hfix v hv₁ hv₂
  rw [← (dotProductEquiv (ZMod 2) (Fin 9)).apply_symm_apply f, ← hv_def, h0, map_zero]

private theorem w183_l34_dual_fix_iff {Γ Q : Type} [Group Γ] [AddCommGroup Q]
    [Module (ZMod 2) Q] (ρ : Representation (ZMod 2) Γ Q) (g : Γ)
    (q : Module.Dual (ZMod 2) Q) :
    (Representation.dual ρ g) q = q ↔ (ρ g).dualMap q = q := by
  have hdual : Representation.dual ρ g = (ρ g⁻¹).dualMap := by
    rw [Representation.dual_apply, LinearMap.dualMap_def]
  rw [hdual]
  constructor
  · intro h
    ext x
    rw [LinearMap.dualMap_apply]
    have hx := DFunLike.congr_fun h (ρ g x)
    simp only [LinearMap.comp_apply, LinearMap.dualMap_apply] at hx
    have h1 : (ρ g⁻¹) (ρ g x) = x := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [h1] at hx
    exact hx.symm
  · intro h
    ext x
    rw [LinearMap.dualMap_apply]
    have hx := DFunLike.congr_fun h (ρ g⁻¹ x)
    simp only [LinearMap.comp_apply, LinearMap.dualMap_apply] at hx
    have h1 : (ρ g) (ρ g⁻¹ x) = x := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [h1] at hx
    exact hx.symm

private theorem w183_l34_phi_fix_dual {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 4) (φ : K ≃+* F4) :
    ∀ q : Module.Dual (ZMod 2) (Additive (FFModel.twistTensor 1 (StatedSL 3 K)).Mod),
      (∀ g : ↥(StatedSL 3 K), (Representation.dual (w183_l34Rep (K := K)
        (FFModel.twistTensor_isActionModel 1 (StatedSL 3 K) (by rw [hK]; norm_num))) g) q = q) →
      q = 0 := by
  intro q hq
  have hD : (FFModel.twistTensor 1 (StatedSL 3 K)).IsActionModel :=
    FFModel.twistTensor_isActionModel 1 (StatedSL 3 K) (by rw [hK]; norm_num)
  obtain ⟨ω, P, B, hω, hP, hB, hP3, hB3, hgen⟩ := s16nt_l34_gen hK
  have hP4 : ((mapGLF φ P : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) =
      w183_l34Aux2_P4 := by
    rw [coe_mapGLF, hP]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [w183_l34Aux2_P4]
  have hφω : (φ ω) ^ 2 + φ ω + 1 = 0 := by
    have h := congrArg φ hω
    simpa using h
  have hintP : ∀ x, w183_l34_linEquiv (K := K) φ (w183_l34Rep (K := K) hD P x) =
      (w183_l34Aux2_colMat (cols w183_l34Aux2_P4)).mulVecLin
        (w183_l34_linEquiv (K := K) φ x) := by
    intro x
    rw [w183_l34_linEquiv_intertwine (K := K) hD hK φ P x, hP4]
  have hqP : (w183_l34Rep (K := K) hD P).dualMap q = q :=
    (w183_l34_dual_fix_iff (w183_l34Rep (K := K) hD) P q).mp (hq P)
  have hqB : (w183_l34Rep (K := K) hD B).dualMap q = q :=
    (w183_l34_dual_fix_iff (w183_l34Rep (K := K) hD) B q).mp (hq B)
  rcases w183_l34_F4_root_cases (φ ω) hφω with hωφ | hωφ
  · have hB4 : ((mapGLF φ B : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) =
        w183_l34Aux2_B4 := by
      rw [coe_mapGLF, hB]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [w183_l34Aux2_B4, hωφ]
    have hintB : ∀ x, w183_l34_linEquiv (K := K) φ (w183_l34Rep (K := K) hD B x) =
        (w183_l34Aux2_colMat (cols w183_l34Aux2_B4)).mulVecLin
          (w183_l34_linEquiv (K := K) φ x) := by
      intro x
      rw [w183_l34_linEquiv_intertwine (K := K) hD hK φ B x, hB4]
    have hf := w183_l34_fix_vec_to_dual
      (w183_l34Aux2_colMat (cols w183_l34Aux2_P4))
      (w183_l34Aux2_colMat (cols w183_l34Aux2_B4))
      (w183_l34Aux2_fix_dual)
    exact w183_l34Aux2_fix_dual_two (L := w183_l34_linEquiv (K := K) φ) hintP hintB hf
      q hqP hqB
  · have hB4 : ((mapGLF φ B : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) =
        w183_l34Aux2_B4' := by
      rw [coe_mapGLF, hB]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [w183_l34Aux2_B4', hωφ]
    have hintB : ∀ x, w183_l34_linEquiv (K := K) φ (w183_l34Rep (K := K) hD B x) =
        (w183_l34Aux2_colMat (cols w183_l34Aux2_B4')).mulVecLin
          (w183_l34_linEquiv (K := K) φ x) := by
      intro x
      rw [w183_l34_linEquiv_intertwine (K := K) hD hK φ B x, hB4]
    have hf := w183_l34_fix_vec_to_dual
      (w183_l34Aux2_colMat (cols w183_l34Aux2_P4))
      (w183_l34Aux2_colMat (cols w183_l34Aux2_B4'))
      (w183_l34Aux2_fix_dual_B4')
    exact w183_l34Aux2_fix_dual_two (L := w183_l34_linEquiv (K := K) φ) hintP hintB hf
      q hqP hqB

theorem s16nt_card_l34Mod {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4) :
    Nat.card (FFModel.twistTensor 1 (StatedSL 3 K)).Mod = 2 ^ 9 := by
  have hmod : Nat.card (FFModel.twistTensor 1 (StatedSL 3 K)).Mod =
      Nat.card ↥(hermSub 1 (Fin 3) K) := by
    show Nat.card (↥(hermSub 1 (Fin 3) K) ⧸
      (⊥ : Subgroup (Multiplicative (Matrix (Fin 3) (Fin 3) K))).subgroupOf
        (hermSub 1 (Fin 3) K)) = _
    rw [Subgroup.bot_subgroupOf]
    exact Nat.card_congr (QuotientGroup.quotientBot).toEquiv
  rw [hmod]
  have hsub : Nat.card ↥(hermSub 1 (Fin 3) K) =
      Nat.card ↥(CFSG.Quasithin.B45Sp4.hermA 1 (Fin 3) K) :=
    Nat.card_congr
      { toFun := fun x => ⟨Multiplicative.toAdd
            (x : Multiplicative (Matrix (Fin 3) (Fin 3) K)),
          (CFSG.Quasithin.B45Sp4.ofAdd_mem_hermSub.mp x.2)⟩
        invFun := fun y => ⟨Multiplicative.ofAdd (y : Matrix (Fin 3) (Fin 3) K),
          (CFSG.Quasithin.B45Sp4.ofAdd_mem_hermSub.mpr y.2)⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  rw [hsub]
  have hF : Nat.card K = 2 ^ (2 * 1) := by rw [hK]; norm_num
  have hsq := CFSG.Quasithin.B45Sp4.card_hermA_sq (ι := Fin 3) (a := 1) le_rfl hF
  rw [Fintype.card_fin] at hsq
  have hsq' : Nat.card ↥(CFSG.Quasithin.B45Sp4.hermA 1 (Fin 3) K) ^ 2 = (2 ^ 9) ^ 2 := by
    rw [hsq, hK]
    norm_num
  exact Nat.pow_left_injective two_ne_zero hsq'

theorem w183_l34_fix_dual_transport {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 4) :
    ∀ q : Module.Dual (ZMod 2) (Additive (FFModel.twistTensor 1 (StatedSL 3 K)).Mod),
      (∀ g : ↥(StatedSL 3 K), (Representation.dual (w183_l34Rep (K := K)
        (FFModel.twistTensor_isActionModel 1 (StatedSL 3 K) (by rw [hK]; norm_num))) g) q = q) →
      q = 0 := by
  haveI : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = Fintype.card F4 := by
    rw [← Nat.card_eq_fintype_card, hK, F4.card]
  let φ : K ≃+* F4 := FiniteField.ringEquivOfCardEq hc
  exact w183_l34_phi_fix_dual hK φ

private theorem w183_l34_h1_step {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 4) (hD : (FFModel.twistTensor 1 (StatedSL 3 K)).IsActionModel)
    (P B : ↥(StatedSL 3 K)) (hP3 : P ^ 3 = 1) (hB3 : B ^ 3 = 1)
    (hgen : Subgroup.closure {P, B} = ⊤)
    (hrankP : Module.finrank (ZMod 2) (LinearMap.range (∑ i ∈ Finset.range 3,
      (w183_l34Rep (K := K) hD P) ^ i)) = 3)
    (hrankB : Module.finrank (ZMod 2) (LinearMap.range (∑ i ∈ Finset.range 3,
      (w183_l34Rep (K := K) hD B) ^ i)) = 3) :
    Module.finrank (ZMod 2) (H1 (Representation.dual (w183_l34Rep (K := K) hD))) ≤ 3 := by
  haveI hamb : Finite (FFModel.twistTensor 1 (StatedSL 3 K)).Amb :=
    inferInstanceAs (Finite (Multiplicative (Matrix (Fin 3) (Fin 3) K)))
  haveI hsec : Finite (↥(FFModel.twistTensor 1 (StatedSL 3 K)).sec) := Subtype.finite
  haveI hmod : Finite (FFModel.twistTensor 1 (StatedSL 3 K)).Mod := inferInstance
  haveI hQfin : Finite (Additive (FFModel.twistTensor 1 (StatedSL 3 K)).Mod) := inferInstance
  haveI : Fintype (Additive (FFModel.twistTensor 1 (StatedSL 3 K)).Mod) := Fintype.ofFinite _
  haveI hfun : Finite (Additive (FFModel.twistTensor 1 (StatedSL 3 K)).Mod → ZMod 2) :=
    inferInstance
  haveI : Finite (Module.Dual (ZMod 2)
      (Additive (FFModel.twistTensor 1 (StatedSL 3 K)).Mod)) :=
    Finite.of_injective
      (fun f : Module.Dual (ZMod 2) (Additive (FFModel.twistTensor 1 (StatedSL 3 K)).Mod) =>
        (f : Additive (FFModel.twistTensor 1 (StatedSL 3 K)).Mod → ZMod 2))
      DFunLike.coe_injective
  have hfix := w183_l34_fix_dual_transport (K := K) hK
  have hP' : Module.finrank (ZMod 2) (LinearMap.range (∑ i ∈ Finset.range 3,
      (Representation.dual (w183_l34Rep (K := K) hD) P) ^ i)) = 3 := by
    rw [s16nt_rank_norm_dual (a := P) (r := 3) (w183_l34Rep (K := K) hD) hP3]
    exact hrankP
  have hB' : Module.finrank (ZMod 2) (LinearMap.range (∑ i ∈ Finset.range 3,
      (Representation.dual (w183_l34Rep (K := K) hD) B) ^ i)) = 3 := by
    rw [s16nt_rank_norm_dual (a := B) (r := 3) (w183_l34Rep (K := K) hD) hB3]
    exact hrankB
  have h := s16nt_h1_le_of_two_gen (Representation.dual (w183_l34Rep (K := K) hD))
    hgen (r := 3) (s := 3) hP3 hB3 hfix
  rw [hP', hB'] at h
  have hQ : Module.finrank (ZMod 2)
      (Additive (FFModel.twistTensor 1 (StatedSL 3 K)).Mod) = 9 := by
    haveI : Module.Finite (ZMod 2)
        (Additive (FFModel.twistTensor 1 (StatedSL 3 K)).Mod) := Module.Finite.of_finite
    have hcard : Nat.card (Additive (FFModel.twistTensor 1 (StatedSL 3 K)).Mod) = 2 ^ 9 :=
      s16nt_card_l34Mod (K := K) hK
    have hpow := Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := Additive (FFModel.twistTensor 1 (StatedSL 3 K)).Mod)
    rw [Nat.card_zmod, hcard] at hpow
    exact (Nat.pow_right_injective le_rfl hpow).symm
  rw [Subspace.dual_finrank_eq, hQ] at h
  omega

private theorem w183_l34_rank_P {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 4) (φ : K ≃+* F4)
    (hD : (FFModel.twistTensor 1 (StatedSL 3 K)).IsActionModel)
    (P : ↥(StatedSL 3 K))
    (hP : ((P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![0, 1, 0; 0, 0, 1; 1, 0, 0]) :
    Module.finrank (ZMod 2) (LinearMap.range (∑ i ∈ Finset.range 3,
      (w183_l34Rep (K := K) hD P) ^ i)) = 3 := by
  have hP4 : ((mapGLF φ P : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) =
      w183_l34Aux2_P4 := by
    rw [coe_mapGLF, hP]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [w183_l34Aux2_P4]
  have hint : ∀ x, w183_l34_linEquiv (K := K) φ (w183_l34Rep (K := K) hD P x) =
      (w183_l34Aux2_colMat (cols w183_l34Aux2_P4)).mulVecLin
        (w183_l34_linEquiv (K := K) φ x) := by
    intro x
    rw [w183_l34_linEquiv_intertwine (K := K) hD hK φ P x, hP4]
  rw [w183_l34Aux2_finrank_range_norm_congr (L := w183_l34_linEquiv (K := K) φ) hint 3,
    w183_l34_finrank_norm_three, w183_l34Aux2_rank_P4]

private theorem w183_l34_rank_B {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 4) (φ : K ≃+* F4)
    (hD : (FFModel.twistTensor 1 (StatedSL 3 K)).IsActionModel)
    (ω : K) (hω : ω ^ 2 + ω + 1 = 0) (B : ↥(StatedSL 3 K))
    (hB : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![1, 1, ω; 0, 1, 1; 0, 1, 0]) :
    Module.finrank (ZMod 2) (LinearMap.range (∑ i ∈ Finset.range 3,
      (w183_l34Rep (K := K) hD B) ^ i)) = 3 := by
  have hφω : (φ ω) ^ 2 + φ ω + 1 = 0 := by
    have h := congrArg φ hω
    simpa using h
  rcases w183_l34_F4_root_cases (φ ω) hφω with hωφ | hωφ
  · have hB4 : ((mapGLF φ B : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) =
        w183_l34Aux2_B4 := by
      rw [coe_mapGLF, hB]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [w183_l34Aux2_B4, hωφ]
    have hint : ∀ x, w183_l34_linEquiv (K := K) φ (w183_l34Rep (K := K) hD B x) =
        (w183_l34Aux2_colMat (cols w183_l34Aux2_B4)).mulVecLin
          (w183_l34_linEquiv (K := K) φ x) := by
      intro x
      rw [w183_l34_linEquiv_intertwine (K := K) hD hK φ B x, hB4]
    rw [w183_l34Aux2_finrank_range_norm_congr (L := w183_l34_linEquiv (K := K) φ) hint 3,
      w183_l34_finrank_norm_three, w183_l34Aux2_rank_B4]
  · have hB4 : ((mapGLF φ B : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) =
        w183_l34Aux2_B4' := by
      rw [coe_mapGLF, hB]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [w183_l34Aux2_B4', hωφ]
    have hint : ∀ x, w183_l34_linEquiv (K := K) φ (w183_l34Rep (K := K) hD B x) =
        (w183_l34Aux2_colMat (cols w183_l34Aux2_B4')).mulVecLin
          (w183_l34_linEquiv (K := K) φ x) := by
      intro x
      rw [w183_l34_linEquiv_intertwine (K := K) hD hK φ B x, hB4]
    rw [w183_l34Aux2_finrank_range_norm_congr (L := w183_l34_linEquiv (K := K) φ) hint 3,
      w183_l34_finrank_norm_three, w183_l34Aux2_rank_B4']

private theorem w183_l34_phi_h1_bound {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 4) (φ : K ≃+* F4) :
    Module.finrank (ZMod 2)
      (H1 (Representation.dual (w183_l34Rep (K := K)
        (FFModel.twistTensor_isActionModel 1 (StatedSL 3 K) (by rw [hK]; norm_num))))) ≤ 3 := by
  have hD : (FFModel.twistTensor 1 (StatedSL 3 K)).IsActionModel :=
    FFModel.twistTensor_isActionModel 1 (StatedSL 3 K) (by rw [hK]; norm_num)
  obtain ⟨ω, P, B, hω, hP, hB, hP3, hB3, hgen⟩ := s16nt_l34_gen hK
  exact w183_l34_h1_step hK hD P B hP3 hB3 hgen
    (w183_l34_rank_P hK φ hD P hP) (w183_l34_rank_B hK φ hD ω hω B hB)

theorem w183_l34_h1_bound {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 4) :
    Module.finrank (ZMod 2)
      (H1 (Representation.dual (w183_l34Rep (K := K)
        (FFModel.twistTensor_isActionModel 1 (StatedSL 3 K) (by rw [hK]; norm_num))))) ≤ 3 := by
  haveI : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = Fintype.card F4 := by
    rw [← Nat.card_eq_fintype_card, hK, F4.card]
  let φ : K ≃+* F4 := FiniteField.ringEquivOfCardEq hc
  exact w183_l34_phi_h1_bound hK φ

private theorem w183_l34Rep_equivariant {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 4) :
    ∀ (γ : ↥(StatedSL 3 K))
      (q : (FFModel.twistTensor 1 (StatedSL 3 K)).Mod),
      w183_l34ModEquiv (K := K)
          ((FFModel.twistTensor_isActionModel 1 (StatedSL 3 K) (by rw [hK]; norm_num)).modAct
            γ q) =
        Multiplicative.ofAdd
          (w183_l34Rep (K := K)
              (FFModel.twistTensor_isActionModel 1 (StatedSL 3 K) (by rw [hK]; norm_num))
              γ (Multiplicative.toAdd (w183_l34ModEquiv (K := K) q))) := by
  intro γ q
  rfl

theorem s16nt_cover_l34 {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4) :
    S16BoundCover (FFModel.twistTensor 1 (StatedSL 3 K)) 3 := by
  have hD := FFModel.twistTensor_isActionModel 1 (StatedSL 3 K) (by rw [hK]; norm_num)
  haveI hgam : Finite (FFModel.twistTensor 1 (StatedSL 3 K)).Gam :=
    inferInstanceAs (Finite ↥(StatedSL 3 K))
  haveI hamb : Finite (FFModel.twistTensor 1 (StatedSL 3 K)).Amb :=
    inferInstanceAs (Finite (Multiplicative (Matrix (Fin 3) (Fin 3) K)))
  haveI hsec : Finite (↥(FFModel.twistTensor 1 (StatedSL 3 K)).sec) := Subtype.finite
  haveI hmod : Finite (FFModel.twistTensor 1 (StatedSL 3 K)).Mod := inferInstance
  haveI hQ : Finite (Additive (FFModel.twistTensor 1 (StatedSL 3 K)).Mod) := inferInstance
  exact s16nt_cover_of_h1_model hD (w183_l34ModEquiv (K := K))
    (w183_l34Rep (K := K) hD) (w183_l34Rep_equivariant hK) (w183_l34_h1_bound hK)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
