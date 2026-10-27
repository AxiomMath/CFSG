module

public import CFSG.Open.StatedDefs
public import CFSG.Quasithin.Background.Module
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin
open scoped MatrixGroups Matrix

abbrev OmI : Type := Fin 2 ⊕ Fin 2

structure OmegaModel (W : Type) [CommGroup W] where
  K : Type
  [field : Field K]
  [fin : Finite K]
  [charTwo : CharP K 2]
  four_le : 4 ≤ Nat.card K
  e : W ≃* Multiplicative (OmI → K)

attribute [instance] OmegaModel.field OmegaModel.fin OmegaModel.charTwo

namespace OmegaModel

variable {W : Type} [CommGroup W] (S : OmegaModel W)

@[expose] def vec (w : W) : OmI → S.K := Multiplicative.toAdd (S.e w)

@[expose] def ofVec (v : OmI → S.K) : W := S.e.symm (Multiplicative.ofAdd v)

@[expose] def smul (c : S.K) (w : W) : W := S.ofVec (c • S.vec w)

@[expose] def Q (w : W) : S.K := StatedQuadPlus 2 S.K (S.vec w)

@[expose] def pol (w w' : W) : S.K := S.Q (w * w') - S.Q w - S.Q w'

theorem vec_ofVec (v : OmI → S.K) : S.vec (S.ofVec v) = v := by
  simp [vec, ofVec]

theorem ofVec_vec (w : W) : S.ofVec (S.vec w) = w := by
  simp [vec, ofVec]

theorem vec_injective : Function.Injective S.vec := fun a b h => by
  rw [← S.ofVec_vec a, ← S.ofVec_vec b, h]

theorem vec_mul (w w' : W) : S.vec (w * w') = S.vec w + S.vec w' := by
  simp [vec]

theorem vec_one : S.vec 1 = 0 := by
  simp [vec]

theorem vec_inv (w : W) : S.vec w⁻¹ = - S.vec w := by
  simp [vec]

theorem vec_smul (c : S.K) (w : W) : S.vec (S.smul c w) = c • S.vec w := by
  simp [smul, vec_ofVec]

theorem smul_one_eq (w : W) : S.smul 1 w = w := by
  simp [smul, ofVec_vec]

theorem smul_smul_eq (c c' : S.K) (w : W) : S.smul c (S.smul c' w) = S.smul (c * c') w := by
  simp [smul, vec_ofVec, smul_smul]

theorem smul_mul_eq (c : S.K) (w w' : W) : S.smul c (w * w') = S.smul c w * S.smul c w' := by
  apply S.vec_injective
  simp [vec_smul, vec_mul, smul_add]

theorem smul_add_eq (c c' : S.K) (w : W) : S.smul (c + c') w = S.smul c w * S.smul c' w := by
  apply S.vec_injective
  simp [vec_smul, vec_mul, add_smul]

theorem smul_zero_eq (w : W) : S.smul 0 w = 1 := by
  apply S.vec_injective
  simp [vec_smul, vec_one]

theorem smul_one_elem (c : S.K) : S.smul c 1 = 1 := by
  apply S.vec_injective
  simp [vec_smul, vec_one]

theorem card_eq : Nat.card W = Nat.card S.K ^ 4 := by
  rw [Nat.card_congr S.e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun]
  simp [Nat.card_eq_fintype_card]

theorem Q_smul (c : S.K) (w : W) : S.Q (S.smul c w) = c ^ 2 * S.Q w := by
  simp only [Q, StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, vec_smul, Fin.sum_univ_two]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem Q_mul (w w' : W) : S.Q (w * w') = S.Q w + S.Q w' + S.pol w w' := by
  unfold pol
  ring

theorem pol_comm (w w' : W) : S.pol w w' = S.pol w' w := by
  unfold pol
  rw [mul_comm w w']
  ring

theorem pol_mul_left (w w' w'' : W) : S.pol (w * w') w'' = S.pol w w'' + S.pol w' w'' := by
  simp only [pol, Q, StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, vec_mul, Fin.sum_univ_two,
    Pi.add_apply]
  ring

theorem pol_smul_left (c : S.K) (w w' : W) : S.pol (S.smul c w) w' = c * S.pol w w' := by
  simp only [pol, Q, StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, vec_mul, vec_smul,
    Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem pol_self (w : W) : S.pol w w = 0 := by
  simp only [pol, Q, StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, vec_mul, Fin.sum_univ_two,
    Pi.add_apply]
  have h2 : (2 : S.K) = 0 := CharP.cast_eq_zero S.K 2
  linear_combination (S.vec w (Sum.inl 0) * S.vec w (Sum.inr 0) +
    S.vec w (Sum.inl 1) * S.vec w (Sum.inr 1)) * h2

theorem pol_mul_right (w w' w'' : W) : S.pol w (w' * w'') = S.pol w w' + S.pol w w'' := by
  rw [S.pol_comm w (w' * w''), S.pol_mul_left, S.pol_comm w' w, S.pol_comm w'' w]

theorem pol_smul_right (c : S.K) (w w' : W) : S.pol w (S.smul c w') = c * S.pol w w' := by
  rw [S.pol_comm w (S.smul c w'), S.pol_smul_left, S.pol_comm w' w]

theorem Q_one : S.Q 1 = 0 := by
  simp [Q, StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, vec_one]

theorem pol_eq (w w' : W) : S.pol w w' = S.vec w (Sum.inl 0) * S.vec w' (Sum.inr 0) +
    S.vec w' (Sum.inl 0) * S.vec w (Sum.inr 0) + S.vec w (Sum.inl 1) * S.vec w' (Sum.inr 1) +
    S.vec w' (Sum.inl 1) * S.vec w (Sum.inr 1) := by
  simp only [pol, Q, StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, vec_mul, Fin.sum_univ_two,
    Pi.add_apply]
  ring

theorem eq_one_of_pol_eq_zero {w : W} (h : ∀ w' : W, S.pol w w' = 0) : w = 1 := by
  apply S.vec_injective
  rw [vec_one]
  have h1 := h (S.ofVec (Pi.single (Sum.inr 0) 1))
  have h2 := h (S.ofVec (Pi.single (Sum.inl 0) 1))
  have h3 := h (S.ofVec (Pi.single (Sum.inr 1) 1))
  have h4 := h (S.ofVec (Pi.single (Sum.inl 1) 1))
  simp [pol_eq, vec_ofVec] at h1 h2 h3 h4
  funext i
  rcases i with i | i <;> fin_cases i <;> simp [*]

theorem exists_Q_ne_zero : ∃ w : W, S.Q w ≠ 0 := by
  refine ⟨S.ofVec (fun i => if i = Sum.inl 0 ∨ i = Sum.inr 0 then 1 else 0), ?_⟩
  simp [Q, StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, vec_ofVec, Fin.sum_univ_two]

@[expose] def natAut {K : Type} [Field K] (γ : GL OmI K) : MulAut (Multiplicative (OmI → K)) where
  toFun x := Multiplicative.ofAdd ((γ : Matrix OmI OmI K) *ᵥ Multiplicative.toAdd x)
  invFun x := Multiplicative.ofAdd (((γ⁻¹ : GL OmI K) : Matrix OmI OmI K) *ᵥ
    Multiplicative.toAdd x)
  left_inv x := by
    simp only [toAdd_ofAdd, Matrix.mulVec_mulVec]
    rw [← Units.val_mul, inv_mul_cancel]
    simp
  right_inv x := by
    simp only [toAdd_ofAdd, Matrix.mulVec_mulVec]
    rw [← Units.val_mul, mul_inv_cancel]
    simp
  map_mul' x y := by
    simp [Matrix.mulVec_add]

@[expose] def natActHom (K : Type) [Field K] :
    GL OmI K →* MulAut (Multiplicative (OmI → K)) where
  toFun := natAut
  map_one' := by
    ext x
    simp [natAut]
  map_mul' γ δ := by
    ext x
    simp [natAut, Matrix.mulVec_mulVec]

@[expose] def actHom : GL OmI S.K →* MulAut W :=
  (MulAut.congr S.e.symm).toMonoidHom.comp (natActHom S.K)

@[expose] def omega : Subgroup (MulAut W) :=
  (StatedOmega (StatedQuadPlus 2 S.K)).map S.actHom

theorem actHom_vec (γ : GL OmI S.K) (w : W) :
    S.vec (S.actHom γ w) = (γ : Matrix OmI OmI S.K) *ᵥ S.vec w := by
  simp [actHom, vec, natActHom, natAut, MulAut.congr]

theorem omega_Q {h : MulAut W} (hh : h ∈ S.omega) (w : W) : S.Q (h w) = S.Q w := by
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hh
  have hiso : γ ∈ CFSG.MatrixModel.isometryCore (StatedQuadPlus 2 S.K) := by
    have : StatedOmega (StatedQuadPlus 2 S.K) ≤
        CFSG.MatrixModel.isometryCore (StatedQuadPlus 2 S.K) := by
      unfold StatedOmega
      refine Subgroup.commutator_le.mpr (fun a ha b hb => ?_)
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    exact this hγ
  have hpres : ∀ A ∈ CFSG.MatrixModel.isometryCore (StatedQuadPlus 2 S.K),
      ∀ v, StatedQuadPlus 2 S.K ((A : Matrix OmI OmI S.K) *ᵥ v) = StatedQuadPlus 2 S.K v := by
    intro A hA
    unfold CFSG.MatrixModel.isometryCore at hA
    refine Subgroup.closure_induction (p := fun (A : GL OmI S.K) _ => ∀ v, StatedQuadPlus 2 S.K
      ((A : Matrix OmI OmI S.K) *ᵥ v) = StatedQuadPlus 2 S.K v) (fun A hA => hA) ?_ ?_ ?_ hA
    · intro v; simp
    · intro A B _ _ hA hB v
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, hA, hB]
    · intro A _ hA v
      have := hA (((A⁻¹ : GL OmI S.K) : Matrix OmI OmI S.K) *ᵥ v)
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec] at this
      exact this.symm
  simp only [Q, actHom_vec, hpres γ hiso]

theorem omega_smul {h : MulAut W} (hh : h ∈ S.omega) (c : S.K) (w : W) :
    h (S.smul c w) = S.smul c (h w) := by
  obtain ⟨γ, -, rfl⟩ := Subgroup.mem_map.mp hh
  apply S.vec_injective
  simp [actHom_vec, vec_smul, Matrix.mulVec_smul]

@[expose] def toMat {K : Type} (v : OmI → K) : Matrix (Fin 2) (Fin 2) K :=
  !![v (Sum.inl 0), v (Sum.inl 1); v (Sum.inr 1), v (Sum.inr 0)]

@[expose] def ofMat {K : Type} (X : Matrix (Fin 2) (Fin 2) K) : OmI → K
  | Sum.inl i => X 0 i
  | Sum.inr i => X 1 (Fin.rev i)

theorem ofMat_toMat {K : Type} (v : OmI → K) : ofMat (toMat v) = v := by
  funext i
  rcases i with i | i <;> fin_cases i <;> simp [ofMat, toMat]

theorem toMat_ofMat {K : Type} (X : Matrix (Fin 2) (Fin 2) K) : toMat (ofMat X) = X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ofMat, toMat]

theorem toMat_add {K : Type} [Add K] (v v' : OmI → K) : toMat (v + v') = toMat v + toMat v' := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMat]

theorem toMat_smul {K : Type} [Mul K] (c : K) (v : OmI → K) : toMat (c • v) = c • toMat v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMat]

theorem ofMat_smul {K : Type} [Mul K] (c : K) (X : Matrix (Fin 2) (Fin 2) K) :
    ofMat (c • X) = c • ofMat X := by
  funext i
  rcases i with i | i <;> fin_cases i <;> simp [ofMat]

theorem Q_eq_det (w : W) : S.Q w = (toMat (S.vec w)).det := by
  simp only [Q, StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, Fin.sum_univ_two, toMat,
    Matrix.det_fin_two_of]
  rw [sub_eq_add_neg, CharTwo.neg_eq]

@[expose] def matAut {K : Type} [Field K] (b a : SL(2, K)) :
    MulAut (Multiplicative (Matrix (Fin 2) (Fin 2) K)) where
  toFun X := Multiplicative.ofAdd ((b : Matrix (Fin 2) (Fin 2) K) * Multiplicative.toAdd X *
    (a : Matrix (Fin 2) (Fin 2) K)ᵀ)
  invFun X := Multiplicative.ofAdd (((b⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *
    Multiplicative.toAdd X * ((a⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)ᵀ)
  left_inv X := by
    have hb : ((b⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *
        (b : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]
      rfl
    have ha : (a : Matrix (Fin 2) (Fin 2) K)ᵀ * ((a⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)ᵀ =
        1 := by
      rw [← Matrix.transpose_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]
      simp
    simp only [toAdd_ofAdd]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hb, Matrix.one_mul, Matrix.mul_assoc, ha,
      Matrix.mul_one]
    rfl
  right_inv X := by
    have hb : (b : Matrix (Fin 2) (Fin 2) K) *
        ((b⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]
      rfl
    have ha : ((a⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)ᵀ * (a : Matrix (Fin 2) (Fin 2) K)ᵀ =
        1 := by
      rw [← Matrix.transpose_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]
      simp
    simp only [toAdd_ofAdd]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hb, Matrix.one_mul, Matrix.mul_assoc, ha,
      Matrix.mul_one]
    rfl
  map_mul' X Y := by
    simp [Matrix.mul_add, Matrix.add_mul]

@[expose] def matAutHom (K : Type) [Field K] :
    SL(2, K) × SL(2, K) →* MulAut (Multiplicative (Matrix (Fin 2) (Fin 2) K)) where
  toFun p := matAut p.1 p.2
  map_one' := by
    ext X
    simp [matAut]
  map_mul' p q := by
    ext X
    simp [matAut, Matrix.mul_assoc, Matrix.transpose_mul]

@[expose] def matEquiv : W ≃* Multiplicative (Matrix (Fin 2) (Fin 2) S.K) where
  toFun w := Multiplicative.ofAdd (toMat (S.vec w))
  invFun X := S.ofVec (ofMat (Multiplicative.toAdd X))
  left_inv w := by
    show S.ofVec (ofMat (toMat (S.vec w))) = w
    rw [ofMat_toMat, ofVec_vec]
  right_inv X := by
    simp [vec_ofVec, toMat_ofMat]
  map_mul' w w' := by
    simp [vec_mul, toMat_add]

@[expose] def jHom : SL(2, S.K) × SL(2, S.K) →* MulAut W :=
  (MulAut.congr S.matEquiv.symm).toMonoidHom.comp (matAutHom S.K)

@[expose] def omega0 : Subgroup (MulAut W) := (S.jHom).range

theorem vec_jHom (p : SL(2, S.K) × SL(2, S.K)) (w : W) :
    S.vec (S.jHom p w) = ofMat ((p.1 : Matrix (Fin 2) (Fin 2) S.K) * toMat (S.vec w) *
      (p.2 : Matrix (Fin 2) (Fin 2) S.K)ᵀ) := by
  simp [jHom, matEquiv, matAutHom, matAut, MulAut.congr, vec_ofVec]

theorem smul_jHom (p : SL(2, S.K) × SL(2, S.K)) (c : S.K) (w : W) :
    S.jHom p (S.smul c w) = S.smul c (S.jHom p w) := by
  apply S.vec_injective
  rw [vec_jHom, vec_smul, vec_smul, vec_jHom, toMat_smul, Matrix.mul_smul, Matrix.smul_mul,
    ofMat_smul]

theorem Q_jHom (p : SL(2, S.K) × SL(2, S.K)) (w : W) : S.Q (S.jHom p w) = S.Q w := by
  rw [Q_eq_det, Q_eq_det, vec_jHom, toMat_ofMat, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, Matrix.SpecialLinearGroup.det_coe, Matrix.SpecialLinearGroup.det_coe,
    one_mul, mul_one]

theorem jHom_injective : Function.Injective S.jHom := by
  rw [injective_iff_map_eq_one S.jHom]
  intro p hp
  have key : ∀ X : Matrix (Fin 2) (Fin 2) S.K,
      (p.1 : Matrix (Fin 2) (Fin 2) S.K) * X *
        (p.2 : Matrix (Fin 2) (Fin 2) S.K)ᵀ = X := by
    intro X
    have h := congrArg (fun f : MulAut W => f (S.ofVec (ofMat X))) hp
    simp only [MulAut.one_apply] at h
    have hv : S.vec (S.jHom p (S.ofVec (ofMat X))) =
        S.vec (S.ofVec (ofMat X)) := by rw [h]
    rw [S.vec_jHom, S.vec_ofVec, toMat_ofMat] at hv
    simpa [toMat_ofMat] using congrArg toMat hv
  have hba : (p.1 : Matrix (Fin 2) (Fin 2) S.K) *
      (p.2 : Matrix (Fin 2) (Fin 2) S.K)ᵀ = 1 := by
    simpa using key 1
  have hab : (p.2 : Matrix (Fin 2) (Fin 2) S.K)ᵀ *
      (p.1 : Matrix (Fin 2) (Fin 2) S.K) = 1 := mul_eq_one_comm.mp hba
  have hcomm : ∀ X : Matrix (Fin 2) (Fin 2) S.K,
      (p.1 : Matrix (Fin 2) (Fin 2) S.K) * X =
        X * (p.1 : Matrix (Fin 2) (Fin 2) S.K) := by
    intro X
    have hX := key X
    calc (p.1 : Matrix (Fin 2) (Fin 2) S.K) * X
        = (p.1 : Matrix (Fin 2) (Fin 2) S.K) * X * 1 := (mul_one _).symm
      _ = (p.1 : Matrix (Fin 2) (Fin 2) S.K) * X *
            ((p.2 : Matrix (Fin 2) (Fin 2) S.K)ᵀ *
              (p.1 : Matrix (Fin 2) (Fin 2) S.K)) := by rw [hab]
      _ = ((p.1 : Matrix (Fin 2) (Fin 2) S.K) * X *
            (p.2 : Matrix (Fin 2) (Fin 2) S.K)ᵀ) *
              (p.1 : Matrix (Fin 2) (Fin 2) S.K) := (Matrix.mul_assoc _ _ _).symm
      _ = X * (p.1 : Matrix (Fin 2) (Fin 2) S.K) := by rw [hX]
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single
      (M := (p.1 : Matrix (Fin 2) (Fin 2) S.K))
      (fun i j _ => (hcomm (Matrix.single i j 1)).symm)
  have hdet : (p.1 : Matrix (Fin 2) (Fin 2) S.K).det = c ^ 2 := by
    rw [← hc, Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two, pow_two]
  have hc2 : c ^ 2 = 1 := by
    have hd := Matrix.SpecialLinearGroup.det_coe (A := p.1)
    rwa [hdet] at hd
  have hc1 : c = 1 := by
    rcases sq_eq_one_iff.mp hc2 with h | h
    · exact h
    · rw [h, CharTwo.neg_eq]
  have hb : (p.1 : Matrix (Fin 2) (Fin 2) S.K) = 1 := by
    rw [← hc, hc1, Matrix.scalar_apply, Matrix.diagonal_one]
  have ha't : (p.2 : Matrix (Fin 2) (Fin 2) S.K)ᵀ = 1 := by
    rw [hb, Matrix.one_mul] at hba
    exact hba
  have ha : (p.2 : Matrix (Fin 2) (Fin 2) S.K) = 1 := Matrix.transpose_eq_one.mp ha't
  exact Prod.ext (Subtype.ext hb) (Subtype.ext ha)

theorem actHom_injective : Function.Injective S.actHom := by
  intro γ δ h
  have hv : ∀ v : OmI → S.K,
      (γ : Matrix OmI OmI S.K) *ᵥ v = (δ : Matrix OmI OmI S.K) *ᵥ v := by
    intro v
    have h1 := congrArg (fun f : MulAut W => f (S.ofVec v)) h
    have h2 := congrArg S.vec h1
    simp only [S.actHom_vec, S.vec_ofVec] at h2
    exact h2
  exact Units.ext (Matrix.ext_of_mulVec_single fun j => hv (Pi.single j 1))

theorem exists_actHom_of_smul_comm {h : MulAut W}
    (hh : ∀ (c : S.K) (w : W), h (S.smul c w) = S.smul c (h w)) :
    ∃ γ : GL OmI S.K, S.actHom γ = h := by
  have hof_add : ∀ v v' : OmI → S.K, S.ofVec (v + v') = S.ofVec v * S.ofVec v' := by
    intro v v'
    simp [ofVec, ofAdd_add]
  have hof_smul : ∀ (c : S.K) (v : OmI → S.K), S.ofVec (c • v) = S.smul c (S.ofVec v) := by
    intro c v
    simp [smul, vec_ofVec]
  let L : (OmI → S.K) →ₗ[S.K] (OmI → S.K) :=
    { toFun := fun v => S.vec (h (S.ofVec v))
      map_add' := by
        intro v v'
        rw [hof_add, map_mul, S.vec_mul]
      map_smul' := by
        intro c v
        rw [hof_smul, hh, S.vec_smul]
        rfl }
  have hL : Function.Bijective L := by
    have h1 : Function.Bijective S.vec :=
      ⟨S.vec_injective, fun v => ⟨S.ofVec v, S.vec_ofVec v⟩⟩
    have h2 : Function.Bijective (h : W → W) := h.bijective
    have h3 : Function.Bijective S.ofVec :=
      ⟨fun a b hab => by
        have h' := congrArg S.vec hab
        simpa [S.vec_ofVec] using h',
       fun v => ⟨S.vec v, S.ofVec_vec v⟩⟩
    exact h1.comp (h2.comp h3)
  let e : (OmI → S.K) ≃ₗ[S.K] (OmI → S.K) := LinearEquiv.ofBijective L hL
  let γ : GL OmI S.K := (Matrix.GeneralLinearGroup.toLin).symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv e)
  refine ⟨γ, MulEquiv.ext fun w => S.vec_injective ?_⟩
  rw [S.actHom_vec]
  have htoLin : Matrix.GeneralLinearGroup.toLin γ =
      LinearMap.GeneralLinearGroup.ofLinearEquiv e :=
    MulEquiv.apply_symm_apply (Matrix.GeneralLinearGroup.toLin) _
  have hmat : (γ : Matrix OmI OmI S.K) *ᵥ S.vec w = L (S.vec w) := by
    have h1 : (Matrix.GeneralLinearGroup.toLin γ : (OmI → S.K) →ₗ[S.K] (OmI → S.K))
        (S.vec w) = (γ : Matrix OmI OmI S.K) *ᵥ S.vec w :=
      Matrix.GeneralLinearGroup.toLin_apply γ (S.vec w)
    rw [← h1, htoLin]
    simp [e]
  rw [hmat]
  change S.vec (h (S.ofVec (S.vec w))) = S.vec (h w)
  rw [S.ofVec_vec]

private theorem exists_ne_zero_sq_ne_one (K : Type*) [Field K] [Finite K] [CharP K 2]
    (h : 4 ≤ Nat.card K) : ∃ a : K, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
  classical
  letI := Fintype.ofFinite K
  have hcard : 4 ≤ Fintype.card K := by simpa [Nat.card_eq_fintype_card] using h
  have h2 : ({0, 1} : Finset K).card = 2 := Finset.card_pair_eq_two_iff.mpr zero_ne_one
  have hlt : ({0, 1} : Finset K).card < (Finset.univ : Finset K).card := by
    rw [h2, Finset.card_univ]
    omega
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
  refine ⟨a, ha.1, fun hsq => ?_⟩
  rcases sq_eq_one_iff.mp hsq with h1 | h1
  · exact ha.2 h1
  · have : a = 1 := by rw [h1, CharTwo.neg_eq]
    exact ha.2 this

private theorem isPerfect_prod {G H : Type*} [Group G] [Group H]
    [Group.IsPerfect G] [Group.IsPerfect H] : Group.IsPerfect (G × H) where
  commutator_eq_top := by
    have hG : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = (⊤ : Subgroup G) :=
      Group.IsPerfect.commutator_eq_top (G := G)
    have hH : ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ = (⊤ : Subgroup H) :=
      Group.IsPerfect.commutator_eq_top (G := H)
    show ⁅(⊤ : Subgroup (G × H)), (⊤ : Subgroup (G × H))⁆ = ⊤
    rw [← Subgroup.top_prod_top (G := G) (N := H), Subgroup.commutator_prod_prod, hG, hH,
      Subgroup.top_prod_top]

theorem omega0_le_omega : S.omega0 ≤ S.omega := by
  obtain ⟨a, ha0, hasq⟩ := exists_ne_zero_sq_ne_one S.K S.four_le
  haveI hSL : Group.IsPerfect (SL(2, S.K)) :=
    Group.isPerfect_def.mpr (Matrix.SL2.commutator_eq_top ha0 hasq)
  haveI hprod : Group.IsPerfect (SL(2, S.K) × SL(2, S.K)) := isPerfect_prod
  haveI homega0 : Group.IsPerfect S.omega0 := Group.IsPerfect.range (f := S.jHom)
  have hle : S.omega0 ≤
      (CFSG.MatrixModel.isometryCore (StatedQuadPlus 2 S.K)).map S.actHom := by
    intro h hh
    have hh' : h ∈ S.jHom.range := hh
    rw [MonoidHom.mem_range] at hh'
    obtain ⟨p, hp⟩ := hh'
    rw [← hp]
    obtain ⟨γ, hγ⟩ := S.exists_actHom_of_smul_comm (h := S.jHom p) (S.smul_jHom p)
    refine Subgroup.mem_map.mpr ⟨γ, ?_, hγ⟩
    unfold CFSG.MatrixModel.isometryCore
    refine Subgroup.subset_closure ?_
    intro v
    have h1 : StatedQuadPlus 2 S.K ((γ : Matrix OmI OmI S.K) *ᵥ v) =
        S.Q (S.actHom γ (S.ofVec v)) := by
      simp only [Q, S.actHom_vec, S.vec_ofVec]
    rw [h1, hγ, S.Q_jHom, Q, S.vec_ofVec]
  calc S.omega0 = ⁅S.omega0, S.omega0⁆ :=
        (Subgroup.commutator_eq_self (H := S.omega0)).symm
    _ ≤ ⁅(CFSG.MatrixModel.isometryCore (StatedQuadPlus 2 S.K)).map S.actHom,
          (CFSG.MatrixModel.isometryCore (StatedQuadPlus 2 S.K)).map S.actHom⁆ :=
        Subgroup.commutator_mono hle hle
    _ = (⁅CFSG.MatrixModel.isometryCore (StatedQuadPlus 2 S.K),
          CFSG.MatrixModel.isometryCore (StatedQuadPlus 2 S.K)⁆).map S.actHom :=
        (Subgroup.map_commutator _ _ S.actHom).symm
    _ = S.omega := rfl

end OmegaModel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
