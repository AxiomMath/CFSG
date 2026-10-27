module

public import CFSG.OddTranspositions.O4Minus5Pair
public import CFSG.Open.FischerThreeTranspositionMilestoneDefs
import CFSG.OddTranspositions.O4PairTransport
import CFSG.OddTranspositions.O4PairFixSubgroup
import CFSG.OddTranspositions.O4PairClass65Lang
public import CFSG.Open.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.OddTranspositions.PartFour

section Herm

open CFSG.OddTranspositions.QZ CFSG.GorensteinWalter Matrix

private theorem five_eq_zero : (5 : ZMod 5) = 0 := by decide

private def sg : F25t →+* F25t := frob25t.toRingHom

private theorem sg_apply (x : F25t) : sg x = ⟨x.a, -x.b⟩ := rfl

private theorem sg_sg (x : F25t) : sg (sg x) = x := by
  simp [sg_apply]

private def toHerm (v : Fin 4 → ZMod 5) : Matrix (Fin 2) (Fin 2) F25t :=
  !![⟨v 0, 0⟩, ⟨v 2, v 3⟩; ⟨v 2, -v 3⟩, ⟨v 1, 0⟩]

private def ofHerm (A : Matrix (Fin 2) (Fin 2) F25t) : Fin 4 → ZMod 5 :=
  ![(A 0 0).a, (A 1 1).a, (A 0 1).a, (A 0 1).b]

private def IsHerm (A : Matrix (Fin 2) (Fin 2) F25t) : Prop := Aᵀ = A.map sg

private theorem ofHerm_toHerm (v : Fin 4 → ZMod 5) : ofHerm (toHerm v) = v := by
  ext i; fin_cases i <;> simp [ofHerm, toHerm]

private theorem isHerm_toHerm (v : Fin 4 → ZMod 5) : IsHerm (toHerm v) := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [toHerm, sg_apply]

private theorem zmod5_eq_neg {x : ZMod 5} (h : x = -x) : x = 0 := by
  revert x; decide

private theorem toHerm_ofHerm {A : Matrix (Fin 2) (Fin 2) F25t} (hA : IsHerm A) :
    toHerm (ofHerm A) = A := by
  have h00 := congrFun (congrFun hA 0) 0
  have h11 := congrFun (congrFun hA 1) 1
  have h01 := congrFun (congrFun hA 0) 1
  have h10 := congrFun (congrFun hA 1) 0
  simp only [transpose_apply, map_apply, sg_apply] at h00 h11 h01 h10
  have hb0 : (A 0 0).b = 0 := zmod5_eq_neg (congrArg F25t.b h00)
  have hb1 : (A 1 1).b = 0 := zmod5_eq_neg (congrArg F25t.b h11)
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [toHerm, ofHerm]
  · exact F25t.ext rfl hb0.symm
  · exact h01.symm
  · exact F25t.ext rfl hb1.symm

private def Phi (g A : Matrix (Fin 2) (Fin 2) F25t) : Matrix (Fin 2) (Fin 2) F25t :=
  g * A * (g.map sg)ᵀ

private theorem map_sg_one : (1 : Matrix (Fin 2) (Fin 2) F25t).map sg = 1 :=
  Matrix.map_one sg (map_zero sg) (map_one sg)

private theorem map_sg_sg (g : Matrix (Fin 2) (Fin 2) F25t) : (g.map sg).map sg = g :=
  Matrix.ext fun i j => by simp [sg_sg]

private theorem Phi_one (A : Matrix (Fin 2) (Fin 2) F25t) : Phi 1 A = A := by
  simp [Phi, map_sg_one]

private theorem Phi_mul (g h A : Matrix (Fin 2) (Fin 2) F25t) :
    Phi (g * h) A = Phi g (Phi h A) := by
  simp only [Phi, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]

private theorem Phi_add (g A B : Matrix (Fin 2) (Fin 2) F25t) :
    Phi g (A + B) = Phi g A + Phi g B := by
  simp [Phi, Matrix.mul_add, Matrix.add_mul]

private theorem Phi_zero (g : Matrix (Fin 2) (Fin 2) F25t) : Phi g 0 = 0 := by
  simp [Phi]

private theorem isHerm_Phi {A : Matrix (Fin 2) (Fin 2) F25t} (hA : IsHerm A)
    (g : Matrix (Fin 2) (Fin 2) F25t) : IsHerm (Phi g A) := by
  have hX : ((g.map sg)ᵀ).map sg = gᵀ := by rw [← Matrix.transpose_map, map_sg_sg]
  unfold IsHerm Phi at *
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hA,
    Matrix.map_mul, Matrix.map_mul, hX, Matrix.mul_assoc]

private def toHermAdd : (Fin 4 → ZMod 5) →+ Matrix (Fin 2) (Fin 2) F25t where
  toFun := toHerm
  map_zero' := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [toHerm]
  map_add' v w := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [toHerm]
    ring

private def ofHermAdd : Matrix (Fin 2) (Fin 2) F25t →+ (Fin 4 → ZMod 5) where
  toFun := ofHerm
  map_zero' := by
    ext i; fin_cases i <;> simp [ofHerm]
  map_add' A B := by
    ext i; fin_cases i <;> simp [ofHerm]

private def PhiAdd (g : Matrix (Fin 2) (Fin 2) F25t) :
    Matrix (Fin 2) (Fin 2) F25t →+ Matrix (Fin 2) (Fin 2) F25t where
  toFun := Phi g
  map_zero' := Phi_zero g
  map_add' := Phi_add g

private def actAdd (g : Matrix (Fin 2) (Fin 2) F25t) : (Fin 4 → ZMod 5) →+ (Fin 4 → ZMod 5) :=
  ofHermAdd.comp ((PhiAdd g).comp toHermAdd)

private def actL (g : Matrix (Fin 2) (Fin 2) F25t) :
    (Fin 4 → ZMod 5) →ₗ[ZMod 5] (Fin 4 → ZMod 5) :=
  (actAdd g).toZModLinearMap 5

private theorem actL_apply (g : Matrix (Fin 2) (Fin 2) F25t) (v : Fin 4 → ZMod 5) :
    actL g v = ofHerm (Phi g (toHerm v)) := rfl

private theorem actL_one : actL 1 = LinearMap.id :=
  LinearMap.ext fun v => by simp [actL_apply, Phi_one, ofHerm_toHerm]

private theorem actL_mul (g h : Matrix (Fin 2) (Fin 2) F25t) :
    actL (g * h) = actL g * actL h := by
  refine LinearMap.ext fun v => ?_
  rw [Module.End.mul_apply, actL_apply, actL_apply, actL_apply, Phi_mul,
    toHerm_ofHerm (isHerm_Phi (isHerm_toHerm v) h)]

private def matOf (g : Matrix (Fin 2) (Fin 2) F25t) : Matrix (Fin 4) (Fin 4) (ZMod 5) :=
  LinearMap.toMatrix' (actL g)

private theorem matOf_mulVec (g : Matrix (Fin 2) (Fin 2) F25t) (v : Fin 4 → ZMod 5) :
    matOf g *ᵥ v = ofHerm (Phi g (toHerm v)) := by
  rw [matOf, LinearMap.toMatrix'_mulVec, actL_apply]

private theorem matOf_one : matOf 1 = 1 := by
  rw [matOf, actL_one, LinearMap.toMatrix'_id]

private theorem matOf_mul (g h : Matrix (Fin 2) (Fin 2) F25t) :
    matOf (g * h) = matOf g * matOf h := by
  rw [matOf, matOf, matOf, actL_mul, LinearMap.toMatrix'_mul]

private def slHom : Matrix.SpecialLinearGroup (Fin 2) F25t →* Matrix (Fin 4) (Fin 4) (ZMod 5) where
  toFun A := matOf (A : Matrix (Fin 2) (Fin 2) F25t)
  map_one' := by simpa using matOf_one
  map_mul' A B := by simpa using matOf_mul (A : Matrix (Fin 2) (Fin 2) F25t) B

private def slGL : Matrix.SpecialLinearGroup (Fin 2) F25t →* GL (Fin 4) (ZMod 5) :=
  slHom.toHomUnits

private theorem Phi_neg_one (A : Matrix (Fin 2) (Fin 2) F25t) : Phi (-1) A = A := by
  have : ((-1 : Matrix (Fin 2) (Fin 2) F25t).map sg) = -1 := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [sg_apply]
  simp [Phi, this]

private theorem actL_neg_one : actL (-1) = LinearMap.id :=
  LinearMap.ext fun v => by simp [actL_apply, Phi_neg_one, ofHerm_toHerm]

private theorem slGL_center (A : Matrix.SpecialLinearGroup (Fin 2) F25t)
    (hA : A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F25t)) : slGL A = 1 := by
  rcases (CFSG.PSL2Table.mem_center_SL_iff A).mp hA with rfl | rfl
  · exact map_one _
  · refine Units.ext ?_
    have h : matOf (-1) = 1 := by rw [matOf, actL_neg_one, LinearMap.toMatrix'_id]
    simpa [slGL, slHom] using h

private def psiN : PSL2 F25t →* GL (Fin 4) (ZMod 5) :=
  QuotientGroup.lift (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F25t)) slGL
    (fun A hA => (MonoidHom.mem_ker).mpr (slGL_center A hA))

private theorem psiN_mk_coe (A : Matrix.SpecialLinearGroup (Fin 2) F25t) :
    ((psiN (CFSG.PSL2Table.mk A) : GL (Fin 4) (ZMod 5)) : Matrix (Fin 4) (Fin 4) (ZMod 5)) =
      matOf (A : Matrix (Fin 2) (Fin 2) F25t) := rfl

private def negb (v : Fin 4 → ZMod 5) : Fin 4 → ZMod 5 := ![v 0, v 1, v 2, -v 3]

private theorem toHerm_negb (v : Fin 4 → ZMod 5) : toHerm (negb v) = (toHerm v).map sg := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [toHerm, negb, sg_apply]

private theorem ofHerm_map_sg (M : Matrix (Fin 2) (Fin 2) F25t) :
    ofHerm (M.map sg) = negb (ofHerm M) := by
  ext i; fin_cases i <;> simp [ofHerm, negb, sg_apply]

private theorem Phi_map_sg (A M : Matrix (Fin 2) (Fin 2) F25t) :
    (Phi A (M.map sg)).map sg = Phi (A.map sg) M := by
  have hX : ((A.map sg)ᵀ).map sg = Aᵀ := by rw [← Matrix.transpose_map, map_sg_sg]
  simp only [Phi, Matrix.map_mul, hX, map_sg_sg]

private def r0m : Matrix (Fin 4) (Fin 4) (ZMod 5) := Matrix.diagonal ![1, 1, 1, -1]

private theorem r0m_mulVec (v : Fin 4 → ZMod 5) : r0m *ᵥ v = negb v := by
  ext i
  rw [r0m, Matrix.mulVec_diagonal]
  fin_cases i <;> simp [negb]

private theorem r0m_mul_self : r0m * r0m = 1 := by
  rw [r0m, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i; fin_cases i <;> simp

private def R0 : GL (Fin 4) (ZMod 5) := ⟨r0m, r0m, r0m_mul_self, r0m_mul_self⟩

private theorem R0_mul_self : R0 * R0 = 1 := Units.ext r0m_mul_self

private theorem R0_inv : R0⁻¹ = R0 := inv_eq_of_mul_eq_one_right R0_mul_self

private theorem matOf_map_sg (A : Matrix (Fin 2) (Fin 2) F25t) :
    matOf (A.map sg) = r0m * matOf A * r0m := by
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  simp only [Matrix.toLin'_apply]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, r0m_mulVec, matOf_mulVec, matOf_mulVec,
    r0m_mulVec, toHerm_negb, ← ofHerm_map_sg, Phi_map_sg]

open scoped Classical in
private noncomputable def f2 : (F25t ≃+* F25t) →* GL (Fin 4) (ZMod 5) where
  toFun τ := if τ = 1 then 1 else R0
  map_one' := by simp
  map_mul' a b := by
    rcases psl2FieldAut_eq_one_or_frob25t a with rfl | rfl <;>
    rcases psl2FieldAut_eq_one_or_frob25t b with rfl | rfl <;>
    simp [frob25t_mul_self, frob25t_ne_one, R0_mul_self]

private theorem f2_frob : f2 frob25t = R0 := by
  simp [f2, frob25t_ne_one]

private theorem psl2FieldAut_mk' (e : F25t ≃+* F25t)
    (A : Matrix.SpecialLinearGroup (Fin 2) F25t) :
    psl2FieldAut F25t e (CFSG.PSL2Table.mk A) =
      CFSG.PSL2Table.mk (Matrix.SpecialLinearGroup.map e.toRingHom A) := by
  show CFSG.GorensteinWalter.psl2RingEquiv e
      (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F25t)) A) = _
  rw [CFSG.GorensteinWalter.psl2RingEquiv_mk]
  rfl

private theorem compat (τ : F25t ≃+* F25t) :
    psiN.comp (psl2FieldAut F25t τ).toMonoidHom =
      (MulAut.conj (f2 τ)).toMonoidHom.comp psiN := by
  rcases psl2FieldAut_eq_one_or_frob25t τ with rfl | rfl
  · refine MonoidHom.ext fun x => ?_
    simp [f2]
  · refine MonoidHom.ext fun x => ?_
    obtain ⟨A, rfl⟩ := CFSG.PSL2Table.mk_surjective x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, f2_frob,
      R0_inv, psl2FieldAut_mk']
    refine Units.ext ?_
    rw [psiN_mk_coe, Units.val_mul, Units.val_mul, psiN_mk_coe]
    exact matOf_map_sg _

private noncomputable def psi : PSigmaL2t →* GL (Fin 4) (ZMod 5) :=
  SemidirectProduct.lift psiN f2 compat

private theorem psi_inl (x : PSL2 F25t) : psi (SemidirectProduct.inl x) = psiN x :=
  SemidirectProduct.lift_inl _ _ _ _

private theorem psi_inr_frob : psi (SemidirectProduct.inr frob25t) = R0 := by
  rw [psi, SemidirectProduct.lift_inr, f2_frob]

private def bform : LinearMap.BilinForm (ZMod 5) (Fin 4 → ZMod 5) :=
  LinearMap.mk₂ (ZMod 5) (fun x y => x 0 * y 1 + x 1 * y 0 + 3 * x 2 * y 2 + x 3 * y 3)
    (by intros; simp only [Pi.add_apply]; ring)
    (by intros; simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (by intros; simp only [Pi.add_apply]; ring)
    (by intros; simp only [Pi.smul_apply, smul_eq_mul]; ring)

private theorem bform_apply (x y : Fin 4 → ZMod 5) :
    bform x y = x 0 * y 1 + x 1 * y 0 + 3 * x 2 * y 2 + x 3 * y 3 := rfl

private theorem bform_symm (x y : Fin 4 → ZMod 5) : bform x y = bform y x := by
  simp only [bform_apply]; ring

private theorem bform_nondeg (x : Fin 4 → ZMod 5) (h : ∀ y, bform x y = 0) : x = 0 := by
  have h0 := h ![1, 0, 0, 0]
  have h1 := h ![0, 1, 0, 0]
  have h2 := h ![0, 0, 1, 0]
  have h3 := h ![0, 0, 0, 1]
  simp [bform_apply] at h0 h1 h2 h3
  have h2' : x 2 = 0 := by
    have key : ∀ z : ZMod 5, 3 * z = 0 → z = 0 := by decide
    exact key _ h2
  ext i; fin_cases i <;> simp [h0, h1, h2', h3]

private def Qf (v : Fin 4 → ZMod 5) : ZMod 5 := v 0 * v 1 - v 2 ^ 2 + 3 * v 3 ^ 2

private theorem bform_eq_Qf (x y : Fin 4 → ZMod 5) :
    bform x y = Qf (x + y) - Qf x - Qf y := by
  simp only [bform_apply, Qf, Pi.add_apply]
  linear_combination (x 2 * y 2 - x 3 * y 3) * five_eq_zero

private theorem det_toHerm (v : Fin 4 → ZMod 5) : (toHerm v).det = ⟨Qf v, 0⟩ := by
  rw [Matrix.det_fin_two, sub_eq_add_neg]
  apply F25t.ext <;> simp [toHerm, Qf] <;> ring

private theorem Qf_matOf (g : Matrix.SpecialLinearGroup (Fin 2) F25t) (v : Fin 4 → ZMod 5) :
    Qf (matOf (g : Matrix (Fin 2) (Fin 2) F25t) *ᵥ v) = Qf v := by
  rw [matOf_mulVec]
  have hH := isHerm_Phi (isHerm_toHerm v) (g : Matrix (Fin 2) (Fin 2) F25t)
  have h1 : (⟨Qf (ofHerm (Phi (g : Matrix (Fin 2) (Fin 2) F25t) (toHerm v))), 0⟩ : F25t) =
      ⟨Qf v, 0⟩ := by
    rw [← det_toHerm, toHerm_ofHerm hH, ← det_toHerm]
    unfold Phi
    have hdet : ((g : Matrix (Fin 2) (Fin 2) F25t).map sg).det = 1 := by
      have h := RingHom.map_det sg (g : Matrix (Fin 2) (Fin 2) F25t)
      rw [RingHom.mapMatrix_apply, Matrix.SpecialLinearGroup.det_coe, map_one] at h
      exact h.symm
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdet,
      Matrix.SpecialLinearGroup.det_coe, one_mul, mul_one]
  exact congrArg F25t.a h1

private def IsIsom (M : GL (Fin 4) (ZMod 5)) : Prop :=
  ∀ x y, bform ((M : Matrix (Fin 4) (Fin 4) (ZMod 5)) *ᵥ x)
    ((M : Matrix (Fin 4) (Fin 4) (ZMod 5)) *ᵥ y) = bform x y

private theorem IsIsom.mul {M N : GL (Fin 4) (ZMod 5)} (hM : IsIsom M) (hN : IsIsom N) :
    IsIsom (M * N) := by
  intro x y
  simp only [Units.val_mul, ← Matrix.mulVec_mulVec]
  rw [hM, hN]

private theorem IsIsom.one : IsIsom 1 := by
  intro x y; simp

private theorem isIsom_slGL (A : Matrix.SpecialLinearGroup (Fin 2) F25t) : IsIsom (slGL A) := by
  intro x y
  have hmv : ((slGL A : GL (Fin 4) (ZMod 5)) : Matrix (Fin 4) (Fin 4) (ZMod 5)) =
      matOf (A : Matrix (Fin 2) (Fin 2) F25t) := rfl
  rw [hmv, bform_eq_Qf, bform_eq_Qf x y, ← Matrix.mulVec_add, Qf_matOf, Qf_matOf, Qf_matOf]

private theorem isIsom_R0 : IsIsom R0 := by
  intro x y
  have hR : ((R0 : GL (Fin 4) (ZMod 5)) : Matrix (Fin 4) (Fin 4) (ZMod 5)) = r0m := rfl
  rw [hR, r0m_mulVec, r0m_mulVec]
  simp only [bform_apply, negb]
  simp

private theorem isIsom_f2 (τ : F25t ≃+* F25t) : IsIsom (f2 τ) := by
  rcases psl2FieldAut_eq_one_or_frob25t τ with rfl | rfl
  · rw [map_one]; exact IsIsom.one
  · rw [f2_frob]; exact isIsom_R0

private theorem isIsom_psi (g : PSigmaL2t) : IsIsom (psi g) := by
  obtain ⟨q, τ⟩ := g
  rw [SemidirectProduct.mk_eq_inl_mul_inr, map_mul, psi_inl]
  refine IsIsom.mul ?_ ?_
  · obtain ⟨A, rfl⟩ := CFSG.PSL2Table.mk_surjective q
    exact isIsom_slGL A
  · rw [psi, SemidirectProduct.lift_inr]
    exact isIsom_f2 τ

private theorem conj_refl {M g : GL (Fin 4) (ZMod 5)} (hM : IsIsom M) {v : Fin 4 → ZMod 5}
    (hg : ∀ x, (g : Matrix (Fin 4) (Fin 4) (ZMod 5)) *ᵥ x = x + (-2 * bform x v) • v)
    (x : Fin 4 → ZMod 5) :
    ((M * g * M⁻¹ : GL (Fin 4) (ZMod 5)) : Matrix (Fin 4) (Fin 4) (ZMod 5)) *ᵥ x =
      x + (-2 * bform x ((M : Matrix (Fin 4) (Fin 4) (ZMod 5)) *ᵥ v)) •
        ((M : Matrix (Fin 4) (Fin 4) (ZMod 5)) *ᵥ v) := by
  set y : Fin 4 → ZMod 5 := ((M⁻¹ : GL (Fin 4) (ZMod 5)) : Matrix (Fin 4) (Fin 4) (ZMod 5)) *ᵥ x
    with hy
  have hMy : (M : Matrix (Fin 4) (Fin 4) (ZMod 5)) *ᵥ y = x := by
    rw [hy, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hb : bform y v = bform x ((M : Matrix (Fin 4) (Fin 4) (ZMod 5)) *ᵥ v) := by
    rw [← hM y v, hMy]
  simp only [Units.val_mul]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hy, hg y, Matrix.mulVec_add,
    Matrix.mulVec_smul, hMy, hb]

private abbrev Tset : Set (GL (Fin 4) (ZMod 5)) :=
  CFSG.Open.fischerTransvections (fun x y => -2 * bform x y) fun v => bform v v = 1

private def e3 : Fin 4 → ZMod 5 := ![0, 0, 0, 1]

private theorem bform_e3 : bform e3 e3 = 1 := by simp [bform_apply, e3]

private theorem R0_refl (x : Fin 4 → ZMod 5) :
    ((R0 : GL (Fin 4) (ZMod 5)) : Matrix (Fin 4) (Fin 4) (ZMod 5)) *ᵥ x =
      x + (-2 * bform x e3) • e3 := by
  show r0m *ᵥ x = _
  rw [r0m_mulVec]
  ext i
  fin_cases i <;> simp [negb, bform_apply, e3]
  ring

private theorem psi_mem_T {c : PSigmaL2t} (hc : c ∈ class65t) : psi c ∈ Tset := by
  obtain ⟨h, rfl⟩ := isConj_iff.mp ((mem_class65t_iff c).mp hc)
  refine ⟨(psi h : Matrix (Fin 4) (Fin 4) (ZMod 5)) *ᵥ e3, ?_, ?_⟩
  · show bform _ _ = 1
    rw [isIsom_psi h e3 e3, bform_e3]
  · intro x
    rw [map_mul, map_mul, map_inv, psi_inr_frob]
    exact conj_refl (isIsom_psi h) R0_refl x

private def bf (x y : Fin 4 → ZMod 5) : ZMod 5 := x 0 * y 1 + x 1 * y 0 + 3 * x 2 * y 2 + x 3 * y 3

private theorem bform_eq_bf (x y : Fin 4 → ZMod 5) : bform x y = bf x y := rfl

private def posv (v : Fin 4 → ZMod 5) : Prop :=
  (v 0 = 1 ∨ v 0 = 2) ∨ (v 0 = 0 ∧ ((v 1 = 1 ∨ v 1 = 2) ∨ (v 1 = 0 ∧ ((v 2 = 1 ∨ v 2 = 2) ∨
    (v 2 = 0 ∧ (v 3 = 1 ∨ v 3 = 2))))))

private instance posvDec (v : Fin 4 → ZMod 5) : Decidable (posv v) := by
  unfold posv; infer_instance

set_option maxRecDepth 100000 in
private theorem posv_or_neg : ∀ v : Fin 4 → ZMod 5, v ≠ 0 → posv v ∨ posv (-v) := by
  decide

private def Vplus : Finset (Fin 4 → ZMod 5) := Finset.univ.filter fun v => bf v v = 1 ∧ posv v

set_option maxRecDepth 100000 in
private theorem card_Vplus : Vplus.card = 65 := by decide

private def actFn (M : GL (Fin 4) (ZMod 5)) : (Fin 4 → ZMod 5) → (Fin 4 → ZMod 5) :=
  fun x => (M : Matrix (Fin 4) (Fin 4) (ZMod 5)) *ᵥ x

private theorem actFn_injective : Function.Injective actFn := by
  intro M N h
  apply Units.ext
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  simpa [actFn] using congrFun h v

private def reflFn (v : Fin 4 → ZMod 5) : (Fin 4 → ZMod 5) → (Fin 4 → ZMod 5) :=
  fun x => x + (-2 * bform x v) • v

private theorem reflFn_neg (v : Fin 4 → ZMod 5) : reflFn (-v) = reflFn v := by
  funext x
  simp [reflFn]

private theorem Tset_ncard_le : Tset.ncard ≤ 65 := by
  have hsub : actFn '' Tset ⊆ reflFn '' (Vplus : Set (Fin 4 → ZMod 5)) := by
    rintro _ ⟨M, ⟨v, hv, hM⟩, rfl⟩
    have hv0 : v ≠ 0 := by
      rintro rfl
      have h01 : (0 : ZMod 5) ≠ 1 := by decide
      apply h01
      simpa [bform_apply] using hv
    rcases posv_or_neg v hv0 with hp | hp
    · refine ⟨v, ?_, ?_⟩
      · simp only [Vplus, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
        exact ⟨hv, hp⟩
      · funext x; exact (hM x).symm
    · refine ⟨-v, ?_, ?_⟩
      · simp only [Vplus, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
        refine ⟨?_, hp⟩
        rw [← bform_eq_bf]
        simpa using hv
      · rw [reflFn_neg]; funext x; exact (hM x).symm
  calc Tset.ncard = (actFn '' Tset).ncard :=
        (Set.ncard_image_of_injective _ actFn_injective).symm
    _ ≤ (reflFn '' (Vplus : Set (Fin 4 → ZMod 5))).ncard :=
        Set.ncard_le_ncard hsub ((Finset.finite_toSet _).image _)
    _ ≤ (Vplus : Set (Fin 4 → ZMod 5)).ncard := Set.ncard_image_le (Finset.finite_toSet _)
    _ = 65 := by rw [Set.ncard_coe_finset, card_Vplus]

section Inj

open CFSG.PSL2Table

private theorem f25t_eq_neg {x : F25t} (h : x = -x) : x = 0 :=
  F25t.ext (zmod5_eq_neg (congrArg F25t.a h)) (zmod5_eq_neg (congrArg F25t.b h))

private theorem map_unip (t : F25t) :
    Matrix.SpecialLinearGroup.map frob25t.toRingHom (unip t) = unip (frob25t t) := by
  apply SL_ext <;> simp [Matrix.SpecialLinearGroup.map_apply_coe, -one25_def, -zero25_def]

private theorem unip_00 (t : F25t) : (unip t : Matrix (Fin 2) (Fin 2) F25t) 0 0 = 1 := rfl
private theorem unip_01 (t : F25t) : (unip t : Matrix (Fin 2) (Fin 2) F25t) 0 1 = t := rfl
private theorem unip_10 (t : F25t) : (unip t : Matrix (Fin 2) (Fin 2) F25t) 1 0 = 0 := rfl
private theorem unip_11 (t : F25t) : (unip t : Matrix (Fin 2) (Fin 2) F25t) 1 1 = 1 := rfl

private theorem no_inner_frob :
    ¬ ∃ n : PSL2 F25t, ∀ x : PSL2 F25t, n * psl2FieldAut F25t frob25t x = x * n := by
  rintro ⟨n, hn⟩
  obtain ⟨A, rfl⟩ := mk_surjective n
  have h1 := hn (mk (unip 1))
  rw [psl2FieldAut_mk', map_unip, map_one, ← map_mul, ← map_mul, mk_eq_mk_iff] at h1
  have hdet := det_entries A
  have hcomm : (A : Matrix (Fin 2) (Fin 2) F25t) 1 0 = 0 ∧
      (A : Matrix (Fin 2) (Fin 2) F25t) 1 1 = (A : Matrix (Fin 2) (Fin 2) F25t) 0 0 := by
    rcases h1 with h | h
    · have e00 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) F25t =>
        (M : Matrix (Fin 2) (Fin 2) F25t) 0 0) h
      have e01 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) F25t =>
        (M : Matrix (Fin 2) (Fin 2) F25t) 0 1) h
      simp only [mul_apply_SL, unip_00, unip_01, unip_10, unip_11] at e00 e01
      exact ⟨by linear_combination e00, by linear_combination e01⟩
    · exfalso
      have e00 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) F25t =>
        (M : Matrix (Fin 2) (Fin 2) F25t) 0 0) h
      have e10 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) F25t =>
        (M : Matrix (Fin 2) (Fin 2) F25t) 1 0) h
      have e11 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) F25t =>
        (M : Matrix (Fin 2) (Fin 2) F25t) 1 1) h
      simp only [mul_apply_SL, neg_apply_SL, unip_00, unip_01, unip_10, unip_11] at e00 e10 e11
      have hr : (A : Matrix (Fin 2) (Fin 2) F25t) 1 0 = 0 :=
        f25t_eq_neg (by linear_combination e10)
      have hp : (A : Matrix (Fin 2) (Fin 2) F25t) 0 0 = 0 :=
        f25t_eq_neg (by linear_combination e00 - hr)
      have hs : (A : Matrix (Fin 2) (Fin 2) F25t) 1 1 = 0 :=
        f25t_eq_neg (by linear_combination e11 - hr)
      rw [hp, hs, hr] at hdet
      simp only [mul_zero, sub_zero] at hdet
      exact zero_ne_one hdet
  obtain ⟨hr, hs⟩ := hcomm
  have hAcomm : ∀ t : F25t, A * unip t = unip t * A := by
    intro t
    apply SL_ext <;> simp only [mul_apply_SL, unip_00, unip_01, unip_10, unip_11, hr, hs] <;> ring
  have h2 := hn (mk (unip ⟨0, 1⟩))
  rw [psl2FieldAut_mk', map_unip, ← map_mul, ← map_mul, ← hAcomm] at h2
  have h3 : mk (unip (frob25t ⟨0, 1⟩)) = mk (unip ⟨0, 1⟩) := by
    rw [map_mul, map_mul] at h2
    exact mul_left_cancel h2
  rw [mk_eq_mk_iff] at h3
  rcases h3 with h3 | h3
  · have := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) F25t =>
      (M : Matrix (Fin 2) (Fin 2) F25t) 0 1) h3
    simp only [unip_01] at this
    have hb := congrArg F25t.b this
    revert hb
    decide
  · have := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) F25t =>
      (M : Matrix (Fin 2) (Fin 2) F25t) 0 0) h3
    simp only [neg_apply_SL, unip_00] at this
    have ha := congrArg F25t.a this
    revert ha
    decide

private theorem right_eq_one_of_comm (z : PSigmaL2t)
    (hz : ∀ x : PSL2 F25t, z * SemidirectProduct.inl x = SemidirectProduct.inl x * z) :
    z.right = 1 := by
  rcases psl2FieldAut_eq_one_or_frob25t z.right with h | h
  · exact h
  · exfalso
    refine no_inner_frob ⟨z.left, fun x => ?_⟩
    have := congrArg SemidirectProduct.left (hz x)
    simpa [SemidirectProduct.mul_left, h] using this

private theorem psiN_ne_one : psiN (mk (unip (1 : F25t))) ≠ 1 := by
  intro h
  have hm : matOf ((unip (1 : F25t) : Matrix.SpecialLinearGroup (Fin 2) F25t) :
      Matrix (Fin 2) (Fin 2) F25t) = 1 := by
    have := congrArg (fun g : GL (Fin 4) (ZMod 5) => (g : Matrix (Fin 4) (Fin 4) (ZMod 5))) h
    simpa [psiN_mk_coe] using this
  have h2 := congrFun (congrArg (fun M => M *ᵥ (![0, 1, 0, 0] : Fin 4 → ZMod 5)) hm) 0
  simp only [matOf_mulVec, Matrix.one_mulVec] at h2
  simp [ofHerm, Phi, toHerm, Matrix.mul_apply, Fin.sum_univ_two, sg_apply] at h2
  exact absurd h2 (by decide)

private theorem simple_PSL2 : IsSimpleGroup (PSL2 F25t) :=
  Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [card_F25t_nat]; norm_num)

private theorem psiN_injective : Function.Injective psiN := by
  have := simple_PSL2
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal psiN.ker with h | h
  · exact h
  · exfalso
    refine psiN_ne_one ?_
    have : mk (unip (1 : F25t)) ∈ psiN.ker := by rw [h]; trivial
    exact this

private theorem psi_injective : Function.Injective psi := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  rw [Subgroup.mem_bot]
  have hcomm : ∀ x : PSL2 F25t,
      g * SemidirectProduct.inl x = SemidirectProduct.inl x * g := by
    intro x
    have hmem : g * SemidirectProduct.inl x * g⁻¹ * (SemidirectProduct.inl x)⁻¹ ∈
        (SemidirectProduct.inl : PSL2 F25t →* PSigmaL2t).range := by
      rw [SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
      simp
    obtain ⟨y, hy⟩ := hmem
    have hpsi : psiN y = 1 := by
      have := congrArg psi hy
      rw [psi_inl] at this
      simpa [hg, psi_inl] using this
    have hy1 : y = 1 := psiN_injective (hpsi.trans (map_one psiN).symm)
    rw [hy1, map_one] at hy
    exact (commutatorElement_eq_one_iff_commute.mp hy.symm).eq
  have hright : g.right = 1 := right_eq_one_of_comm g hcomm
  have hg' : g = SemidirectProduct.inl g.left :=
    SemidirectProduct.ext (by simp) (by simp [hright])
  have hleft : g.left = 1 := by
    have h1 : psi g = psiN g.left := by
      calc psi g = psi (SemidirectProduct.inl g.left) := congrArg psi hg'
        _ = psiN g.left := psi_inl _
    exact psiN_injective ((h1.symm.trans hg).trans (map_one psiN).symm)
  calc g = SemidirectProduct.inl g.left := hg'
    _ = SemidirectProduct.inl 1 := by rw [hleft]
    _ = 1 := map_one _

private theorem exists_sq_ne : ∃ a : F25t, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
  refine ⟨⟨2, 0⟩, ?_, ?_⟩
  · intro h
    have := congrArg F25t.a h
    revert this
    decide
  · intro h
    have := congrArg F25t.a h
    simp only [pow_two, mul25_def, one25_def] at this
    revert this
    decide

private theorem center_PSL2_eq_bot : Subgroup.center (PSL2 F25t) = ⊥ := by
  have := simple_PSL2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (PSL2 F25t)) with h | h
  · exact h
  · exfalso
    have hc : commutator (PSL2 F25t) = ⊥ := (commutator_eq_bot_iff_center_eq_top (PSL2 F25t)).mpr h
    have htop : commutator (PSL2 F25t) = ⊤ := SL2Simple.PSL_commutator_eq_top exists_sq_ne
    obtain ⟨x, y, hxy⟩ := (inferInstance : Nontrivial (PSL2 F25t)).exists_pair_ne
    have hx : x ∈ commutator (PSL2 F25t) := by rw [htop]; trivial
    have hy : y ∈ commutator (PSL2 F25t) := by rw [htop]; trivial
    rw [hc, Subgroup.mem_bot] at hx hy
    exact hxy (hx.trans hy.symm)

private theorem center_psigma_eq_bot : Subgroup.center PSigmaL2t = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hcomm : ∀ x : PSL2 F25t, z * SemidirectProduct.inl x = SemidirectProduct.inl x * z :=
    fun x => ((Subgroup.mem_center_iff.mp hz) (SemidirectProduct.inl x)).symm
  have hright : z.right = 1 := right_eq_one_of_comm z hcomm
  have hz' : z = SemidirectProduct.inl z.left :=
    SemidirectProduct.ext (by simp) (by simp [hright])
  have hc : z.left ∈ Subgroup.center (PSL2 F25t) := by
    rw [Subgroup.mem_center_iff]
    intro x
    have h : (SemidirectProduct.inl z.left : PSigmaL2t) * SemidirectProduct.inl x =
        SemidirectProduct.inl x * SemidirectProduct.inl z.left := by
      rw [← hz']; exact hcomm x
    rw [← map_mul, ← map_mul] at h
    exact (SemidirectProduct.inl_injective h).symm
  rw [center_PSL2_eq_bot, Subgroup.mem_bot] at hc
  calc z = SemidirectProduct.inl z.left := hz'
    _ = SemidirectProduct.inl 1 := by rw [hc]
    _ = 1 := map_one _

end Inj

private theorem card_class65t_eq : Nat.card class65t = 65 :=
  card_class65t_of_card_fix (by
    rw [← card_FixG]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun q => eq_comm))

private theorem psi_image_class65t : psi '' class65t = Tset := by
  have hsub : psi '' class65t ⊆ Tset := by
    rintro _ ⟨c, hc, rfl⟩
    exact psi_mem_T hc
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
  have hc : class65t.ncard = 65 := by
    rw [← Nat.card_coe_set_eq]
    exact card_class65t_eq
  rw [Set.ncard_image_of_injective _ psi_injective, hc]
  exact Tset_ncard_le

private theorem closure_class65t_eq_top : Subgroup.closure class65t = ⊤ := by
  have h1 : (Subgroup.closure class65t).map (psigmaL2Equiv : PSigmaL2t →* PSigmaL225) = ⊤ := by
    rw [MonoidHom.map_closure]
    have : ((psigmaL2Equiv : PSigmaL2t →* PSigmaL225) '' class65t) = class65 :=
      psigmaL2Equiv_image_class65t
    rw [this]
    exact closure_class65_eq_top
  have h2 := Subgroup.comap_map_eq_self_of_injective
    (f := (psigmaL2Equiv : PSigmaL2t →* PSigmaL225)) psigmaL2Equiv.injective
    (Subgroup.closure class65t)
  rw [h1, Subgroup.comap_top] at h2
  exact h2.symm

private theorem closure_Tset : Subgroup.closure Tset = psi.range := by
  rw [← psi_image_class65t, ← MonoidHom.map_closure, closure_class65t_eq_top,
    ← MonoidHom.range_eq_map]

private noncomputable def psiK : PSigmaL2t ≃* Subgroup.closure Tset :=
  (MonoidHom.ofInjective psi_injective).trans (MulEquiv.subgroupCongr closure_Tset.symm)

private theorem psiK_coe (g : PSigmaL2t) :
    ((psiK g : Subgroup.closure Tset) : GL (Fin 4) (ZMod 5)) = psi g := rfl

private theorem center_K_eq_bot : Subgroup.center (Subgroup.closure Tset) = ⊥ := by
  rw [eq_bot_iff]
  intro k hk
  rw [Subgroup.mem_bot]
  obtain ⟨g, rfl⟩ := psiK.surjective k
  have hg : g ∈ Subgroup.center PSigmaL2t := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply psiK.injective
    rw [map_mul, map_mul]
    exact (Subgroup.mem_center_iff.mp hk) (psiK x)
  rw [center_psigma_eq_bot, Subgroup.mem_bot] at hg
  rw [hg, map_one]

private noncomputable def centerQuotEquiv :
    Subgroup.closure Tset ≃* (Subgroup.closure Tset) ⧸ Subgroup.center (Subgroup.closure Tset) :=
  MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center (Subgroup.closure Tset)))
    ⟨by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', center_K_eq_bot],
     QuotientGroup.mk_surjective⟩

private theorem centerQuotEquiv_apply (k : Subgroup.closure Tset) :
    centerQuotEquiv k = (QuotientGroup.mk k : (Subgroup.closure Tset) ⧸
      Subgroup.center (Subgroup.closure Tset)) := rfl

private theorem model_aux {X : Type} [Group X] {E : Set X} (e : X ≃* PSigmaL225)
    (he : e '' E = class65) :
    CFSG.Open.fischerCentralQuotientModel E (Subgroup.closure Tset) Tset := by
  let e' : X ≃* PSigmaL2t := e.trans psigmaL2Equiv.symm
  have he' : e' '' E = class65t := by
    have h1 : (psigmaL2Equiv.symm : PSigmaL225 → PSigmaL2t) '' class65 = class65t := by
      rw [← psigmaL2Equiv_image_class65t, Set.image_image]
      simp
    rw [← h1, ← he, Set.image_image]
    rfl
  have hmem : ∀ g, g ∈ E ↔ e' g ∈ class65t := by
    intro g
    rw [← he']
    exact (e'.injective.mem_set_image).symm
  have hψ : ∀ x : GL (Fin 4) (ZMod 5), x ∈ Tset ↔ ∃ c ∈ class65t, psi c = x := by
    intro x
    rw [← psi_image_class65t]
    rfl
  refine ⟨(e'.trans psiK).trans centerQuotEquiv, fun g => ?_⟩
  constructor
  · intro hg
    refine ⟨psiK (e' g), ?_, rfl⟩
    rw [psiK_coe]
    exact (hψ _).mpr ⟨e' g, (hmem g).mp hg, rfl⟩
  · rintro ⟨k, hkT, hk⟩
    have hk' : psiK (e' g) = k := by
      apply centerQuotEquiv.injective
      rw [centerQuotEquiv_apply]
      exact hk
    have hkT' := (hψ _).mp hkT
    rw [← hk', psiK_coe] at hkT'
    obtain ⟨c, hc, hck⟩ := hkT'
    rw [psi_injective hck] at hc
    exact (hmem g).mpr hc

end Herm

variable {X : Type} [Group X]

theorem fischerModel_of_isO4Minus5Pair {E : Set X} (h : QZ.IsO4Minus5Pair X E) :
    ∃ b : LinearMap.BilinForm (ZMod 5) (Fin 4 → ZMod 5),
      (∀ x y, b x y = b y x) ∧ (∀ x, (∀ y, b x y = 0) → x = 0) ∧
      CFSG.Open.fischerCentralQuotientModel E
        (Subgroup.closure
          (CFSG.Open.fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1))
        (CFSG.Open.fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1) := by
  obtain ⟨e, he⟩ := h
  exact ⟨bform, bform_symm, bform_nondeg, model_aux e he⟩

end CFSG.OddTranspositions.PartFour
