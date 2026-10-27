module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotInvolutionCentralizer
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeTypeA
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionLinear
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentralizerBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.SeitzReduction.LinearPilot Matrix

namespace LinFusion

variable {m : ℕ} {F : Type} [Field F]

@[expose] def ggTransPlacement (hm : 1 ≤ m) : InvPlacement (m + 1) 1 where
  u := fun _ => Fin.last m
  w := fun _ => 0
  u_injective := fun a b _ => Subsingleton.elim a b
  w_injective := fun a b _ => Subsingleton.elim a b
  u_ne_w := fun _ _ h => by
    have h' := congrArg Fin.val h
    simp only [Fin.val_last, Fin.val_zero] at h'
    omega

theorem ggTransPlacement_u (hm : 1 ≤ m) (a : Fin 1) : (ggTransPlacement hm).u a = Fin.last m :=
  rfl

theorem ggTransPlacement_w (hm : 1 ≤ m) (a : Fin 1) : (ggTransPlacement hm).w a = 0 :=
  rfl

theorem ggTransPlacement_mat (hm : 1 ≤ m) :
    (ggTransPlacement hm).mat F = ggInvSL (m + 1) 1 F := by
  apply Subtype.ext
  rw [InvPlacement.coe_mat, coe_ggInvSL, ggInvMatrix_one m hm]
  congr 1
  ext i j
  simp only [InvPlacement.nil, of_apply, single_apply, ggTransPlacement, exists_const]

theorem det_eq_of_blockTriangular_one {n : ℕ} (P : InvPlacement n 1)
    {B : Matrix (Fin n) (Fin n) F} (hB : B.BlockTriangular P.level) :
    B.det = B (P.u 0) (P.u 0) *
      (B.submatrix (Subtype.val : P.free → Fin n) (Subtype.val : P.free → Fin n)).det *
        B (P.w 0) (P.w 0) := by
  classical
  let b : Fin n → Fin 3 := fun i => ⟨P.level i, by have := P.level_le_two i; omega⟩
  have hb : B.BlockTriangular b := fun i j hij => hB (by simpa [b, Fin.lt_def] using hij)
  rw [hb.det_fintype, Fin.prod_univ_three]
  have hu : ∀ x : {a // b a = 0}, (x : Fin n) = P.u 0 := by
    intro x
    obtain ⟨c, hc⟩ := P.level_eq_zero_iff.1 (congrArg Fin.val x.2)
    rw [← hc, Subsingleton.elim c 0]
  have hw : ∀ x : {a // b a = 2}, (x : Fin n) = P.w 0 := by
    intro x
    obtain ⟨c, hc⟩ := P.level_eq_two_iff.1 (congrArg Fin.val x.2)
    rw [← hc, Subsingleton.elim c 0]
  have : Subsingleton {a // b a = 0} := ⟨fun x y => Subtype.ext ((hu x).trans (hu y).symm)⟩
  have : Subsingleton {a // b a = 2} := ⟨fun x y => Subtype.ext ((hw x).trans (hw y).symm)⟩
  have hu0 : b (P.u 0) = 0 := Fin.ext (P.level_u 0)
  have hw0 : b (P.w 0) = 2 := Fin.ext (P.level_w 0)
  have h0 : (B.toSquareBlock b 0).det = B (P.u 0) (P.u 0) := by
    rw [det_eq_elem_of_subsingleton _ ⟨P.u 0, hu0⟩]
    rfl
  have h2 : (B.toSquareBlock b 2).det = B (P.w 0) (P.w 0) := by
    rw [det_eq_elem_of_subsingleton _ ⟨P.w 0, hw0⟩]
    rfl
  have he : ∀ i, b i = 1 ↔ i ∈ P.free := fun i => by
    rw [P.mem_free, Fin.ext_iff]
    rfl
  have h1 : (B.toSquareBlock b 1).det =
      (B.submatrix (Subtype.val : P.free → Fin n) (Subtype.val : P.free → Fin n)).det := by
    rw [← det_reindex_self (Equiv.subtypeEquivRight he)]
    rfl
  rw [h0, h1, h2]

theorem eq_one_of_specialLinearGroup_fin_one (a : SpecialLinearGroup (Fin 1) F) : a = 1 := by
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  have h := a.prop
  rw [det_unique] at h
  simpa using h

theorem core_le_ggOTwoPrime [CharP F 2] {n : ℕ} (P : InvPlacement n 1) :
    P.core F ≤ ggOTwoPrime (Subgroup.centralizer {P.mat F}) := by
  refine sup_le ?_ (sup_le ?_ ?_)
  · intro r hr
    exact Subgroup.subset_closure ⟨P.radical_le_centralizer hr, 2, P.radical_pow_four hr⟩
  · rintro _ ⟨a, rfl⟩
    rw [eq_one_of_specialLinearGroup_fin_one a, map_one]
    exact one_mem _
  · rw [blockSpecialLinear_eq_closure, Subgroup.closure_le]
    rintro _ ⟨i, j, hij, c, hi, hj, rfl⟩
    refine Subgroup.subset_closure ⟨P.blockSpecialLinear_free_le_centralizer
      (transvection_mem_blockSpecialLinear hij hi hj c), 1, ?_⟩
    rw [pow_one, pow_two]
    exact InvPlacement.transvection_mul_self hij c

theorem mem_ggOTwoPrime_centralizer_of_corner [CharP F 2] (hm : 1 ≤ m)
    {B : SpecialLinearGroup (Fin (m + 1)) F}
    (hB : B ∈ Subgroup.centralizer {ggInvSL (m + 1) 1 F})
    (h1 : (B : Matrix (Fin (m + 1)) (Fin (m + 1)) F) (Fin.last m) (Fin.last m) = 1) :
    B ∈ ggOTwoPrime (Subgroup.centralizer {ggInvSL (m + 1) 1 F}) := by
  set P := ggTransPlacement hm
  rw [← ggTransPlacement_mat hm] at hB ⊢
  obtain ⟨hBT, hBuw⟩ := P.mem_centralizer_mat_iff.1 hB
  have hdet := det_eq_of_blockTriangular_one P hBT
  have hu : (B : Matrix (Fin (m + 1)) (Fin (m + 1)) F) (P.u 0) (P.u 0) = 1 := h1
  have hw : (B : Matrix (Fin (m + 1)) (Fin (m + 1)) F) (P.w 0) (P.w 0) = 1 := by
    rw [hBuw 0 0]
    exact h1
  rw [B.prop, hu, hw, one_mul, mul_one] at hdet
  have h0 : ((B : Matrix (Fin (m + 1)) (Fin (m + 1)) F).submatrix P.u P.u).det = 1 := by
    rw [det_unique]
    exact h1
  exact core_le_ggOTwoPrime P (P.mem_core_of_det hB h0 hdet.symm)

theorem commute_single_of_commute (hm : 1 ≤ m) {A : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hA : A * ggInvMatrix (m + 1) 1 F = ggInvMatrix (m + 1) 1 F * A) :
    A * single (Fin.last m) 0 1 = single (Fin.last m) 0 1 * A := by
  rw [ggInvMatrix_one m hm, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]
    at hA
  exact add_left_cancel hA

theorem col_last_of_commute (hm : 1 ≤ m) {A : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hA : A * ggInvMatrix (m + 1) 1 F = ggInvMatrix (m + 1) 1 F * A) (a : Fin (m + 1)) :
    A a (Fin.last m) = if a = Fin.last m then A 0 0 else 0 := by
  have h := congrFun (congrFun (commute_single_of_commute hm hA) a) 0
  rw [mul_single_apply_same, mul_one] at h
  by_cases ha : a = Fin.last m
  · rw [ite_eq_left ha, h, ha, single_mul_apply_same, one_mul]
  · rw [ite_eq_right ha, h, single_mul_apply_of_ne _ _ _ _ _ ha]

theorem row_zero_of_commute (hm : 1 ≤ m) {A : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hA : A * ggInvMatrix (m + 1) 1 F = ggInvMatrix (m + 1) 1 F * A) (b : Fin (m + 1)) :
    A 0 b = if b = 0 then A (Fin.last m) (Fin.last m) else 0 := by
  have h := congrFun (congrFun (commute_single_of_commute hm hA) (Fin.last m)) b
  rw [single_mul_apply_same, one_mul] at h
  by_cases hb : b = 0
  · rw [ite_eq_left hb, ← h, hb, mul_single_apply_same, mul_one]
  · rw [ite_eq_right hb, ← h, mul_single_apply_of_ne _ _ _ _ _ hb]

theorem corner_eq_of_commute (hm : 1 ≤ m) {A : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hA : A * ggInvMatrix (m + 1) 1 F = ggInvMatrix (m + 1) 1 F * A) :
    A (Fin.last m) (Fin.last m) = A 0 0 := by
  rw [col_last_of_commute hm hA, ite_eq_left rfl]

theorem mul_corner_of_commute (hm : 1 ≤ m) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
    {B : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hB : B * ggInvMatrix (m + 1) 1 F = ggInvMatrix (m + 1) 1 F * B) :
    (A * B) (Fin.last m) (Fin.last m) = A (Fin.last m) (Fin.last m) * B (Fin.last m) (Fin.last m) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last m)]
  · intro k _ hk
    rw [col_last_of_commute hm hB, ite_eq_right hk, mul_zero]
  · simp

variable (m F) in
@[expose] def ggT0GL : GL (Fin (m + 1)) F :=
  Matrix.SpecialLinearGroup.toGL (ggInvSL (m + 1) 1 F)

theorem coe_ggT0GL : ((ggT0GL m F : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
    ggInvMatrix (m + 1) 1 F :=
  rfl

theorem commute_of_mem_centralizer {A : GL (Fin (m + 1)) F}
    (hA : A ∈ Subgroup.centralizer {ggT0GL m F}) :
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * ggInvMatrix (m + 1) 1 F =
      ggInvMatrix (m + 1) 1 F * (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hA
  have h := congrArg (fun X : GL (Fin (m + 1)) F => (X : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) hA
  simp only [Units.val_mul, coe_ggT0GL] at h
  exact h

theorem corner_mul_corner_inv (hm : 1 ≤ m) (A : Subgroup.centralizer {ggT0GL m F}) :
    ((A : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) (Fin.last m) (Fin.last m) *
      (((A⁻¹ : Subgroup.centralizer {ggT0GL m F}) : GL (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) (Fin.last m) (Fin.last m) = 1 := by
  rw [← mul_corner_of_commute hm _ (commute_of_mem_centralizer (A⁻¹).2), ← Units.val_mul,
    ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one, one_apply_eq]

variable (F) in
@[expose] noncomputable def ggCentLambda (hm : 1 ≤ m) :
    Subgroup.centralizer {ggT0GL m F} →* Fˣ where
  toFun A :=
    ⟨((A : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) (Fin.last m) (Fin.last m),
      (((A⁻¹ : Subgroup.centralizer {ggT0GL m F}) : GL (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) (Fin.last m) (Fin.last m),
      corner_mul_corner_inv hm A, by rw [mul_comm]; exact corner_mul_corner_inv hm A⟩
  map_one' := by
    ext
    simp
  map_mul' A B := by
    ext
    simp only [Subgroup.coe_mul, Units.val_mul]
    exact mul_corner_of_commute hm _ (commute_of_mem_centralizer B.2)

theorem coe_ggCentLambda (hm : 1 ≤ m) (A : Subgroup.centralizer {ggT0GL m F}) :
    ((ggCentLambda F hm A : Fˣ) : F) =
      ((A : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) (Fin.last m) (Fin.last m) :=
  rfl

variable (F) in
@[expose] noncomputable def ggCentChar (hm : 1 ≤ m) :
    Subgroup.centralizer {ggT0GL m F} →* Fˣ :=
  (Matrix.GeneralLinearGroup.det.comp (Subgroup.centralizer {ggT0GL m F}).subtype) *
    (ggCentLambda F hm)⁻¹ ^ (m + 1)

theorem det_eq_of_ggCentChar_eq_one (hm : 1 ≤ m) {A : Subgroup.centralizer {ggT0GL m F}}
    (h : ggCentChar F hm A = 1) :
    ((A : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F).det =
      ((ggCentLambda F hm A : Fˣ) : F) ^ (m + 1) := by
  have h' : Matrix.GeneralLinearGroup.det (A : GL (Fin (m + 1)) F) =
      ggCentLambda F hm A ^ (m + 1) := by
    simp only [ggCentChar, MonoidHom.mul_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
      MonoidHom.pow_apply, MonoidHom.inv_apply, inv_pow] at h
    exact mul_inv_eq_one.mp h
  have h'' := congrArg Units.val h'
  rwa [Units.val_pow_eq_pow_val] at h''

theorem conjSL_one (u : SpecialLinearGroup (Fin (m + 1)) F) : InnerDiagA.conjSL 1 u = u := by
  apply Subtype.ext
  rw [InnerDiagA.coe_conjSL]
  simp

theorem conjSL_mul (A B : GL (Fin (m + 1)) F) (u : SpecialLinearGroup (Fin (m + 1)) F) :
    InnerDiagA.conjSL (A * B) u = InnerDiagA.conjSL A (InnerDiagA.conjSL B u) := by
  apply Subtype.ext
  rw [InnerDiagA.coe_conjSL, InnerDiagA.coe_conjSL, InnerDiagA.coe_conjSL, _root_.mul_inv_rev,
    Units.val_mul, Units.val_mul]
  simp only [Matrix.mul_assoc]

section Induced

variable {G : Type*} [Group G]

@[expose] def ggInducedPairs (ψ : SpecialLinearGroup (Fin (m + 1)) F →* G) :
    Subgroup (G × GL (Fin (m + 1)) F) where
  carrier := {p | ∀ u, p.1 * ψ u * p.1⁻¹ = ψ (InnerDiagA.conjSL p.2 u)}
  one_mem' := fun u => by simp [conjSL_one]
  mul_mem' := by
    intro a b ha hb u
    show a.1 * b.1 * ψ u * (a.1 * b.1)⁻¹ = ψ (InnerDiagA.conjSL (a.2 * b.2) u)
    rw [conjSL_mul, ← ha, ← hb]
    group
  inv_mem' := by
    intro a ha u
    show a.1⁻¹ * ψ u * a.1⁻¹⁻¹ = ψ (InnerDiagA.conjSL a.2⁻¹ u)
    have h := ha (InnerDiagA.conjSL a.2⁻¹ u)
    rw [← conjSL_mul, mul_inv_cancel, conjSL_one] at h
    rw [← h]
    group

theorem mem_ggInducedPairs {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G} {y : G}
    {A : GL (Fin (m + 1)) F} :
    (y, A) ∈ ggInducedPairs ψ ↔ ∀ u, y * ψ u * y⁻¹ = ψ (InnerDiagA.conjSL A u) :=
  Iff.rfl

theorem mem_centralizer_of_mem_ggInducedPairs [CharP F 2] (hm : 1 ≤ m)
    {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) {y : G}
    {A : GL (Fin (m + 1)) F} (h : (y, A) ∈ ggInducedPairs ψ)
    (hy : y ∈ Subgroup.centralizer {ψ (ggInvSL (m + 1) 1 F)}) :
    A ∈ Subgroup.centralizer {ggT0GL m F} := by
  set T := ggInvSL (m + 1) 1 F with hTdef
  have hT : T * T = 1 := ggInvSL_mul_self (by omega)
  have hTinv : T⁻¹ = T := (eq_inv_of_mul_eq_one_left hT).symm
  rw [Subgroup.mem_centralizer_singleton_iff] at hy
  have h1 : ψ (InnerDiagA.conjSL A T) = ψ T := by
    rw [← mem_ggInducedPairs.mp h T, hy, mul_inv_cancel_right]
  set c := InnerDiagA.conjSL A T with hc
  set z := c * T⁻¹ with hz
  have hzc : z ∈ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F) :=
    hker (by rw [MonoidHom.mem_ker, map_mul, h1, map_inv, mul_inv_cancel])
  have hc2 : c * c = 1 := by rw [hc, ← map_mul, hT, map_one]
  have hcz : c = z * T := by rw [hz, inv_mul_cancel_right]
  have hz2 : z ^ 2 = 1 := by
    have hzT : T * z = z * T := Subgroup.mem_center_iff.mp hzc T
    calc z ^ 2 = z * z * (T * T) := by rw [hT, mul_one, pow_two]
      _ = z * (T * z) * T := by rw [hzT]; group
      _ = c * c := by rw [hcz]; group
      _ = 1 := hc2
  have hz1 : z = 1 := eq_one_of_mem_center_of_sq_eq_one hzc hz2
  have hcT : c = T := by rw [hcz, hz1, one_mul]
  have hmat := congrArg (fun X : SpecialLinearGroup (Fin (m + 1)) F =>
    (X : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) hcT
  simp only [hc, InnerDiagA.coe_conjSL] at hmat
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  change (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * (T : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
    (T : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
  conv_rhs => rw [← hmat]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.mul_one]

theorem ggOTwoPrime_mono {H K : Subgroup G} (h : H ≤ K) : ggOTwoPrime H ≤ ggOTwoPrime K :=
  Subgroup.closure_mono fun _ hy => ⟨h hy.1, hy.2⟩

theorem map_ggOTwoPrime_le {U : Type*} [Group U] (ψ : U →* G) (H : Subgroup U) :
    (ggOTwoPrime H).map ψ ≤ ggOTwoPrime (H.map ψ) := by
  rw [ggOTwoPrime, MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨y, ⟨hyH, k, hk⟩, rfl⟩
  exact ⟨⟨y, hyH, rfl⟩, k, by rw [← map_pow, hk, map_one]⟩

theorem conjSL_eq_of_smul {A : GL (Fin (m + 1)) F} {c : Fˣ}
    {B : SpecialLinearGroup (Fin (m + 1)) F}
    (hB : (B : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = (c : F) • (A : Matrix _ _ F))
    (u : SpecialLinearGroup (Fin (m + 1)) F) : InnerDiagA.conjSL A u = B * u * B⁻¹ := by
  apply Subtype.ext
  rw [InnerDiagA.coe_conjSL, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, InvPlacement.coe_inv_eq_inv, hB]
  generalize (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = X
  have hinv : ((c : F) • (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F))⁻¹ =
      ((c⁻¹ : Fˣ) : F) • ((A⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, one_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [hinv, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Units.val_mul,
    mul_inv_cancel, Units.val_one, one_smul]

theorem mem_ggOTwoPrime_of_ggCentChar_eq_one [CharP F 2] (hm : 1 ≤ m)
    {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {z : G} {A : GL (Fin (m + 1)) F}
    (hzA : (z, A) ∈ ggInducedPairs ψ) (hA : A ∈ Subgroup.centralizer {ggT0GL m F})
    (hχ : ggCentChar F hm ⟨A, hA⟩ = 1) :
    z ∈ ggOTwoPrime (ψ.range ⊓ Subgroup.centralizer {ψ (ggInvSL (m + 1) 1 F)}) := by
  set l := ggCentLambda F hm ⟨A, hA⟩ with hl
  have hdet := det_eq_of_ggCentChar_eq_one hm hχ
  set M : Matrix (Fin (m + 1)) (Fin (m + 1)) F := ((l⁻¹ : Fˣ) : F) • (A : Matrix _ _ F) with hM
  have hMdet : M.det = 1 := by
    rw [hM, det_smul, Fintype.card_fin]
    change ((l⁻¹ : Fˣ) : F) ^ (m + 1) * (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F).det = 1
    rw [hdet, ← mul_pow, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_pow]
  set B : SpecialLinearGroup (Fin (m + 1)) F := ⟨M, hMdet⟩ with hB
  have hAc := commute_of_mem_centralizer hA
  have hBc : B ∈ Subgroup.centralizer {ggInvSL (m + 1) 1 F} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    change M * ggInvMatrix (m + 1) 1 F = ggInvMatrix (m + 1) 1 F * M
    rw [hM, Matrix.smul_mul, Matrix.mul_smul, hAc]
  have hB1 : (B : Matrix (Fin (m + 1)) (Fin (m + 1)) F) (Fin.last m) (Fin.last m) = 1 := by
    change (((l⁻¹ : Fˣ) : F) • (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) (Fin.last m)
      (Fin.last m) = 1
    rw [Matrix.smul_apply, smul_eq_mul, ← coe_ggCentLambda hm ⟨A, hA⟩, ← hl, ← Units.val_mul,
      inv_mul_cancel, Units.val_one]
  have hBO := mem_ggOTwoPrime_centralizer_of_corner hm hBc hB1
  have hconj : ∀ u, InnerDiagA.conjSL A u = B * u * B⁻¹ := by
    intro u
    exact conjSL_eq_of_smul (c := l⁻¹) rfl u
  have hz : z = ψ B := by
    have hw : (ψ B)⁻¹ * z ∈ Subgroup.centralizer (ψ.range : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨u, rfl⟩
      have h := mem_ggInducedPairs.mp hzA u
      rw [hconj, map_mul, map_mul, map_inv] at h
      calc ψ u * ((ψ B)⁻¹ * z) = (ψ B)⁻¹ * (ψ B * ψ u * (ψ B)⁻¹) * z := by group
        _ = (ψ B)⁻¹ * (z * ψ u * z⁻¹) * z := by rw [h]
        _ = (ψ B)⁻¹ * z * ψ u := by group
    rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hw
    exact hw.symm
  rw [hz]
  refine ggOTwoPrime_mono ?_ (map_ggOTwoPrime_le ψ _ (Subgroup.mem_map_of_mem ψ hBO))
  intro x hx
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hx
  refine ⟨⟨v, rfl⟩, ?_⟩
  have hv' := Subgroup.mem_centralizer_singleton_iff.mp hv
  exact Subgroup.mem_centralizer_singleton_iff.mpr (by rw [← map_mul, hv', map_mul])

theorem exists_zpowers_sup_ggOTwoPrime_sl [Finite F] [CharP F 2] (hm : 1 ≤ m)
    (ψ : SpecialLinearGroup (Fin (m + 1)) F →* G)
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) (Y : Subgroup G)
    (hYr : Y ≤ Subgroup.centralizer {ψ (ggInvSL (m + 1) 1 F)})
    (hY : ∀ y ∈ Y, ∃ A : GL (Fin (m + 1)) F, (y, A) ∈ ggInducedPairs ψ) :
    ∃ y₀ ∈ Y, Y ≤ Subgroup.zpowers y₀ ⊔
      ggOTwoPrime (ψ.range ⊓ Subgroup.centralizer {ψ (ggInvSL (m + 1) 1 F)}) := by
  set SY : Subgroup (G × GL (Fin (m + 1)) F) := ggInducedPairs ψ ⊓ Y.prod ⊤ with hSY
  have hmem : ∀ p : SY, (p : G × GL (Fin (m + 1)) F).2 ∈ Subgroup.centralizer {ggT0GL m F} :=
    fun p => mem_centralizer_of_mem_ggInducedPairs hm hker p.2.1 (hYr p.2.2.1)
  let π : SY →* Subgroup.centralizer {ggT0GL m F} :=
    MonoidHom.codRestrict ((MonoidHom.snd G (GL (Fin (m + 1)) F)).comp SY.subtype) _ hmem
  let φ : SY →* Fˣ := (ggCentChar F hm).comp π
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := φ.range)
  obtain ⟨p₀, hp₀⟩ := g.2
  refine ⟨(p₀ : G × GL (Fin (m + 1)) F).1, p₀.2.2.1, fun y hy => ?_⟩
  obtain ⟨A, hA⟩ := hY y hy
  let p : SY := ⟨(y, A), hA, hy, Subgroup.mem_top A⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨φ p, p, rfl⟩)
  have hk' : φ (p₀ ^ k) = φ p := by
    rw [map_zpow, hp₀]
    exact congrArg Subtype.val hk
  set q : SY := p * (p₀ ^ k)⁻¹ with hq
  have hφq : φ q = 1 := by rw [hq, map_mul, map_inv, hk', mul_inv_cancel]
  have hzq := mem_ggOTwoPrime_of_ggCentChar_eq_one hm hC q.2.1 (hmem q) hφq
  have hpow : ((p₀ ^ k : SY) : G × GL (Fin (m + 1)) F).1 = (p₀ : G × GL (Fin (m + 1)) F).1 ^ k := by
    rw [Subgroup.coe_zpow]
    exact map_zpow (MonoidHom.fst G (GL (Fin (m + 1)) F)) _ k
  have hy' : y = (q : G × GL (Fin (m + 1)) F).1 * ((p₀ : G × GL (Fin (m + 1)) F).1) ^ k := by
    rw [hq, Subgroup.coe_mul, Subgroup.coe_inv, Prod.fst_mul, Prod.fst_inv, hpow,
      inv_mul_cancel_right]
  rw [hy']
  exact mul_mem (Subgroup.mem_sup_right hzq)
    (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers _ k))

end Induced

end LinFusion

end CFSG.StandardType
