module

public import CFSG.Quasithin.Vol2.Ch11SecB414MC
public import CFSG.Quasithin.Vol2.Ch11SecB414MA
public import CFSG.Quasithin.Vol2.Ch11SecS12T

public section

namespace CFSG.Quasithin.H13.Ch4.B414.M

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LieType.SteinbergBR.BlockPar
open CFSG.Assembly.LowTwoRank (StatedSL)
open Matrix
open scoped MatrixGroups

variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
theorem pow_three_eq_one (hF : Nat.card F = 4) {x : F} (hx : x ≠ 0) : x ^ 3 = 1 := by
  have h3 : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
  have := pow_card_eq_one' (G := Fˣ) (x := Units.mk0 x hx)
  rw [h3] at this
  simpa using congrArg Units.val this

omit [Finite F] [CharP F 2] in
theorem mem_normalizer_of_mem_Ptheta {y : PGL3 F} (hy : y ∈ Ptheta F 0) :
    y ∈ Subgroup.normalizer ((pCoreOf 2 (Ptheta F 0) : Subgroup (PGL3 F)) : Set (PGL3 F)) :=
  CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ (Subgroup.le_normalizer hy)

omit [Finite F] [CharP F 2] in
theorem det_eq_one_of_mem_range (hF : Nat.card F = 4) {g : GL (Fin 3) F}
    (hg : ProjGenLinGroup.mk g ∈ (thetaP F).range) : (g : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  obtain ⟨x, hx⟩ := hg
  obtain ⟨A, rfl⟩ := proj_surjective 3 F x
  rw [thetaP_proj, ProjGenLinGroup.mk_eq_mk_iff] at hx
  obtain ⟨c, hc⟩ := hx
  have e := congrArg (fun B : GL (Fin 3) F => (B : Matrix (Fin 3) (Fin 3) F).det) hc
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.det_mul, A.prop, one_mul, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] at e
  rw [← e]
  exact pow_three_eq_one hF c.ne_zero

theorem det_rhoMatG (hF : Nat.card F = 4) {g : GL (Fin 3) F}
    (hg : ProjGenLinGroup.mk g ∈ Ptheta F 0) : (rhoMatG g).det = 1 := by
  have hgn := mem_normalizer_of_mem_Ptheta hg
  have hgi : ProjGenLinGroup.mk g⁻¹ ∈ Ptheta F 0 := by rw [map_inv]; exact (Ptheta F 0).inv_mem hg
  obtain ⟨h10, h20⟩ :=
    CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12.entries_of_normalizer_zero hF hgn
  obtain ⟨i10, i20⟩ := CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12.entries_of_normalizer_zero hF
    (mem_normalizer_of_mem_Ptheta hgi)
  have hdet := det_eq_one_of_mem_range hF (Subgroup.map_le_range (thetaP F) (parab34 F 0) hg)
  have hdeti : ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 :=
    det_eq_one_of_mem_range hF (Subgroup.map_le_range (thetaP F) (parab34 F 0) hgi)
  have h00 : (g : Matrix (Fin 3) (Fin 3) F) 0 0 *
      ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0 = 1 := by
    have := congrFun (congrFun (coe_mul_inv_GL g) 0) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply_eq] at this
    rw [i10, i20, mul_zero, mul_zero, add_zero, add_zero] at this
    exact this
  have hg00 : (g : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one h00
  rw [Matrix.det_fin_three, i10, i20] at hdeti
  rw [Matrix.det_fin_two]
  simp only [rhoMatG, Matrix.of_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  have h3 := pow_three_eq_one hF hg00
  set a := (g : Matrix (Fin 3) (Fin 3) F) 0 0
  set X := ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 1 *
      ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 -
    ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 2 *
      ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 1
  linear_combination (-(a ^ 2 * X)) * h00 + a ^ 3 * hdeti + h3

omit [Finite F] [CharP F 2] in
theorem coe_inv3 (A : SpecialLinearGroup (Fin 3) F) :
    ((A⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.adjugate (A : Matrix (Fin 3) (Fin 3) F) := rfl

@[expose] noncomputable def rhoRef (hF : Nat.card F = 4) :
    ↥(Ptheta F 0) →* SpecialLinearGroup (Fin 2) F where
  toFun p := ⟨rhoMatG (repP (p : PGL3 F)), det_rhoMatG hF (by rw [mk_repP]; exact p.2)⟩
  map_one' := by
    apply Subtype.ext
    show rhoMatG (repP ((1 : ↥(Ptheta F 0)) : PGL3 F)) = 1
    rw [rhoMatG_eq_of_mk_eq (g' := 1) (by rw [mk_repP, map_one]; rfl), rhoMatG_one]
  map_mul' p q := by
    apply Subtype.ext
    show rhoMatG (repP ((p * q : ↥(Ptheta F 0)) : PGL3 F)) =
      rhoMatG (repP (p : PGL3 F)) * rhoMatG (repP (q : PGL3 F))
    rw [rhoMatG_eq_of_mk_eq (g' := repP (p : PGL3 F) * repP (q : PGL3 F))
      (by rw [mk_repP, map_mul, mk_repP, mk_repP]; rfl)]
    exact rhoMatG_mul hF (by rw [mk_repP]; exact mem_normalizer_of_mem_Ptheta p.2)
      (by rw [mk_repP]; exact mem_normalizer_of_mem_Ptheta q.2)

theorem rhoRef_eq (hF : Nat.card F = 4) (p : ↥(Ptheta F 0)) {g : GL (Fin 3) F}
    (hg : ProjGenLinGroup.mk g = p) :
    ((rhoRef hF p : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = rhoMatG g :=
  rhoMatG_eq_of_mk_eq (by rw [mk_repP, hg])

theorem betaRef_conj (hF : Nat.card F = 4) (p : ↥(Ptheta F 0))
    (u u' : ↥(pCoreOf 2 (Ptheta F 0))) (h : (u' : PGL3 F) = p * u * (p : PGL3 F)⁻¹) :
    Multiplicative.toAdd (betaRef hF u') =
      ((rhoRef hF p : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ
        Multiplicative.toAdd (betaRef hF u) := by
  have hc := conj_iota0 hF (g := repP (p : PGL3 F))
    (by rw [mk_repP]; exact mem_normalizer_of_mem_Ptheta p.2) (betaRef hF u)
  rw [mk_repP, iota0_betaRef, ← h] at hc
  have e : betaRef hF u' = Multiplicative.ofAdd (rhoMatG (repP (p : PGL3 F)) *ᵥ
      Multiplicative.toAdd (betaRef hF u)) := by
    apply iota0_injective
    rw [iota0_betaRef]
    exact hc
  rw [e, toAdd_ofAdd]
  rfl

theorem rhoRef_surjective (hF : Nat.card F = 4) : Function.Surjective (rhoRef hF) := by
  intro B
  have hB : (B : Matrix (Fin 2) (Fin 2) F).det = 1 := B.prop
  rw [Matrix.det_fin_two] at hB
  let C : Matrix (Fin 3) (Fin 3) F :=
    !![1, 0, 0; 0, (B : Matrix (Fin 2) (Fin 2) F) 1 1, -(B : Matrix (Fin 2) (Fin 2) F) 1 0;
      0, -(B : Matrix (Fin 2) (Fin 2) F) 0 1, (B : Matrix (Fin 2) (Fin 2) F) 0 0]
  have hC : C.det = 1 := by
    simp only [C, Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.head_cons, Matrix.head_fin_const, Matrix.tail_cons]
    linear_combination hB
  let A : SpecialLinearGroup (Fin 3) F := ⟨C, hC⟩
  have hA : A ∈ stabilizer (flagSpace 3 F 1) := by
    refine mem_stabilizer_of_map_le ?_
    rintro _ ⟨w, hw, rfl⟩
    have hw' : w ∈ flagSpace 3 F 1 := hw
    rw [mem_flagSpace] at hw' ⊢
    have h1 := hw' 1 (by simp)
    have h2 := hw' 2 (by simp)
    intro j hj
    fin_cases j
    · simp at hj
    all_goals simp [A, C, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h1, h2]
  refine ⟨⟨_, CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12.mk_mem_Ptheta (j := 0) hA⟩, ?_⟩
  apply Subtype.ext
  rw [rhoRef_eq hF _ rfl]
  ext i k
  simp only [rhoMatG, Matrix.of_apply, ← map_inv, SpecialLinearGroup.coe_GL_coe_matrix]
  rw [coe_inv3]
  simp only [Matrix.adjugate_fin_three]
  fin_cases i <;> fin_cases k <;>
  · simp [A, C]
    try linear_combination hB

theorem card_pCoreOf_Ptheta (hF : Nat.card F = 4) :
    Nat.card ↥(pCoreOf 2 (Ptheta F 0)) = 16 := by
  rw [Nat.card_congr (betaRef hF).toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
    hF, Nat.card_fin]
  norm_num

theorem card_Ptheta_zero (hF : Nat.card F = 4) : Nat.card ↥(Ptheta F 0) = 960 := by
  rw [Subgroup.card_map_of_injective thetaP_injective, ← dInf_parab34 hF 0]
  exact (parab34_structure hF 0).1

theorem rhoRef_ker (hF : Nat.card F = 4) :
    (rhoRef hF).ker = (pCoreOf 2 (Ptheta F 0)).subgroupOf (Ptheta F 0) := by
  have hU : pCoreOf 2 (Ptheta F 0) ≤ Ptheta F 0 := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hle : (pCoreOf 2 (Ptheta F 0)).subgroupOf (Ptheta F 0) ≤ (rhoRef hF).ker := by
    intro p hp
    rw [Subgroup.mem_subgroupOf] at hp
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    show ((rhoRef hF p : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1
    refine matrix_ext_mulVec fun v => ?_
    have hv : iota0 (Multiplicative.ofAdd v) ∈ pCoreOf 2 (Ptheta F 0) := by
      rw [← range_iota0 hF]
      exact ⟨_, rfl⟩
    have hcomm : (iota0 (Multiplicative.ofAdd v) : PGL3 F) =
        p * iota0 (Multiplicative.ofAdd v) * (p : PGL3 F)⁻¹ := by
      rw [← range_iota0 hF] at hp
      obtain ⟨w, hw⟩ := hp
      rw [← hw, ← map_inv, ← map_mul, ← map_mul, mul_comm w, mul_assoc, mul_inv_cancel, mul_one]
    have hc := betaRef_conj hF p ⟨_, hv⟩ ⟨_, hv⟩ hcomm
    rw [betaRef_iota0, toAdd_ofAdd] at hc
    rw [Matrix.one_mulVec]
    exact hc.symm
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  have h1 := Subgroup.card_ker_mul_card_range (rhoRef hF)
  rw [MonoidHom.range_eq_top_of_surjective _ (rhoRef_surjective hF), Subgroup.card_top,
    CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A.card_SL2_four hF, card_Ptheta_zero hF] at h1
  have h2 : Nat.card ↥((pCoreOf 2 (Ptheta F 0)).subgroupOf (Ptheta F 0)) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU).toEquiv, card_pCoreOf_Ptheta hF]
  omega

theorem exists_intertwine_levi (hF : Nat.card F = 4)
    (α₀' : ↥(Ptheta F 0) →* ↥(StatedSL 2 F)) (hs : Function.Surjective α₀')
    (hk : α₀'.ker = (pCoreOf 2 (Ptheta F 0)).subgroupOf (Ptheta F 0)) :
    ∃ T : (Fin 2 → F) ≃+ (Fin 2 → F), ∀ (p : ↥(Ptheta F 0)) (v : Fin 2 → F),
      T (((rhoRef hF p : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v) =
        (((α₀' p : StatedSL 2 F) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ T v := by
  let e := (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm
  let α'' : ↥(Ptheta F 0) →* SpecialLinearGroup (Fin 2) F := e.toMonoidHom.comp α₀'
  have hs'' : Function.Surjective α'' := e.surjective.comp hs
  have hk'' : (rhoRef hF).ker = α''.ker := by
    rw [rhoRef_ker, ← hk]
    ext p
    simp only [α'', MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact e.map_eq_one_iff.symm
  obtain ⟨φ, hφ⟩ := CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12.exists_mulEquiv_of_ker_eq
    (rhoRef hF) α'' (rhoRef_surjective hF) hs'' hk''
  obtain ⟨T, hT⟩ := exists_addEquiv_intertwine hF φ
  refine ⟨T, fun p v => ?_⟩
  rw [hT, ← hφ]
  congr 1
  have := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe 2 F (e (α₀' p))
  rw [MulEquiv.apply_symm_apply] at this
  exact this.symm

end CFSG.Quasithin.H13.Ch4.B414.M
