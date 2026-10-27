module

public import CFSG.Quasithin.Background.SimsF5Defs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofKleinSixB
public import CFSG.Quasithin.H13.ModelsLinear

public section

namespace CFSG.Quasithin.SimsF5

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

noncomputable section

open scoped Matrix
open CFSG.Open CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatLeafProof.KleinSix
  (rhoGL rhoGL_apply transv range_eq_elementaryGroup coordsOf coordsOf_skewOf skewOf)
open CFSG.LocalAnalysis (antiMat)
open CFSG.RankThree.PartOne.KCOrthogonalDescent (linConj map_orthogonalGroup subgroupEquivOfMap)

@[expose] def kleinE : Fin 3 → V6 :=
  ![![0, 0, 0, 0, 1, 1], ![0, 1, 1, 1, 0, 0], ![1, 0, 1, 2, 0, 0]]

@[expose] def kleinF : Fin 3 → V6 :=
  ![![0, 0, 0, 0, 1, 2], ![0, 1, 2, 2, 0, 0], ![1, 0, 2, 1, 0, 0]]

@[expose] def kleinMat : Matrix (Fin 6) (Fin 3 ⊕ Fin 3) (ZMod 3) :=
  Matrix.of fun k x => Sum.elim (fun i => kleinE i k) (fun i => kleinF i k) x

@[expose] def kleinInvMat : Matrix (Fin 3 ⊕ Fin 3) (Fin 6) (ZMod 3) :=
  Matrix.of fun x k => Sum.elim (fun i => -(if k = 5 then -1 else 1) * kleinF i k)
    (fun i => -(if k = 5 then -1 else 1) * kleinE i k) x

theorem kleinMat_mul_kleinInvMat : kleinMat * kleinInvMat = 1 := by
  decide

theorem kleinInvMat_mul_kleinMat : kleinInvMat * kleinMat = 1 := by
  decide

@[expose] def kleinEquiv : (Fin 3 ⊕ Fin 3 → ZMod 3) ≃ₗ[ZMod 3] (Fin 6 → ZMod 3) :=
  LinearEquiv.ofLinear (Matrix.toLin' kleinMat) (Matrix.toLin' kleinInvMat)
    (by rw [← Matrix.toLin'_mul, kleinMat_mul_kleinInvMat, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, kleinInvMat_mul_kleinMat, Matrix.toLin'_one])

theorem kleinEquiv_eq_mulVec (w : Fin 3 ⊕ Fin 3 → ZMod 3) : kleinEquiv w = kleinMat.mulVec w :=
  rfl

theorem kleinEquiv_apply (w : Fin 3 ⊕ Fin 3 → ZMod 3) :
    kleinEquiv w = ![w (.inl 2) + w (.inr 2), w (.inl 1) + w (.inr 1),
      w (.inl 1) + 2 * w (.inr 1) + w (.inl 2) + 2 * w (.inr 2),
      w (.inl 1) + 2 * w (.inl 2) + (2 * w (.inr 1) + w (.inr 2)),
      w (.inl 0) + w (.inr 0), w (.inl 0) + 2 * w (.inr 0)] := by
  funext k
  fin_cases k <;> simp [kleinEquiv_eq_mulVec, kleinMat, kleinE, kleinF, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Fin.sum_univ_three] <;> ring

theorem qV_kleinEquiv (w : Fin 3 ⊕ Fin 3 → ZMod 3) :
    qV (kleinEquiv w) = ∑ i : Fin 3, w (.inl i) * w (.inr i) := by
  rw [kleinEquiv_apply, Fin.sum_univ_three]
  simp only [qV, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  generalize w (.inl 0) = a0
  generalize w (.inl 1) = a1
  generalize w (.inl 2) = a2
  generalize w (.inr 0) = b0
  generalize w (.inr 1) = b1
  generalize w (.inr 2) = b2
  revert a0 a1 a2 b0 b1 b2
  decide

@[expose] def kleinForm : QuadraticForm (ZMod 3) V6 :=
  (quadPlus 3 (ZMod 3)).comp kleinEquiv.symm.toLinearMap

theorem kleinForm_kleinEquiv (w : Fin 3 ⊕ Fin 3 → ZMod 3) :
    kleinForm (kleinEquiv w) = quadPlus 3 (ZMod 3) w := by
  change quadPlus 3 (ZMod 3) (kleinEquiv.symm (kleinEquiv w)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem coe_kleinForm : ⇑kleinForm = qV := by
  funext v
  obtain ⟨w, rfl⟩ := kleinEquiv.surjective v
  rw [kleinForm_kleinEquiv, quadPlus_apply, qV_kleinEquiv]

theorem orthogonalGroup_kleinForm :
    (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 (ZMod 3))).map
        (linConj kleinEquiv).toMonoidHom = TauCeti.QuadraticMap.orthogonalGroup kleinForm :=
  map_orthogonalGroup kleinEquiv 1 fun w => by rw [kleinForm_kleinEquiv, Units.val_one, one_mul]

theorem commutator_orthogonalGroup_kleinForm :
    ⁅TauCeti.QuadraticMap.orthogonalGroup kleinForm,
        TauCeti.QuadraticMap.orthogonalGroup kleinForm⁆ =
      (rhoGL (K := ZMod 3)).range.map (linConj kleinEquiv).toMonoidHom := by
  rw [← orthogonalGroup_kleinForm, ← Subgroup.map_commutator,
    commutator_orthogonalGroup_quadPlus (by norm_num),
    ← range_eq_elementaryGroup (by decide)]

@[expose] def statedOmegaEquivCommutator {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀) :
    StatedOmega Q₀ ≃*
      ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
  ((toLinEquiv ι K).subgroupMap (StatedOmega Q₀)).trans (MulEquiv.subgroupCongr (by
    rw [statedOmega_eq_comap hQ]
    exact Subgroup.map_comap_eq_self_of_surjective (toLinEquiv ι K).surjective _))

@[expose] def mdotEquivRange : ↥MDot ≃* (rhoGL (K := ZMod 3)).range :=
  (statedOmegaEquivCommutator coe_kleinForm).trans
    (subgroupEquivOfMap (linConj kleinEquiv) commutator_orthogonalGroup_kleinForm.symm).symm

theorem quasisimple_SL_four_three :
    CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 4) (ZMod 3)) :=
  CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 4 (ZMod 3)
    (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num))

theorem isSimpleGroup_PSL_four_three :
    IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 3)) :=
  quasisimple_SL_four_three.2.1

theorem rhoGL_transv_ne_one : rhoGL (K := ZMod 3) (transv 0 1 (by decide) 1) ≠ 1 := by
  intro h
  have h1 := LinearEquiv.congr_fun h (Pi.single (.inr 2) 1)
  rw [rhoGL_apply] at h1
  have h2 := congrFun h1 (.inl 1)
  simp [transv, coordsOf, skewOf, antiMat, Matrix.transvection, Matrix.mul_apply,
    Fin.sum_univ_four] at h2

theorem center_le_ker_rhoGL :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) (ZMod 3)) ≤ (rhoGL (K := ZMod 3)).ker := by
  intro z hz
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hz
  obtain ⟨r, hr, hrz⟩ := hz
  have key : ∀ r : ZMod 3, r ^ 4 = 1 → r * r = 1 := by decide
  have hr2 : r * r = 1 := key r (by simpa using hr)
  rw [MonoidHom.mem_ker]
  refine LinearEquiv.ext fun v => ?_
  rw [rhoGL_apply, ← hrz]
  have h : Matrix.scalar (Fin 4) r * skewOf v * (Matrix.scalar (Fin 4) r)ᵀ = skewOf v := by
    ext i j
    simp only [Matrix.scalar_apply, Matrix.diagonal_transpose, Matrix.diagonal_mul,
      Matrix.mul_diagonal]
    rw [mul_right_comm, hr2, one_mul]
  rw [h, coordsOf_skewOf]
  rfl

theorem ker_rhoGL_le_center :
    (rhoGL (K := ZMod 3)).ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) (ZMod 3)) := by
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups
    quasisimple_SL_four_three (Subgroup.Normal.isSubnormal (MonoidHom.normal_ker rhoGL)) with h | h
  · exfalso
    refine rhoGL_transv_ne_one ?_
    rw [← MonoidHom.mem_ker, h]
    exact Subgroup.mem_top _
  · exact h

theorem ker_rhoGL :
    (rhoGL (K := ZMod 3)).ker = Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) (ZMod 3)) :=
  le_antisymm ker_rhoGL_le_center center_le_ker_rhoGL

@[expose] def pslEquivRange :
    Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 3) ≃* (rhoGL (K := ZMod 3)).range :=
  (QuotientGroup.quotientMulEquivOfEq ker_rhoGL.symm).trans
    (QuotientGroup.quotientKerEquivRange rhoGL)

@[expose] def mdotEquivPSL : ↥MDot ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 3) :=
  mdotEquivRange.trans pslEquivRange.symm

theorem isL43_MDot : CFSG.ASVolI.ChF.IsL43 ↥MDot :=
  ⟨ZMod 3, inferInstance, inferInstance, Nat.card_zmod 3,
    ⟨mdotEquivPSL.trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 4 (ZMod 3))⟩⟩

theorem card_MDot : Nat.card ↥MDot = 6065280 := by
  rw [Nat.card_congr mdotEquivPSL.toEquiv]
  exact CFSG.Quasithin.H13.card_psl_four_three

theorem isSimpleGroup_MDot : IsSimpleGroup ↥MDot := by
  haveI := isSimpleGroup_PSL_four_three
  exact mdotEquivPSL.isSimpleGroup

theorem center_MDot_eq_bot : Subgroup.center ↥MDot = ⊥ := by
  haveI := isSimpleGroup_MDot
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥MDot) with h | h
  · exact h
  · exfalso
    have hc : ∀ a b : ↥MDot, a * b = b * a := fun a b =>
      (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a
    letI : CommGroup ↥MDot := { (inferInstance : Group ↥MDot) with mul_comm := hc }
    have := IsSimpleGroup.prime_card (α := ↥MDot)
    rw [card_MDot] at this
    norm_num at this

end

end CFSG.Quasithin.SimsF5
