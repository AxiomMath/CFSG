module

public import CFSG.Quasithin.Background.GoldschmidtG22M12IdentLinear
public import CFSG.RankThree.PartTwo.KFacts.AutPSUFaithful
public import CFSG.RankThree.PartTwo.KFacts.AutKindsCentral
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15422Cat
import CFSG.RankThree.PartTwo.KFacts.AutPSUScalar
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Milestones.CL_LIT_SQTK_simple_list
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.F6CatDickson
public import CFSG.Quasithin.Background.F6CatRecogSetting
public import CFSG.Quasithin.Background.GoldschmidtG22M12IdentBasic
public import CFSG.Sporadic.J4Base
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import CFSG.Walter.Defs
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate8026Base
public import Certificates.Certificate9

public section

namespace CFSG.Quasithin.F6

namespace G22M12Ident

open CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank Matrix

section Norm

variable {p f : ℕ} {F : Type} [Field F]

@[expose] def normOneUnits (h : UnitaryFieldData p f F) : Subgroup Fˣ where
  carrier := {c | h.norm (c : F) = 1}
  one_mem' := by simp [UnitaryFieldData.norm]
  mul_mem' := by
    intro a b ha hb
    change h.norm ((a * b : Fˣ) : F) = 1
    rw [Units.val_mul, norm_mul_eq h, show h.norm (a : F) = 1 from ha,
      show h.norm (b : F) = 1 from hb, one_mul]
  inv_mem' := by
    intro a ha
    change h.norm ((a⁻¹ : Fˣ) : F) = 1
    rw [Units.val_inv_eq_inv_val, norm_inv_eq h]
    change (h.norm (a : F))⁻¹ = 1
    rw [show h.norm (a : F) = 1 from ha, inv_one]

theorem mem_normOneUnits (h : UnitaryFieldData p f F) {c : Fˣ} :
    c ∈ normOneUnits h ↔ h.norm (c : F) = 1 :=
  Iff.rfl

theorem bar_eq_inv_of_norm (h : UnitaryFieldData p f F) {c : Fˣ} (hc : c ∈ normOneUnits h) :
    h.bar (c : F) = ((c⁻¹ : Fˣ) : F) := by
  rw [Units.val_inv_eq_inv_val]
  have h1 : (c : F) * h.bar (c : F) = 1 := hc
  exact eq_inv_of_mul_eq_one_right h1

theorem det_mem_normOneUnits (h : UnitaryFieldData p f F) {A : GL (Fin 3) F}
    (hA : A ∈ unitaryIsom3 h) : GeneralLinearGroup.det A ∈ normOneUnits h := by
  have h1 := congrArg Matrix.det ((mem_unitaryIsom3 (h := h)).mp hA)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h1
  have h2 : ((A : Matrix (Fin 3) (Fin 3) F).map h.bar).det =
      h.bar (A : Matrix (Fin 3) (Fin 3) F).det := (RingHom.map_det h.bar _).symm
  rw [h2] at h1
  change h.norm ((GeneralLinearGroup.det A : Fˣ) : F) = 1
  rw [GeneralLinearGroup.val_det_apply, UnitaryFieldData.norm, mul_comm]
  exact h1

theorem scalar_mem_unitaryIsom3 (h : UnitaryFieldData p f F) {c : Fˣ} (hc : c ∈ normOneUnits h) :
    GeneralLinearGroup.scalar (Fin 3) c ∈ unitaryIsom3 h :=
  CFSG.RankThree.PartTwo.KFacts.scalar_mem_unitaryIsom3_of_norm (h := h) hc

theorem diagOne_mem_unitaryIsom3 (h : UnitaryFieldData p f F) {δ : Fˣ} (hδ : δ ∈ normOneUnits h) :
    diagOne δ ∈ unitaryIsom3 h := by
  rw [mem_unitaryIsom3, coe_diagOne, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  have h1 : (δ : F) * h.bar (δ : F) = 1 := hδ
  fin_cases i
  · simp only [Fin.zero_eta, Matrix.cons_val_zero]
    rw [mul_comm]
    exact h1
  · simp
  · simp

end Norm

section Aux

variable {p : ℕ} {F : Type} [Field F]

theorem ringEquiv_eq_one_or_bar (h : UnitaryFieldData p 1 F) (σ : F ≃+* F) :
    σ = 1 ∨ ∀ c, σ c = h.bar c := by
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.finite
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = p ^ 2 := by
    rw [← Nat.card_eq_fintype_card, h.card]
  obtain ⟨h2, σ₀, hσ₀, hσ₀x⟩ :=
    CFSG.Quasithin.EmptyFaithfulMultiple.L15422.card_ringEquiv_eq_two hcard
  by_cases hσ : σ = 1
  · exact Or.inl hσ
  · right
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : F ≃+* F)).mp h2
    have h1 : σ = σ₀ := (hy σ hσ).trans (hy σ₀ hσ₀).symm
    intro c
    rw [h1, hσ₀x, h.bar_apply, pow_one]

theorem map_bar_eq_inv_transpose {f : ℕ} (h : UnitaryFieldData p f F)
    (g : ↥(unitarySU p f F 3)) :
    (((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map h.bar) =
      ((((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))⁻¹)ᵀ := by
  have h1 := ((mem_unitarySU_iff h).mp g.2).2
  have h2 : (((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ =
      (((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))⁻¹ := by
    rw [Matrix.inv_eq_left_inv h1]
  rw [← h2, Matrix.transpose_transpose]

end Aux

section Psu

variable {p : ℕ} {F : Type} [Field F]

theorem glAut_inv_diagOne (h : UnitaryFieldData p 1 F) {σ : F ≃+* F} (hσ : ∀ c, σ c = h.bar c)
    {δ : Fˣ} (hδ : δ ∈ normOneUnits h) :
    UnitaryHigher.glAut σ ((diagOne δ : GL (Fin 3) F)⁻¹) = diagOne δ := by
  apply Units.ext
  rw [UnitaryHigher.coe_glAut]
  change (Matrix.diagonal ![((δ⁻¹ : Fˣ) : F), 1, 1]).map σ = Matrix.diagonal ![(δ : F), 1, 1]
  rw [Matrix.diagonal_map (map_zero σ)]
  congr 1
  funext i
  fin_cases i
  · simp only [Fin.zero_eta, Matrix.cons_val_zero]
    rw [hσ, bar_eq_inv_of_norm h (inv_mem hδ), inv_inv]
  · simp
  · simp

theorem isInnerAut_psuConj_of_sq (h : UnitaryFieldData p 1 F) (A : ↥(unitaryIsom3 h))
    (h2 : IsInnerAut (psuConj h A * psuConj h A)) : IsInnerAut (psuConj h A) := by
  obtain ⟨y, hy⟩ := h2
  obtain ⟨s, rfl⟩ := unitaryProj_surjective h 3 y
  set sG : ↥(unitaryIsom3 h) := ⟨(s : GL (Fin 3) F), unitarySU_le_unitaryIsom3 s.2⟩ with hsG
  have hy' : psuConj h sG = psuConj h A * psuConj h A := by
    rw [← hy, hsG, ← conj_mk_eq_psuConj]
    rfl
  have h3 : psuConj h (A * A * sG⁻¹) * psuField h (1 : F ≃+* F) = 1 := by
    rw [map_one, mul_one, map_mul, map_mul, map_inv, ← hy']
    exact mul_inv_cancel _
  obtain ⟨-, c, hc, hB⟩ := eq_one_of_psuConj_mul_psuField_eq_one (A * A * sG⁻¹) 1 h3
  have hAA : (A : GL (Fin 3) F) * A = GeneralLinearGroup.scalar (Fin 3) c * (s : GL (Fin 3) F) := by
    have hB' : (A : GL (Fin 3) F) * A * (s : GL (Fin 3) F)⁻¹ =
        GeneralLinearGroup.scalar (Fin 3) c := hB
    calc (A : GL (Fin 3) F) * A = ((A : GL (Fin 3) F) * A * (s : GL (Fin 3) F)⁻¹) * s := by group
      _ = _ := by rw [hB']
  have hdets : GeneralLinearGroup.det (s : GL (Fin 3) F) = 1 := by
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply]
    exact ((mem_unitarySU_iff h).mp s.2).1
  have hdet : GeneralLinearGroup.det (A : GL (Fin 3) F) ^ 2 = c ^ 3 := by
    have := congrArg GeneralLinearGroup.det hAA
    rwa [map_mul, map_mul, det_scalar_three, hdets, mul_one, ← pow_two] at this
  obtain ⟨m, hm, hm3⟩ := exists_cube_of_sq_eq (normOneUnits h) (det_mem_normOneUnits h A.2) hc
    hdet
  have hA'GU : GeneralLinearGroup.scalar (Fin 3) m⁻¹ * (A : GL (Fin 3) F) ∈ unitaryIsom3 h :=
    mul_mem (scalar_mem_unitaryIsom3 h (inv_mem hm)) A.2
  have hA'det : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) m⁻¹ *
      (A : GL (Fin 3) F)) = 1 := by
    rw [map_mul, det_scalar_three, inv_pow, hm3]
    group
  set A' : ↥(unitarySU p 1 F 3) := ⟨GeneralLinearGroup.scalar (Fin 3) m⁻¹ * (A : GL (Fin 3) F),
    (mem_unitarySU_iff h).mpr ⟨by
      have := congrArg Units.val hA'det
      rwa [GeneralLinearGroup.val_det_apply, Units.val_one] at this, mem_unitaryIsom3.mp hA'GU⟩⟩
    with hA'
  have hAA' : A = ⟨GeneralLinearGroup.scalar (Fin 3) m, scalar_mem_unitaryIsom3 h hm⟩ *
      ⟨(A' : GL (Fin 3) F), unitarySU_le_unitaryIsom3 A'.2⟩ := by
    apply Subtype.ext
    change (A : GL (Fin 3) F) = GeneralLinearGroup.scalar (Fin 3) m *
      (GeneralLinearGroup.scalar (Fin 3) m⁻¹ * (A : GL (Fin 3) F))
    rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  refine ⟨(A' : unitaryPSU h 3), ?_⟩
  rw [conj_mk_eq_psuConj]
  conv_rhs => rw [hAA', map_mul, psuConj_scalar (scalar_mem_unitaryIsom3 h hm), one_mul]

theorem unitary_classify_psu (h : UnitaryFieldData p 1 F) (hp2 : p ≠ 2)
    (θ : MulAut (unitaryPSU h 3)) (h1 : ¬ IsInnerAut θ) (h2 : IsInnerAut (θ * θ)) :
    ∃ (x : ↥(unitaryIsom3 h)) (A : ↥(unitarySU p 1 F 3)) (σ : F ≃+* F), (∀ c, σ c = h.bar c) ∧
      psuConj h x * θ * (psuConj h x)⁻¹ =
        psuConj h ⟨A, unitarySU_le_unitaryIsom3 A.2⟩ * psuField h σ := by
  have hq2 : 2 < p ^ 1 := by
    have := h.prime.two_le
    rw [pow_one]
    omega
  obtain ⟨A, σ, hθ⟩ := exists_psuConj_mul_psuField hq2 θ
  rcases ringEquiv_eq_one_or_bar h σ with hσ | hσ
  ·
    exfalso
    subst hσ
    rw [map_one, mul_one] at hθ
    subst hθ
    exact h1 (isInnerAut_psuConj_of_sq h A h2)
  ·
    set d : Fˣ := GeneralLinearGroup.det (A : GL (Fin 3) F) with hd
    have hdN : d ∈ normOneUnits h := det_mem_normOneUnits h A.2
    set xG : ↥(unitaryIsom3 h) := ⟨diagOne d, diagOne_mem_unitaryIsom3 h hdN⟩ with hxG
    have hxi : psuField h σ * psuConj h xG⁻¹ * (psuField h σ)⁻¹ = psuConj h xG := by
      rw [psuField_mul_psuConj_mul_inv]
      congr 1
      apply Subtype.ext
      exact glAut_inv_diagOne h hσ hdN
    have hBGU : GeneralLinearGroup.scalar (Fin 3) d⁻¹ * (diagOne d * (A : GL (Fin 3) F) *
        diagOne d) ∈ unitaryIsom3 h :=
      mul_mem (scalar_mem_unitaryIsom3 h (inv_mem hdN)) (mul_mem (mul_mem xG.2 A.2) xG.2)
    have hBdet : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) d⁻¹ *
        (diagOne d * (A : GL (Fin 3) F) * diagOne d)) = 1 := by
      rw [map_mul, map_mul, map_mul, det_scalar_three, det_diagOne, ← hd]
      group
    set B : ↥(unitarySU p 1 F 3) := ⟨GeneralLinearGroup.scalar (Fin 3) d⁻¹ *
      (diagOne d * (A : GL (Fin 3) F) * diagOne d), (mem_unitarySU_iff h).mpr ⟨by
        have := congrArg Units.val hBdet
        rwa [GeneralLinearGroup.val_det_apply, Units.val_one] at this,
          mem_unitaryIsom3.mp hBGU⟩⟩ with hB
    refine ⟨xG, B, σ, hσ, ?_⟩
    have hBxAx : (⟨(B : GL (Fin 3) F), unitarySU_le_unitaryIsom3 B.2⟩ : ↥(unitaryIsom3 h)) =
        ⟨GeneralLinearGroup.scalar (Fin 3) d⁻¹, scalar_mem_unitaryIsom3 h (inv_mem hdN)⟩ *
          (xG * A * xG) := rfl
    calc psuConj h xG * θ * (psuConj h xG)⁻¹
        = psuConj h xG * (psuConj h A * psuField h σ) * (psuConj h xG)⁻¹ := by rw [hθ]
      _ = psuConj h xG * psuConj h A * (psuField h σ * psuConj h xG⁻¹ * (psuField h σ)⁻¹) *
          psuField h σ := by
        rw [map_inv]
        group
      _ = psuConj h (xG * A * xG) * psuField h σ := by rw [hxi, map_mul, map_mul]
      _ = psuConj h ⟨(B : GL (Fin 3) F), unitarySU_le_unitaryIsom3 B.2⟩ * psuField h σ := by
        rw [hBxAx, map_mul (psuConj h) ⟨GeneralLinearGroup.scalar (Fin 3) d⁻¹,
          scalar_mem_unitaryIsom3 h (inv_mem hdN)⟩ (xG * A * xG),
          psuConj_scalar (scalar_mem_unitaryIsom3 h (inv_mem hdN)), one_mul]

end Psu

section Su

variable {p : ℕ} {F : Type} [Field F]

theorem mulAut_eq_of_inv_mul_mem_center_perfect {S : Type*} [Group S] [Group.IsPerfect S]
    {α β : MulAut S} (h : ∀ s, (β s)⁻¹ * α s ∈ Subgroup.center S) : α = β := by
  let z : S →* Subgroup.center S :=
    { toFun := fun s => ⟨(β s)⁻¹ * α s, h s⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun s t => by
        apply Subtype.ext
        have hc := Subgroup.mem_center_iff.mp (h s) ((β t)⁻¹)
        simp only [map_mul, _root_.mul_inv_rev, Subgroup.coe_mul]
        calc (β t)⁻¹ * (β s)⁻¹ * (α s * α t) = (β t)⁻¹ * ((β s)⁻¹ * α s) * α t := by group
          _ = (β s)⁻¹ * α s * (β t)⁻¹ * α t := by rw [hc]
          _ = (β s)⁻¹ * α s * ((β t)⁻¹ * α t) := by group }
  have hker : z.ker = ⊤ := by
    rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := S)]
    exact Abelianization.commutator_subset_ker z
  ext s
  have hs : z s = 1 := (MonoidHom.mem_ker).mp (hker ▸ Subgroup.mem_top s)
  have hs' : (β s)⁻¹ * α s = 1 := congrArg Subtype.val hs
  exact (inv_mul_eq_one.mp hs').symm

theorem eq_of_centerDescend_eq_three {f : ℕ} (h : UnitaryFieldData p f F) (hq2 : 2 < p ^ f)
    {β γ : MulAut ↥(unitarySU p f F 3)}
    (hβγ : MulAut.congr (suCenterEquiv h hq2) (centerDescend _ β) =
      MulAut.congr (suCenterEquiv h hq2) (centerDescend _ γ)) : β = γ := by
  have : Group.IsPerfect ↥(unitarySU p f F 3) := isPerfect_unitarySU_three h hq2
  have hγ' : centerDescend _ β = centerDescend _ γ := (MulAut.congr _).injective hβγ
  apply mulAut_eq_of_inv_mul_mem_center_perfect
  intro g
  have h1 := congrArg (fun τ : MulAut (↥(unitarySU p f F 3) ⧸ Subgroup.center _) =>
    τ (g : ↥(unitarySU p f F 3) ⧸ Subgroup.center _)) hγ'
  simp only [centerDescend_mk] at h1
  exact QuotientGroup.eq.mp h1.symm

theorem congr_centerDescend_suConj {f : ℕ} (h : UnitaryFieldData p f F) (hq2 : 2 < p ^ f)
    (A : ↥(unitaryIsom3 h)) :
    MulAut.congr (suCenterEquiv h hq2) (centerDescend _ (suConj h A)) = psuConj h A := by
  ext y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  rfl

theorem congr_centerDescend_suField {f : ℕ} (h : UnitaryFieldData p f F) (hq2 : 2 < p ^ f)
    (σ : F ≃+* F) :
    MulAut.congr (suCenterEquiv h hq2) (centerDescend _ (suField h σ)) = psuField h σ := by
  ext y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  rfl

theorem unitary_classify_su (h : UnitaryFieldData p 1 F) (hp2 : p ≠ 2)
    (φ : MulAut ↥(unitarySU p 1 F 3)) (h1 : ¬ IsInnerAut φ) (h2 : IsInnerAut (φ * φ)) :
    ∃ (x : ↥(unitaryIsom3 h)) (A : ↥(unitarySU p 1 F 3)) (σ : F ≃+* F), (∀ c, σ c = h.bar c) ∧
      suConj h x * φ * (suConj h x)⁻¹ =
        suConj h ⟨A, unitarySU_le_unitaryIsom3 A.2⟩ * suField h σ := by
  have hq2 : 2 < p ^ 1 := by
    have := h.prime.two_le
    rw [pow_one]
    omega
  set θ : MulAut (unitaryPSU h 3) := MulAut.congr (suCenterEquiv h hq2) (centerDescend _ φ)
    with hθ
  have h1' : ¬ IsInnerAut θ := fun hh => h1 ((isInnerAut_congr_centerDescend_iff h hq2).mp hh)
  have h2' : IsInnerAut (θ * θ) := by
    rw [hθ, ← map_mul, ← map_mul]
    exact (isInnerAut_congr_centerDescend_iff h hq2).mpr h2
  obtain ⟨x, A, σ, hσ, hxA⟩ := unitary_classify_psu h hp2 θ h1' h2'
  refine ⟨x, A, σ, hσ, eq_of_centerDescend_eq_three h hq2 ?_⟩
  simp only [map_mul, map_inv, congr_centerDescend_suConj, congr_centerDescend_suField]
  exact hxA

end Su

section Stated

variable {p : ℕ} {F : Type} [Field F]

theorem classify_unitary_stated_su {q : ℕ} (hq : q = p ^ 1) (h : UnitaryFieldData p 1 F)
    (hp2 : p ≠ 2) (φ : MulAut ↥(StatedSU 3 q F)) (h1 : ¬ IsInnerAut φ)
    (h2 : IsInnerAut (φ * φ)) :
    ∃ (ε : MulAut ↥(StatedSU 3 q F)) (g : ↥(StatedSU 3 q F)), ∀ s : ↥(StatedSU 3 q F),
      ((((ε * φ * ε⁻¹) s : ↥(StatedSU 3 q F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          (((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)⁻¹)ᵀ *
            (((g : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  subst hq
  obtain ⟨x, A, σ, hσ, hxA⟩ := unitary_classify_su h hp2 φ h1 h2
  refine ⟨suConj h x, A, fun s => ?_⟩
  have hmap : ((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map σ =
      ((((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))⁻¹)ᵀ := by
    rw [← map_bar_eq_inv_transpose h s]
    exact Matrix.ext fun i j => hσ _
  rw [hxA, MulAut.mul_apply, coe_suConj, coe_suField, Units.val_mul, Units.val_mul,
    UnitaryHigher.coe_glAut, hmap]
  rfl

theorem classify_unitary_stated_psu {q : ℕ} (hq : q = p ^ 1) (h : UnitaryFieldData p 1 F)
    (hp2 : p ≠ 2) (θ : MulAut (StatedProj (StatedSU 3 q F))) (h1 : ¬ IsInnerAut θ)
    (h2 : IsInnerAut (θ * θ)) :
    ∃ (ε : MulAut (StatedProj (StatedSU 3 q F))) (Θ : MulAut ↥(StatedSU 3 q F))
      (g : ↥(StatedSU 3 q F)), (∀ s : ↥(StatedSU 3 q F),
        ((((Θ s : ↥(StatedSU 3 q F)) : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) =
          ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
            (((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)⁻¹)ᵀ *
              (((g : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) ∧
        ∀ s : ↥(StatedSU 3 q F), (ε * θ * ε⁻¹) (QuotientGroup.mk s) =
          QuotientGroup.mk (Θ s) := by
  subst hq
  set uE := unitaryPSUEquiv h (by norm_num : 1 ≤ 3) with huE
  set θ' : MulAut (unitaryPSU h 3) := MulAut.congr uE.symm θ with hθ'
  have h1' : ¬ IsInnerAut θ' := fun hh => h1 ((isInnerAut_congr uE.symm θ).mp hh)
  have h2' : IsInnerAut (θ' * θ') := by
    rw [hθ', ← map_mul]
    exact (isInnerAut_congr uE.symm (θ * θ)).mpr h2
  obtain ⟨x, A, σ, hσ, hxA⟩ := unitary_classify_psu h hp2 θ' h1' h2'
  have hθ : MulAut.congr uE θ' = θ := by
    ext y
    simp [hθ', MulAut.congr_apply]
  refine ⟨MulAut.congr uE (psuConj h x), suConj h ⟨A, unitarySU_le_unitaryIsom3 A.2⟩ * suField h σ,
    A, fun s => ?_, fun s => ?_⟩
  · have hmap : ((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map σ =
        ((((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))⁻¹)ᵀ := by
      rw [← map_bar_eq_inv_transpose h s]
      exact Matrix.ext fun i j => hσ _
    rw [MulAut.mul_apply, coe_suConj, coe_suField, Units.val_mul, Units.val_mul,
      UnitaryHigher.coe_glAut, hmap]
    rfl
  · have h3 : MulAut.congr uE (psuConj h x) * θ * (MulAut.congr uE (psuConj h x))⁻¹ =
        MulAut.congr uE (psuConj h ⟨A, unitarySU_le_unitaryIsom3 A.2⟩ * psuField h σ) := by
      rw [← hxA, map_mul, map_mul, map_inv, hθ]
    rw [h3]
    have h4 : (QuotientGroup.mk s : StatedProj (StatedSU 3 (p ^ 1) F)) =
        uE (unitaryProj h 3 s) := (unitaryPSUEquiv_unitaryProj h (by norm_num) s).symm
    rw [h4]
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      MulAut.mul_apply]
    rw [show unitaryProj h 3 s = (s : unitaryPSU h 3) from rfl, psuField_mk, psuConj_mk]
    exact unitaryPSUEquiv_unitaryProj h (by norm_num) _

end Stated

end G22M12Ident

end CFSG.Quasithin.F6
