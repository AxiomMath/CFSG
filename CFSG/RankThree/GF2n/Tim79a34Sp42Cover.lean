module

public import CFSG.Open.StatedDefs
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpTwoTwo
public import CFSG.Quasithin.H13.L32NSp4S6
public import CFSG.Quasithin.Background.F6CatRecogTools3
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15422Cat
public import CFSG.ClassicalInvolution.SL2Facts
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearRingEquiv
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2Subgroups
public import Mathlib.GroupTheory.SemidirectProduct
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherWalterSchurEight
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.Monster.Existence.Defs
public import CFSG.Open.MonsterY443Defs
public import CFSG.Quasithin.Background.F6CatRecogL2
public import CFSG.Quasithin.Background.F6CatRecogTools2
public import CFSG.Quasithin.H13.L32NSp4S120
public import CFSG.Quasithin.H13.L32NSp4S36
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.SignalizerFunctorTheorem.NonLocal.Cross
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpData
public import CFSG.Walter.J1
public import CFSG.Walter.J1Props
public import CFSG.Walter.J1Recog
public import CFSG.Walter.PSL2Facts
public import CFSG.Walter.W67.Statements
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG.Open Matrix Subgroup
open CFSG.GorensteinWalter
open CFSG.Quasithin.F6

noncomputable section

abbrev GF9 : Type := GaloisField 3 2

abbrev SL2Nine : Type := Matrix.SpecialLinearGroup (Fin 2) GF9

abbrev frobNine : GF9 ≃+* GF9 := frobeniusEquiv GF9 3

theorem frobNine_apply (x : GF9) : frobNine x = x ^ 3 := rfl

theorem frobNine_mul_self : frobNine * frobNine = 1 := by
  ext x
  change frobNine (frobNine x) = x
  rw [frobNine_apply, frobNine_apply, ← pow_mul]
  letI : Fintype GF9 := Fintype.ofFinite GF9
  have hcard : Fintype.card GF9 = 9 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 3 2 (by norm_num)]
    norm_num
  simpa [hcard] using FiniteField.pow_card x

theorem c2_cases (x : Multiplicative (ZMod 2)) : x = 1 ∨ x = Multiplicative.ofAdd 1 := by
  revert x
  decide

theorem c2_eps_mul_self :
    (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd 1 = 1 := by
  decide

noncomputable def c2FieldHom : Multiplicative (ZMod 2) →* (GF9 ≃+* GF9) where
  toFun x := if x = 1 then 1 else frobNine
  map_one' := by simp
  map_mul' := by
    intro x y
    rcases c2_cases x with rfl | rfl <;> rcases c2_cases y with rfl | rfl <;>
      simp [c2_eps_mul_self, frobNine_mul_self]

@[simp] theorem c2FieldHom_one : c2FieldHom 1 = 1 := map_one _

@[simp] theorem c2FieldHom_ofAdd_one :
    c2FieldHom (Multiplicative.ofAdd 1) = frobNine := by
  simp [c2FieldHom]

@[expose] noncomputable def frobSL : SL2Nine ≃* SL2Nine := by
  let f : SL2Nine →* SL2Nine := Matrix.SpecialLinearGroup.map frobNine.toRingHom
  let g : SL2Nine →* SL2Nine := Matrix.SpecialLinearGroup.map frobNine.symm.toRingHom
  refine MonoidHom.toMulEquiv f g ?_ ?_
  · ext x i j
    simp [f, g, Matrix.SpecialLinearGroup.map_apply_coe]
  · ext x i j
    simp [f, g, Matrix.SpecialLinearGroup.map_apply_coe]

theorem frobSL_apply (n : SL2Nine) :
    frobSL n = Matrix.SpecialLinearGroup.map frobNine.toRingHom n := rfl

theorem frobSL_mul_self : frobSL * frobSL = 1 := by
  apply MulEquiv.ext
  intro x
  change frobSL (frobSL x) = x
  rw [frobSL_apply, frobSL_apply]
  ext i j
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  change frobNine (frobNine ((x : Matrix (Fin 2) (Fin 2) GF9) i j)) =
    (x : Matrix (Fin 2) (Fin 2) GF9) i j
  rw [frobNine_apply, frobNine_apply, ← pow_mul]
  letI : Fintype GF9 := Fintype.ofFinite GF9
  have hcard : Fintype.card GF9 = 9 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 3 2 (by norm_num)]
    norm_num
  simpa [hcard] using FiniteField.pow_card ((x : Matrix (Fin 2) (Fin 2) GF9) i j)

noncomputable def c2Act : Multiplicative (ZMod 2) →* MulAut SL2Nine where
  toFun x := if x = 1 then 1 else frobSL
  map_one' := by simp
  map_mul' := by
    intro x y
    rcases c2_cases x with rfl | rfl <;> rcases c2_cases y with rfl | rfl <;>
      simp [c2_eps_mul_self, frobSL_mul_self]

@[simp] theorem c2Act_one : c2Act 1 = 1 := map_one _

@[simp] theorem c2Act_ofAdd_one : c2Act (Multiplicative.ofAdd 1) = frobSL := by
  simp [c2Act]

abbrev CoverSp42 : Type := SL2Nine ⋊[c2Act] Multiplicative (ZMod 2)

instance : Group CoverSp42 := inferInstance

instance : Finite CoverSp42 :=
  Finite.of_equiv (SL2Nine × Multiplicative (ZMod 2)) SemidirectProduct.equivProd.symm

theorem frobNine_ne_one : frobNine ≠ 1 := by
  letI : Fintype GF9 := Fintype.ofFinite GF9
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Fintype.card GF9 = 3 ^ 2 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 3 2 (by norm_num)]
  obtain ⟨-, σ, hσne, hσpow⟩ :=
    CFSG.Quasithin.EmptyFaithfulMultiple.L15422.card_ringEquiv_eq_two (p := 3) (K := GF9) hcard
  have hσ : σ = frobNine := RingEquiv.ext fun x => by rw [hσpow, frobNine_apply]
  exact fun h => hσne (hσ ▸ h)

theorem c2FieldHom_injective : Function.Injective c2FieldHom := by
  intro x y hxy
  rcases c2_cases x with rfl | rfl <;> rcases c2_cases y with rfl | rfl
  · rfl
  · exfalso
    have h : (1 : GF9 ≃+* GF9) = frobNine := by simpa [c2FieldHom] using hxy
    exact frobNine_ne_one h.symm
  · exfalso
    have h : frobNine = (1 : GF9 ≃+* GF9) := by simpa [c2FieldHom] using hxy
    exact frobNine_ne_one h
  · rfl

noncomputable def fn : SL2Nine →* PGammaL2 GF9 :=
  (SemidirectProduct.inl : PGL2 GF9 →* PGammaL2 GF9).comp
    ((Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := GF9)).comp
      (QuotientGroup.mk' (Subgroup.center SL2Nine)))

noncomputable def fg : Multiplicative (ZMod 2) →* PGammaL2 GF9 :=
  (SemidirectProduct.inr : (GF9 ≃+* GF9) →* PGammaL2 GF9).comp c2FieldHom

theorem fn_ker : fn.ker = Subgroup.center SL2Nine := by
  ext n
  rw [MonoidHom.mem_ker, fn, MonoidHom.comp_apply, MonoidHom.comp_apply,
    ← map_one (SemidirectProduct.inl : PGL2 GF9 →* PGammaL2 GF9),
    SemidirectProduct.inl_inj,
    ← map_one (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := GF9)),
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective.eq_iff,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem fn_frobSL (n : SL2Nine) :
    fn (frobSL n) =
      fg (Multiplicative.ofAdd 1) * fn n * (fg (Multiplicative.ofAdd 1))⁻¹ := by
  have hmiddle : Matrix.ProjectiveSpecialLinearGroup.toPGL
      ((QuotientGroup.mk' (center SL2Nine)) (frobSL n)) =
      (pgl2FieldAut GF9) frobNine
        (Matrix.ProjectiveSpecialLinearGroup.toPGL
          ((QuotientGroup.mk' (center SL2Nine)) n)) := by
    rw [← psl2FieldAut_toPGL]
    congr 1
    rw [frobSL_apply, psl2FieldAut_apply, psl2RingEquiv_mk]
  calc
    fn (frobSL n) = SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL
        ((QuotientGroup.mk' (center SL2Nine)) (frobSL n))) := rfl
    _ = SemidirectProduct.inl ((pgl2FieldAut GF9) frobNine
        (Matrix.ProjectiveSpecialLinearGroup.toPGL
          ((QuotientGroup.mk' (center SL2Nine)) n))) := by rw [hmiddle]
    _ = SemidirectProduct.inr frobNine *
        SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL
          ((QuotientGroup.mk' (center SL2Nine)) n)) *
        (SemidirectProduct.inr frobNine)⁻¹ := by
      simpa [map_inv] using
        (SemidirectProduct.inl_aut (φ := pgl2FieldAut GF9) frobNine
          (Matrix.ProjectiveSpecialLinearGroup.toPGL
            ((QuotientGroup.mk' (center SL2Nine)) n)))
    _ = fg (Multiplicative.ofAdd 1) * fn n * (fg (Multiplicative.ofAdd 1))⁻¹ := by
      simp only [fn, fg, MonoidHom.comp_apply, c2FieldHom_ofAdd_one]

noncomputable def Phi : CoverSp42 →* PGammaL2 GF9 :=
  SemidirectProduct.lift (φ := c2Act) (H := PGammaL2 GF9) fn fg (by
    intro g
    rcases c2_cases g with rfl | rfl
    · apply MonoidHom.ext
      intro n
      simp [fg, MonoidHom.comp_apply]
    · apply MonoidHom.ext
      intro n
      rw [c2Act_ofAdd_one]
      change fn (frobSL n) = (MulAut.conj (fg (Multiplicative.ofAdd 1))) (fn n)
      rw [fg, MonoidHom.comp_apply, c2FieldHom_ofAdd_one]
      simpa [fg, MonoidHom.comp_apply, c2FieldHom_ofAdd_one, MulAut.conj_apply]
        using fn_frobSL n)

@[simp] theorem Phi_inl (n : SL2Nine) : Phi (SemidirectProduct.inl n) = fn n :=
  SemidirectProduct.lift_inl _ _ _ n

@[simp] theorem Phi_inr (g : Multiplicative (ZMod 2)) :
    Phi (SemidirectProduct.inr g) = fg g :=
  SemidirectProduct.lift_inr _ _ _ g

theorem rightHom_Phi (x : CoverSp42) :
    SemidirectProduct.rightHom (Phi x) = c2FieldHom x.right := by
  rw [← SemidirectProduct.inl_left_mul_inr_right x, map_mul, Phi_inl, Phi_inr]
  simp [fn, fg]

theorem Phi_mem_pSigmaL2 (x : CoverSp42) : Phi x ∈ CFSG.Quasithin.F6.PSigmaL2 GF9 := by
  rw [← SemidirectProduct.inl_left_mul_inr_right x, map_mul, Phi_inl, Phi_inr]
  refine (CFSG.Quasithin.F6.PSigmaL2 GF9).mul_mem ?_ ?_
  · exact (le_sup_left : pGammaL2PSLRange GF9 ≤ CFSG.Quasithin.F6.PSigmaL2 GF9)
      (show fn x.left ∈ pGammaL2PSLRange GF9 from ⟨QuotientGroup.mk x.left, rfl⟩)
  · exact (le_sup_right : (SemidirectProduct.inr : (GF9 ≃+* GF9) →* PGammaL2 GF9).range ≤
      CFSG.Quasithin.F6.PSigmaL2 GF9)
      (show fg x.right ∈ (SemidirectProduct.inr : (GF9 ≃+* GF9) →* PGammaL2 GF9).range from
        ⟨c2FieldHom x.right, rfl⟩)

theorem Phi_ker : Phi.ker = (Subgroup.center SL2Nine).map (SemidirectProduct.inl) := by
  ext x
  constructor
  · intro hx
    have hright : c2FieldHom x.right = 1 := by
      have h := congrArg SemidirectProduct.rightHom hx
      rwa [rightHom_Phi, map_one] at h
    have hxr : x.right = 1 := c2FieldHom_injective (by rw [hright, map_one])
    have hxdecomp : x = SemidirectProduct.inl x.left := by
      conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right x]
      rw [hxr, map_one, mul_one]
    rw [hxdecomp] at hx ⊢
    have hfn : fn x.left = 1 := by simpa using hx
    exact ⟨x.left, (fn_ker ▸ MonoidHom.mem_ker.mpr hfn), rfl⟩
  · intro hx
    rcases hx with ⟨z, hz, rfl⟩
    rw [MonoidHom.mem_ker, Phi_inl]
    exact MonoidHom.mem_ker.mp (fn_ker ▸ hz)

theorem frobSL_neg_one : frobSL (-1 : SL2Nine) = -1 := by
  rw [frobSL_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]

theorem c2Act_center {z : SL2Nine} (hz : z ∈ Subgroup.center SL2Nine)
    (g : Multiplicative (ZMod 2)) : c2Act g z = z := by
  rcases c2_cases g with rfl | rfl
  · simp
  · rw [c2Act_ofAdd_one]
    rcases (CFSG.ClassicalInvolution.mem_center_sl2_iff z).mp hz with rfl | rfl
    · simp
    · exact frobSL_neg_one

theorem center_le_center_cover :
    (Subgroup.center SL2Nine).map (SemidirectProduct.inl) ≤ Subgroup.center CoverSp42 := by
  rintro _ ⟨z, hz, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro x
  have hx : x = SemidirectProduct.inl x.left * SemidirectProduct.inr x.right :=
    (SemidirectProduct.inl_left_mul_inr_right x).symm
  have hcomm : (SemidirectProduct.inl (φ := c2Act) z : CoverSp42) *
      (SemidirectProduct.inr (φ := c2Act) x.right : CoverSp42) =
      (SemidirectProduct.inr (φ := c2Act) x.right : CoverSp42) *
        (SemidirectProduct.inl (φ := c2Act) z : CoverSp42) := by
    rw [SemidirectProduct.mul_def, SemidirectProduct.mul_def]
    simp [c2Act_center hz x.right]
  rw [hx]
  symm
  calc
    SemidirectProduct.inl z *
        (SemidirectProduct.inl x.left * SemidirectProduct.inr x.right) =
        (SemidirectProduct.inl z * SemidirectProduct.inl x.left) *
          SemidirectProduct.inr x.right := by rw [mul_assoc]
    _ = SemidirectProduct.inl (z * x.left) * SemidirectProduct.inr x.right := by
      rw [← map_mul]
    _ = SemidirectProduct.inl (x.left * z) * SemidirectProduct.inr x.right := by
      rw [Subgroup.mem_center_iff.mp hz x.left]
    _ = (SemidirectProduct.inl x.left * SemidirectProduct.inl z) *
          SemidirectProduct.inr x.right := by rw [map_mul]
    _ = SemidirectProduct.inl x.left *
          (SemidirectProduct.inl z * SemidirectProduct.inr x.right) := by
      rw [← mul_assoc]
    _ = SemidirectProduct.inl x.left *
          (SemidirectProduct.inr x.right * SemidirectProduct.inl z) := by rw [hcomm]
    _ = (SemidirectProduct.inl x.left * SemidirectProduct.inr x.right) *
          SemidirectProduct.inl z := by rw [← mul_assoc]

theorem center_le_commutator :
    (Subgroup.center SL2Nine).map (SemidirectProduct.inl) ≤ commutator CoverSp42 := by
  rintro _ ⟨z, hz, rfl⟩
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) GF9) :=
    CFSG.ClassicalInvolution.sl2_isPerfect (F := GF9) (by
      rw [show Nat.card GF9 = 9 by rw [GaloisField.card 3 2 (by norm_num)]; norm_num]
      norm_num)
  have hz' : z ∈ commutator SL2Nine := by
    rw [hperf.commutator_eq_top]
    exact Subgroup.mem_top z
  have hmem : (SemidirectProduct.inl (φ := c2Act) z : CoverSp42) ∈
      (commutator SL2Nine).map (SemidirectProduct.inl (φ := c2Act)) :=
    ⟨z, hz', rfl⟩
  rw [commutator_def, Subgroup.map_commutator] at hmem
  have hle : ⁅(⊤ : Subgroup SL2Nine).map (SemidirectProduct.inl (φ := c2Act)),
      (⊤ : Subgroup SL2Nine).map (SemidirectProduct.inl (φ := c2Act))⁆ ≤
      commutator CoverSp42 := by
    rw [commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  exact hle hmem

theorem card_SL2Nine : Nat.card SL2Nine = 720 := by
  rw [sl2_card_formula]
  have hK : Nat.card GF9 = 9 := by rw [GaloisField.card 3 2 (by norm_num)]; norm_num
  rw [hK]
  norm_num

theorem card_center_SL2Nine : Nat.card (Subgroup.center SL2Nine) = 2 := by
  apply CFSG.ClassicalInvolution.sl2_natCard_center
  rw [show Nat.card GF9 = 9 by rw [GaloisField.card 3 2 (by norm_num)]; norm_num]
  norm_num

theorem card_CoverSp42 : Nat.card CoverSp42 = 1440 := by
  rw [SemidirectProduct.card, card_SL2Nine]
  congr 1
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2),
    Nat.card_eq_fintype_card, ZMod.card]

theorem card_statedSp_two_one :
    Nat.card (StatedSp 2 (GaloisField 2 1)) = 720 := by
  have hF2 : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero, pow_one]
  let e : StatedSp 2 (GaloisField 2 1) ≃* Equiv.Perm (Fin 6) :=
    (CFSG.SignalizerFunctorTheorem.NonLocal.spTwoTwoEquiv hF2).trans
      CFSG.Quasithin.H13.Sp4Cert.sympFourEquiv
  rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
  norm_num

theorem exists_cover_statedSp_two_one :
    ∃ (Γ : Type) (_ : Group Γ) (_ : Finite Γ)
      (φ : Γ →* StatedSp 2 (GaloisField 2 1)),
      Function.Surjective φ ∧ φ.ker ≤ Subgroup.center Γ ∧
        φ.ker ≤ commutator Γ ∧ Nat.card φ.ker = 2 := by
  have hK9 : Nat.card GF9 = 9 := by rw [GaloisField.card 3 2 (by norm_num)]; norm_num
  obtain ⟨eSigma⟩ :=
    CFSG.Quasithin.F6.nonempty_pSigmaL2_mulEquiv_perm_six GF9 hK9
  have hF2 : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero, pow_one]
  let eSp : StatedSp 2 (GaloisField 2 1) ≃* Equiv.Perm (Fin 6) :=
    (CFSG.SignalizerFunctorTheorem.NonLocal.spTwoTwoEquiv hF2).trans
      CFSG.Quasithin.H13.Sp4Cert.sympFourEquiv
  let Phi' : CoverSp42 →* ↥(CFSG.Quasithin.F6.PSigmaL2 GF9) :=
    Phi.codRestrict _ Phi_mem_pSigmaL2
  let φ : CoverSp42 →* StatedSp 2 (GaloisField 2 1) :=
    eSp.symm.toMonoidHom.comp (eSigma.toMonoidHom.comp Phi')
  have hφker : φ.ker = Phi.ker := by
    simp only [φ]
    rw [MonoidHom.ker_comp_of_injective _ _ eSp.symm.injective,
      MonoidHom.ker_comp_of_injective _ _ eSigma.injective, MonoidHom.ker_codRestrict]
  have hker : Nat.card φ.ker = 2 := by
    rw [hφker, Phi_ker, Subgroup.card_map_of_injective (SemidirectProduct.inl_injective),
      card_center_SL2Nine]
  have hcenter : φ.ker ≤ Subgroup.center CoverSp42 := by
    rw [hφker, Phi_ker]
    exact center_le_center_cover
  have hcomm : φ.ker ≤ commutator CoverSp42 := by
    rw [hφker, Phi_ker]
    exact center_le_commutator
  have hsurj : Function.Surjective φ := by
    have hcardΓ : Nat.card CoverSp42 = 1440 := card_CoverSp42
    have hcardRange : Nat.card φ.range = 720 := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv] at h
      rw [hcardΓ, hker] at h
      omega
    have htop : φ.range = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [hcardRange, card_statedSp_two_one]
    exact MonoidHom.range_eq_top.mp htop
  exact ⟨CoverSp42, inferInstance, inferInstance, φ, hsurj, hcenter, hcomm, hker⟩


end

end CFSG.RankThree.GF2n.Tim79a
