module

public import CFSG.RankThree.PartOne.S11d.PSUTwistSigma
public import CFSG.RankThree.PartOne.S11d.PSUTwistRat
public import CFSG.RankThree.PartOne.S11d.PSUGood
public import CFSG.RankThree.PartOne.S11d.PSUModel
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.ClassicalGroups
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCover
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBFixedLayer
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Monster.Existence.Defs
public import CFSG.Open.MonsterY443Defs
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.KC.OrthogonalLocalComponents
public import CFSG.RankThree.PartOne.KC.OrthogonalNormPlaneFactors
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSetting
public import CFSG.RankThree.PartOne.KF.F128Syl
public import CFSG.RankThree.PartOne.KF.SU5Model
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartOne.S11c.Sec66Sp
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
public import CFSG.RankThree.SteinbergR3ECAFieldFixedLayerQuotient
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.Walter.Defs
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate1
public import Certificates.Certificate10005
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10010
public import Certificates.Certificate10012
public import Certificates.Certificate10013
public import Certificates.Certificate10014
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2267
public import Certificates.Certificate2326
public import Certificates.Certificate3006
public import Certificates.Certificate3007
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate9130

public section

namespace CFSG.RankThree.PartOne.TCU

open Matrix Subgroup CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.OddIso CFSG.LinearGroups
open scoped commutatorElement

variable {F n p : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 F K}

section Scalar

omit h in
theorem linOf_scalar (d : Kˣ) :
    linOf (GeneralLinearGroup.scalar (Fin n) d : GL (Fin n) K) = (d : K) • LinearMap.id := by
  refine LinearMap.ext fun w => ?_
  rw [linOf_apply]
  funext i
  simp [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mulVec_diagonal]

omit h in
theorem glAut_scalar' (σ : K ≃+* K) (d : Kˣ) :
    glAut σ (GeneralLinearGroup.scalar (Fin n) d : GL (Fin n) K) =
      GeneralLinearGroup.scalar (Fin n) (Units.map (σ : K →* K) d) := by
  apply Units.ext
  rw [coe_glAut, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.scalar_apply, Matrix.diagonal_map (map_zero σ)]
  rfl

omit h in
theorem scalar_eq_one_of_fix {d : Kˣ} {W : Submodule K (Fin n → K)} (hW : W ≠ ⊥)
    (hfix : ∀ w ∈ W, linOf (GeneralLinearGroup.scalar (Fin n) d : GL (Fin n) K) w = w) :
    d = 1 := by
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have h1 := hfix w hw
  rw [linOf_scalar] at h1
  have h2 : ((d : K) - 1) • w = 0 := by
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at h1
    rw [sub_smul, h1, one_smul, sub_self]
  exact Units.ext (sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hw0))

end Scalar

section Gl

variable {A : SUn h n} {u : Module.End K (Fin n → K)} {c : K}

noncomputable def TwistSetup.gl (S : TwistSetup h n p A u c) : GL (Fin n) K :=
  (GeneralLinearGroup.scalar (Fin n) (Units.mk0 c⁻¹ (inv_ne_zero S.hc)) : GL (Fin n) K) *
    (A : GL (Fin n) K)

theorem TwistSetup.linOf_gl (S : TwistSetup h n p A u c) : linOf S.gl = u := by
  rw [TwistSetup.gl, linOf_mul, linOf_scalar, S.hAc]
  refine LinearMap.ext fun v => ?_
  simp [Module.End.mul_apply, smul_smul, S.hc]

theorem TwistSetup.glAut_gl (S : TwistSetup h n p A u c) {σ : K ≃+* K} (hσc : σ c = c)
    (hσA : glAut σ (A : GL (Fin n) K) = A) : glAut σ S.gl = S.gl := by
  rw [TwistSetup.gl, map_mul, glAut_scalar', hσA]
  congr 2
  apply Units.ext
  simp [hσc]

theorem TwistSetup.gl_pow (S : TwistSetup h n p A u c) : S.gl ^ p = 1 := by
  apply linOf_injective
  rw [linOf_pow, S.linOf_gl, linOf_one]
  exact S.hup

end Gl

section Transvection

variable (h)

theorem one_add_bar_one : (1 : K) + h.bar 1 = 0 := by
  have hKc : CharP K 2 := h.charP
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [map_one, one_add_one_eq_two, h2]

@[expose] noncomputable def tvSU {a : Fin n → K} (ha : idForm h n a a = 0) : SUn h n :=
  ⟨tvMat h ha 1, tvMat_mem_gramSU h ha (one_add_bar_one h)⟩

theorem coe_tvSU {a : Fin n → K} (ha : idForm h n a a = 0) :
    ((tvSU h ha : SUn h n) : GL (Fin n) K) = tvMat h ha 1 := rfl

theorem tv_pair_facts {σ : K ≃+* K} {a b : Fin n → K} (hσa : σ ∘ a = a) (hσb : σ ∘ b = b)
    (haa : idForm h n a a = 0) (hbb : idForm h n b b = 0) (hab : idForm h n a b ≠ 0) :
    (glAut σ (tvMat h haa 1) = tvMat h haa 1 ∧ tvMat h haa 1 ^ 2 = 1 ∧ tvMat h haa 1 ≠ 1) ∧
    (glAut σ (tvMat h hbb 1) = tvMat h hbb 1 ∧ tvMat h hbb 1 ^ 2 = 1 ∧ tvMat h hbb 1 ≠ 1) ∧
    tvMat h haa 1 * tvMat h hbb 1 ≠ tvMat h hbb 1 * tvMat h haa 1 := by
  have hKc : CharP K 2 := h.charP
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h11 : (1 : K) + 1 = 0 := by rw [one_add_one_eq_two, h2]
  have hbar1 : h.bar (idForm h n a b) = idForm h n b a := ((idForm_isSymm h n).eq a b)
  have ha0 : a ≠ 0 := fun e => hab (by rw [e, map_zero, LinearMap.zero_apply])
  have hb0 : b ≠ 0 := fun e => hab (by rw [e, map_zero])
  have hba : idForm h n b a ≠ 0 := by
    rw [← hbar1]; exact fun e => hab ((map_eq_zero h.bar).mp e)
  have hsq : ∀ (u : Fin n → K) (hu : idForm h n u u = 0), tvMat h hu 1 ^ 2 = 1 := by
    intro u hu
    apply linOf_injective
    rw [linOf_pow, linOf_one, linOf_tvMat, pow_two, Module.End.mul_eq_comp,
      hermTransvection_comp (idForm h n) hu, h11, hermTransvection_zero]
    rfl
  have hfix : ∀ (u : Fin n → K) (hu : idForm h n u u = 0), σ ∘ u = u →
      glAut σ (tvMat h hu 1) = tvMat h hu 1 := by
    intro u hu hσu
    apply linOf_injective
    rw [linOf_glAut_tvMat, linOf_tvMat, hσu, map_one]
  have hne : ∀ (u v : Fin n → K) (hu : idForm h n u u = 0), u ≠ 0 → idForm h n u v ≠ 0 →
      tvMat h hu 1 ≠ 1 := by
    intro u v hu hu0 huv hT
    have h1 := congrArg (fun g => linOf g v) hT
    simp only [linOf_tvMat, hermTransvection_apply, linOf_one, Module.End.one_apply] at h1
    have h3 : (1 * idForm h n u v) • u = 0 := by
      have := h1
      rw [add_eq_left] at this
      exact this
    rcases smul_eq_zero.mp h3 with h4 | h4
    · exact huv (by simpa using h4)
    · exact hu0 h4
  refine ⟨⟨hfix a haa hσa, hsq a haa, hne a b haa ha0 hab⟩,
    ⟨hfix b hbb hσb, hsq b hbb, hne b a hbb hb0 hba⟩, ?_⟩
  intro hcomm
  have h1 := congrArg (fun g => linOf g b) hcomm
  simp only [linOf_mul, Module.End.mul_apply, linOf_tvMat, hermTransvection_apply, map_add,
    map_smul, hbb, mul_zero, zero_smul, add_zero] at h1
  have h5 : (idForm h n a b * idForm h n b a) • b = 0 := by
    have h6 : (b + (1 * idForm h n a b) • a) - (b + (1 * idForm h n a b) •
        (a + (1 * idForm h n b a) • b)) = (-(idForm h n a b * idForm h n b a)) • b := by
      module
    have h7 : (-(idForm h n a b * idForm h n b a)) • b = 0 := by rw [← h6, h1, sub_self]
    rwa [neg_smul, neg_eq_zero] at h7
  rcases smul_eq_zero.mp h5 with h8 | h8
  · exact mul_ne_zero hab hba h8
  · exact hb0 h8

variable {A : SUn h n} {u : Module.End K (Fin n → K)} {c : K} (S : TwistSetup h n p A u c)

theorem tvSU_mem_D {a : Fin n → K} (haV : a ∈ LinearMap.ker (u - 1)) (ha : idForm h n a a = 0) :
    tvSU h ha ∈ S.D := by
  rw [S.mem_D]
  intro w hw
  rw [coe_tvSU, linOf_tvMat, hermTransvection_apply, fix_perp S.hiso haV hw, mul_zero, zero_smul,
    add_zero]

end Transvection

section Inj

variable {A : SUn h n} {u : Module.End K (Fin n → K)} {c : K} (S : TwistSetup h n p A u c)

theorem TwistSetup.piSU_inj (hR : LinearMap.range (u - 1) ≠ ⊥) {g₁ g₂ : SUn h n} (hg₁ : g₁ ∈ S.D)
    (hg₂ : g₂ ∈ S.D) (hπ : piSU h n g₁ = piSU h n g₂) : g₁ = g₂ := by
  have hz : g₁⁻¹ * g₂ ∈ ZSU h n := QuotientGroup.eq.mp hπ
  obtain ⟨d, -, -, hzd⟩ := hz
  have hmem : g₁⁻¹ * g₂ ∈ S.D := mul_mem (inv_mem hg₁) hg₂
  have hfix := (S.mem_D _).mp hmem
  have hd1 : d = 1 := scalar_eq_one_of_fix hR fun w hw => by
    have := hfix w hw
    rwa [hzd] at this
  have : g₁⁻¹ * g₂ = 1 := by
    apply Subtype.ext
    rw [hzd, hd1, map_one]
    rfl
  exact inv_mul_eq_one.mp this

end Inj

section Model

variable {A : SUn h n} {u : Module.End K (Fin n → K)} {c : K} (S : TwistSetup h n p A u c)

theorem TwistSetup.nonempty_eD :
    Nonempty (↥S.D ≃* sesqSpecialUnitaryGroup
      ((idForm h n).domRestrict₁₂ (LinearMap.ker (u - 1)) (LinearMap.ker (u - 1)))) := by
  have : CharP K 2 := h.charP
  set hc := isCompl_ker_range S.hodd S.hup with hchc
  let ψ : SUn h n →* LinearMap.GeneralLinearGroup K (Fin n → K) :=
    (Matrix.GeneralLinearGroup.toLin : GL (Fin n) K ≃* LinearMap.GeneralLinearGroup K (Fin n → K)
      ).toMonoidHom.comp (gramSU h (idGram K n)).subtype
  have hψinj : Function.Injective ψ :=
    Matrix.GeneralLinearGroup.toLin.injective.comp Subtype.val_injective
  have hle : Dfix (idForm h n) hc ≤ ψ.range := by
    intro δ hδ
    obtain ⟨hδS, -⟩ := (mem_Dfix_iff' (idForm_isSymm h n) (idForm_separatingLeft h n) S.hiso
      S.hodd S.hup δ).mp hδ
    have hmem : (Matrix.GeneralLinearGroup.toLin.symm δ : GL (Fin n) K) ∈ gramSU h (idGram K n) :=
      (toLin_mem_sesqSpecialUnitaryGroup_iff h (idGram K n) _).mp (by
        rw [MulEquiv.apply_symm_apply]
        exact hδS)
    exact ⟨⟨_, hmem⟩, by
      change Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.toLin.symm δ) = δ
      exact MulEquiv.apply_symm_apply _ _⟩
  have hmap : S.D.map ψ = Dfix (idForm h n) hc :=
    Subgroup.map_comap_eq_self hle
  let e1 : ↥S.D ≃* ↥(Dfix (idForm h n) hc) :=
    (Subgroup.equivMapOfInjective S.D ψ hψinj).trans (MulEquiv.subgroupCongr hmap)
  let e2 : ↥(Dfix (idForm h n) hc) ≃* sesqSpecialUnitaryGroup
      ((idForm h n).domRestrict₁₂ (LinearMap.ker (u - 1)) (LinearMap.ker (u - 1))) :=
    (Subgroup.equivMapOfInjective _ (extGL hc) (extGL_injective hc)).symm
  exact ⟨e1.trans e2⟩

theorem TwistSetup.lieModel_D (hR : LinearMap.range (u - 1) ≠ ⊥) :
    ∃ (t' : CFSG.Assembly.LowTwoRank.StatedLieTag) (n' : ℕ),
      CFSG.Blueprint.LieModel (↥(S.D.map (piSU h n)) ⧸ Subgroup.center ↥(S.D.map (piSU h n)))
        t' n' 2 F := by
  have : CharP K 2 := h.charP
  obtain ⟨e⟩ := S.nonempty_eD
  have hinj : Function.Injective ((piSU h n).comp S.D.subtype) := fun a b hab =>
    Subtype.ext (S.piSU_inj hR a.2 b.2 hab)
  let e₀ : ↥S.D ≃* ↥(S.D.map (piSU h n)) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr (by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]))
  exact lieModel_of_sesqSU h (fixSpace_isSymm (idForm_isSymm h n))
    (fixSpace_sep (idForm_separatingLeft h n) S.hiso S.hodd S.hup) S.hm S.hq (e₀.symm.trans e)

end Model

end CFSG.RankThree.PartOne.TCU
