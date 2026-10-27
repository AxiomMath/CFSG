module

public import CFSG.LocalAnalysis.WeakClosure81.FourElevenVocab
public import CFSG.LocalAnalysis.WeakClosure81.FourElevenPGLTwo
public import CFSG.Blueprint.Catalog
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80L3Main
public import CFSG.Quasithin.Vol2.Ch11SecU1L3IX
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalThreeSimilarityGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroProjective
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLOrthData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Cardinality
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Assembly.OddCoreSpan
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.ClassicalGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddL3
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E2Hyp
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.E2TwoNoNStmt
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.Ch11SecU1L3IU
public import CFSG.Quasithin.Vol2.Ch11SecU1L3IV
public import CFSG.Quasithin.Vol2.Ch1Local
public import Certificates.Certificate8026Base
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.LocalAnalysis.WeakClosure81.FourEleven

open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
  CFSG.Quasithin.E2P.Asc80 CFSG.QuasithinUnique.Ch1 CFSG.Quasithin.Vol2.Ch11.SecU1.L3I
open CFSG.ComponentClassification.CatalogueBGraphForm
open CFSG.ComponentClassification.CatalogueBLinearHigherB
open CFSG.ComponentClassification.CatalogueBOrthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalThreeSimilarity
open CFSG.ComponentClassification.Burgoyne.PSL
open scoped MatrixGroups

variable {Q : Type} [Group Q] [Finite Q]

omit [Finite Q] in
theorem exists_mulEquiv_soForm_of_outer {L : Subgroup Q} [L.Normal]
    (hC : centralizer (L : Set Q) = ⊥) (e : ↥L ≃* PSL3 3) {b : Q} (hbL : b ∉ L)
    (hb2 : orderOf b = 2) :
    ∃ R : GL (Fin 3) (ZMod 3), (R : Matrix (Fin 3) (Fin 3) (ZMod 3))ᵀ = R ∧
      Nonempty (↥(L ⊓ centralizer ({b} : Set Q)) ≃*
        ↥(soForm (R : Matrix (Fin 3) (Fin 3) (ZMod 3)))) := by
  obtain ⟨A, hA, hβ⟩ := exists_graph_of_outer (p := 3) (by decide) hC e hbL hb2
  set ψ := e.trans (psl3EquivP 3) with hψ
  set f : projectiveSL 3 (ZMod 3) →* Q := L.subtype.comp ψ.symm.toMonoidHom with hf
  have hfinj : Function.Injective f := L.subtype_injective.comp ψ.symm.injective
  have hfψ : ∀ (x : Q) (hx : x ∈ L), f (ψ ⟨x, hx⟩) = x := fun x hx => by simp [hf]
  set R := ((A⁻¹ : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) with hR
  have hRt : Rᵀ = R := transpose_inv_of_transpose_eq' A hA
  have hRd : R.det ≠ 0 := GeneralLinearGroup.det_ne_zero _
  have hR0 : R ≠ 0 := fun h => hRd (by rw [h]; exact Matrix.det_zero)
  have hfix : ∀ x, b * f x * b⁻¹ = f x ↔
      (LinearFlag.conjAut 3 (ZMod 3) A * LinearFlag.dualAut 3 (ZMod 3)) x = x := by
    intro x
    have hβx : (LinearFlag.conjAut 3 (ZMod 3) A * LinearFlag.dualAut 3 (ZMod 3)) x =
        ψ (MulAut.conjNormal b (ψ.symm x)) := by
      rw [← hβ]
      rfl
    rw [hβx]
    constructor
    · intro h
      apply ψ.symm.injective
      rw [MulEquiv.symm_apply_apply]
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      exact h
    · intro h
      have h1 := congrArg (fun y => ((ψ.symm y : ↥L) : Q)) h
      simp only [MulEquiv.symm_apply_apply, MulAut.conjNormal_apply] at h1
      exact h1
  set F := f.comp (proj 3 (ZMod 3)) with hF
  set H := L ⊓ Subgroup.centralizer ({b} : Set Q) with hH
  have hLC : H = (soForm R).map F := by
    ext g
    constructor
    · rintro ⟨hgL, hgC⟩
      have hgb := Subgroup.mem_centralizer_singleton_iff.mp hgC
      obtain ⟨x, hx⟩ : ∃ x, f x = g := ⟨ψ ⟨g, hgL⟩, hfψ g hgL⟩
      have hxf : (LinearFlag.conjAut 3 (ZMod 3) A * LinearFlag.dualAut 3 (ZMod 3)) x = x := by
        refine (hfix x).mp ?_
        rw [hx]
        calc b * g * b⁻¹ = g * b * b⁻¹ := by rw [hgb]
          _ = g := by group
      obtain ⟨s, hs⟩ := (fixed_iff_mem_range_soProj hA x).mp hxf
      refine ⟨s, s.2, ?_⟩
      have h1 : F s = f (soProj R s) := rfl
      rw [h1, hs, hx]
    · rintro ⟨s, hs, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨(ψ.symm (proj 3 (ZMod 3) s)).2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hx : (LinearFlag.conjAut 3 (ZMod 3) A * LinearFlag.dualAut 3 (ZMod 3))
          (proj 3 (ZMod 3) s) = proj 3 (ZMod 3) s :=
        (fixed_iff_mem_range_soProj hA _).mpr ⟨⟨s, hs⟩, rfl⟩
      have h1 := (hfix _).mpr hx
      have h2 : F s = f (proj 3 (ZMod 3) s) := rfl
      rw [h2]
      calc f (proj 3 (ZMod 3) s) * b = (b * f (proj 3 (ZMod 3) s) * b⁻¹) * b := by rw [h1]
        _ = b * f (proj 3 (ZMod 3) s) := by group
  have hinj : Function.Injective (F.comp (soForm R).subtype) :=
    hfinj.comp (soProj_injective hR0)
  have hrange : (F.comp (soForm R).subtype).range = H := by
    rw [hLC, MonoidHom.range_comp, Subgroup.range_subtype]
  exact ⟨A⁻¹, hRt, ⟨(MulEquiv.subgroupCongr hrange.symm).trans
    (MonoidHom.ofInjective hinj).symm⟩⟩

theorem nonempty_soForm_equiv_pgl2_three
    (R : GL (Fin 3) (ZMod 3)) (hRt : (R : Matrix (Fin 3) (Fin 3) (ZMod 3))ᵀ = R) :
    Nonempty (↥(soForm (R : Matrix (Fin 3) (Fin 3) (ZMod 3))) ≃*
      CFSG.GorensteinWalter.PGL2 (ZMod 3)) := by
  classical
  have hK : ringChar (ZMod 3) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; decide
  have h2 : (2 : ZMod 3) ≠ 0 := Ring.two_ne_zero hK
  have hodd : Odd (Nat.card (ZMod 3)) := odd_card_of_ringChar_ne_two _ hK
  let Q : QuadraticForm (ZMod 3) (Fin 3 → ZMod 3) := matrixQuadraticForm R
  have hQnd : Q.polarBilin.Nondegenerate :=
    polarBilin_matrixQuadraticForm_nondegenerate hK R hRt
  have hdim : Module.finrank (ZMod 3) (Fin 3 → ZMod 3) = 3 :=
    Module.finrank_fin_fun (ZMod 3)
  obtain ⟨-, psi, e, -, -, he'⟩ :=
    finite_odd_orthogonal_three_trace_zero_similarity hodd Q hQnd hdim
  let Φ : TauCeti.QuadraticMap.orthogonalGroup Q ≃*
      (ProjGenLinGroup (Fin 2) (ZMod 3) × rootsOfUnity 2 (ZMod 3)) :=
    e.trans (traceZeroProjectiveEquiv h2).symm
  let π : TauCeti.QuadraticMap.orthogonalGroup Q →*
      ProjGenLinGroup (Fin 2) (ZMod 3) :=
    (MonoidHom.fst _ _).comp Φ.toMonoidHom
  have hker : ∀ g : TauCeti.QuadraticMap.orthogonalGroup Q, π g = 1 →
      ∃ ε : rootsOfUnity 2 (ZMod 3), ∀ v : Fin 3 → ZMod 3,
        g.val v = (ε.val : ZMod 3) • v := by
    intro g hg
    refine ⟨(Φ g).2, ?_⟩
    have hΦg : Φ g = (1, (Φ g).2) := Prod.ext hg rfl
    have heg : e g = traceZeroProjectiveEquiv h2 (1, (Φ g).2) := by
      have h1 := congrArg (traceZeroProjectiveEquiv h2) hΦg
      simp only [Φ, MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at h1
      exact h1
    have hact : ∀ X : traceZeroSubmodule (ZMod 3),
        (e g).val X = (((Φ g).2).val : ZMod 3) • X := by
      intro X
      apply Subtype.ext
      rw [heg, ← ProjGenLinGroup.mk_one, traceZeroProjectiveEquiv_val]
      simp
    intro v
    have h1 : (e.symm (e g)).val v = psi.symm ((e g).val (psi v)) := he' (e g) v
    rw [MulEquiv.symm_apply_apply] at h1
    rw [h1, hact (psi v), map_smul, LinearEquiv.symm_apply_apply]
  let Xof : TauCeti.QuadraticMap.orthogonalGroup Q → GL (Fin 3) (ZMod 3) :=
    fun g => (isoOrthGL hK R hRt g : GL (Fin 3) (ZMod 3))
  have hker_det : ∀ g : TauCeti.QuadraticMap.orthogonalGroup Q, π g = 1 →
      (Xof g : Matrix (Fin 3) (Fin 3) (ZMod 3)).det = 1 → g = 1 := by
    intro g hg hgd
    obtain ⟨ε, hεv⟩ := hker g hg
    have hε2 : (ε.val : ZMod 3) ^ 2 = 1 := (mem_rootsOfUnity' 2 ε.val).mp ε.property
    have hdet : (Xof g : Matrix (Fin 3) (Fin 3) (ZMod 3)).det = (ε.val : ZMod 3) ^ 3 := by
      have hmat : (Xof g : Matrix (Fin 3) (Fin 3) (ZMod 3)) =
          LinearMap.toMatrix'
            (g.val : (Fin 3 → ZMod 3) →ₗ[ZMod 3] (Fin 3 → ZMod 3)) := rfl
      rw [hmat, LinearMap.det_toMatrix']
      have hgm : (g.val : (Fin 3 → ZMod 3) →ₗ[ZMod 3] (Fin 3 → ZMod 3)) =
          (ε.val : ZMod 3) • LinearMap.id := by
        apply LinearMap.ext
        intro v
        simp [hεv v]
      rw [hgm, LinearMap.det_smul, LinearMap.det_id, mul_one, Module.finrank_fin_fun]
    have hd3 : (ε.val : ZMod 3) ^ 3 = 1 := by rw [← hdet]; exact hgd
    have hcube : (ε.val : ZMod 3) ^ 3 = (ε.val : ZMod 3) := by
      calc (ε.val : ZMod 3) ^ 3 = (ε.val : ZMod 3) ^ 2 * (ε.val : ZMod 3) := by ring
        _ = 1 * (ε.val : ZMod 3) := by rw [hε2]
        _ = (ε.val : ZMod 3) := one_mul _
    rw [hcube] at hd3
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    rw [hεv v, hd3, one_smul]
    rfl
  let sGL : ↥(soForm (R : Matrix (Fin 3) (Fin 3) (ZMod 3))) →*
      ↥(isometryGroup 3 (ZMod 3) R) :=
    MonoidHom.codRestrict
      (Matrix.SpecialLinearGroup.toGL.comp
        (soForm (R : Matrix (Fin 3) (Fin 3) (ZMod 3))).subtype)
      (isometryGroup 3 (ZMod 3) R)
      (fun y => (mem_isometryGroup 3 (ZMod 3) R _).mpr y.2)
  let f : ↥(soForm (R : Matrix (Fin 3) (Fin 3) (ZMod 3))) →*
      ProjGenLinGroup (Fin 2) (ZMod 3) :=
    π.comp ((isoOrthGL hK R hRt).symm.toMonoidHom.comp sGL)
  have hf_one : ∀ y, f y = 1 → y = 1 := by
    intro y hy
    have h1 : π ((isoOrthGL hK R hRt).symm (sGL y)) = 1 := hy
    have hdet1 : (Xof ((isoOrthGL hK R hRt).symm (sGL y)) :
        Matrix (Fin 3) (Fin 3) (ZMod 3)).det = 1 := by
      rw [show Xof ((isoOrthGL hK R hRt).symm (sGL y)) =
          (isoOrthGL hK R hRt ((isoOrthGL hK R hRt).symm (sGL y)) :
            GL (Fin 3) (ZMod 3)) from rfl]
      rw [MulEquiv.apply_symm_apply]
      change (Matrix.SpecialLinearGroup.toGL
        (y : Matrix.SpecialLinearGroup (Fin 3) (ZMod 3))).val.det = 1
      rw [← Matrix.GeneralLinearGroup.val_det_apply,
        Matrix.SpecialLinearGroup.coeToGL_det, Units.val_one]
    have hg1 : (isoOrthGL hK R hRt).symm (sGL y) = 1 := hker_det _ h1 hdet1
    have hsgl : sGL y = 1 := by
      have := congrArg (isoOrthGL hK R hRt) hg1
      simpa using this
    have hgl : Matrix.SpecialLinearGroup.toGL
        (y : Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)) = 1 := by
      simpa [sGL] using congrArg
        (fun z : ↥(isometryGroup 3 (ZMod 3) R) => (z : GL (Fin 3) (ZMod 3))) hsgl
    exact Subtype.ext (Matrix.SpecialLinearGroup.toGL_injective (by simpa using hgl))
  have hf_inj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    exact hf_one
  have hcardDom : Nat.card ↥(soForm (R : Matrix (Fin 3) (Fin 3) (ZMod 3))) =
      Nat.card (ZMod 3) * (Nat.card (ZMod 3) ^ 2 - 1) :=
    CFSG.QuasithinUnique.Ch1.card_soForm hK R hRt
  have hcardCod : Nat.card (ProjGenLinGroup (Fin 2) (ZMod 3)) =
      Nat.card (ZMod 3) * (Nat.card (ZMod 3) ^ 2 - 1) :=
    CFSG.GorensteinWalter.pgl2_card_formula (ZMod 3)
  have hbij : Function.Bijective f :=
    (Nat.bijective_iff_injective_and_card f).mpr ⟨hf_inj, by rw [hcardDom, hcardCod]⟩
  exact ⟨MulEquiv.ofBijective f hbij⟩

theorem nonempty_mulEquiv_pgl2_three {L : Subgroup Q} [L.Normal]
    (hC : centralizer (L : Set Q) = ⊥) (hL : LieModel ↥L .PSL 3 3 1) {b : Q} (hbL : b ∉ L)
    (hb2 : orderOf b = 2) :
    Nonempty (↥(L ⊓ centralizer ({b} : Set Q)) ≃* CFSG.GorensteinWalter.PGL2 (ZMod 3)) := by
  have _ : 0 < Nat.card Q := Nat.card_pos
  have hSC : CFSG.Open.StatedClassicalModel ↥L .PSL 3 3 1 :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hL
  obtain ⟨eL⟩ := CFSG.Quasithin.E2P.Asc80.exists_equiv_psl3 (p := 3) hSC
  obtain ⟨R, hRt, ⟨eH⟩⟩ := exists_mulEquiv_soForm_of_outer hC eL hbL hb2
  obtain ⟨eS⟩ := nonempty_soForm_equiv_pgl2_three R hRt
  exact ⟨eH.trans eS⟩

end CFSG.LocalAnalysis.WeakClosure81.FourEleven
