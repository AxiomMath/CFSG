module

public import CFSG.RankThree.GF2n.Stroth80.GuralnickSec119PSU8Proj
import CFSG.RankThree.GF2n.Stroth80.GuralnickSec119PSU8Setup
public import CFSG.RankThree.GF2n.Stroth80.HeringSec119OmegaModelPSU
import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelFixedComm
import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelIrred
import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelSetting
import CFSG.RankThree.GF2n.Stroth80.HeringSec11Action
import CFSG.RankThree.GF2n.Stroth80.HeringSec119OmegaFiltration
import CFSG.RankThree.GF2n.Stroth80.GuralnickSec1110Count
import CFSG.RankThree.GF2n.Stroth80.Sec119Filtration
import CFSG.RankThree.GF2n.Stroth80.Sec38Abelian
import CFSG.RankThree.GF2n.Stroth80.Sec118RT1Form
import CFSG.RankThree.GF2n.Stroth80.HeringSec118RT1Action
import CFSG.RankThree.GF2n.Stroth80.Sec37CommTrans
import CFSG.LocalAnalysis.OddStandard.SmallAltFiveRho
public import CFSG.Blueprint.LieModelAPI
public import CFSG.Certificates.CosetTableShort
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.ClassicalGroups.Symplectic.TransvectionCentralizer
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.GroupTheory.HuppertProduct.Quotient
public import CFSG.GroupTheory.ThompsonIndexTwo
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.GF2n.Smith81.Lin31Back
public import CFSG.RankThree.GF2n.Smith81.LinRank
public import CFSG.RankThree.GF2n.Stroth80.CarterSec11CMIsometry
public import CFSG.RankThree.GF2n.Stroth80.Consumers
public import CFSG.RankThree.GF2n.Stroth80.GlobalModel
public import CFSG.RankThree.GF2n.Stroth80.HeringSec118NotTTransportHom
public import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoBound
public import CFSG.RankThree.GF2n.Stroth80.Sec12Decomp
public import CFSG.RankThree.GF2n.Stroth80.Sec12Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec34Eichler
public import CFSG.RankThree.GF2n.Stroth80.Sec4Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec6Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec7Transport
public import CFSG.RankThree.GF2n.SupIndepDecomp
public import CFSG.RankThree.GF2n.Tim79CentC
public import CFSG.RankThree.GF2n.Tim79CentL
public import CFSG.RankThree.GF2n.Tim79Mod
public import CFSG.RankThree.GF2n.Tim81.Components
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Timmesfeld.RankOne
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate3008
import CFSG.HardMathSupport.Timmesfeld.DFour.FixParity
import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
import CFSG.Permutation.AlternatingAutomorphism
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.OmegaSiegel
open CFSG.HardMathSupport.Kantor79
open CFSG.RankThree.GF2n.Smith81 QuadraticMap Module
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

private theorem Ctx.Xbar_inf_centralizer_eq_bot_of_psu4 (hc : Ctx M Q Z B) {x : ℕ}
    (hx : 2 ≤ x) (hU : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSU 4 2 x) :
    Xbar M Q Z B ⊓ Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)) = ⊥ :=
  CFSG.OddStandard.inf_centralizer_eq_bot_of_center_eq_bot
    (hc.center_Xbar_eq_bot_of_omega hx (m := 3) (Or.inr (Or.inr ⟨rfl, hU⟩)))

private theorem Ctx.mem_L0_of_mem_bar_of_mem_Xbar (hc : Ctx M Q Z B) {x : ℕ}
    (hx : 2 ≤ x) (hU : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSU 4 2 x)
    {L₀ : Subgroup ↥(Xbar M Q Z B)}
    (hcover : ∀ l ∈ bar M Q (LB M Q B), ∃ y : ↥(Xbar M Q Z B), y ∈ L₀ ∧
      (y : Mbar M Q)⁻¹ * l ∈ Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)))
    {l : Mbar M Q} (hl : l ∈ bar M Q (LB M Q B)) (hlX : l ∈ Xbar M Q Z B) :
    (⟨l, hlX⟩ : ↥(Xbar M Q Z B)) ∈ L₀ := by
  obtain ⟨y, hyL0, hyC⟩ := hcover l hl
  have hbot := Ctx.Xbar_inf_centralizer_eq_bot_of_psu4 hc hx hU
  have hprod : (y : Mbar M Q)⁻¹ * l ∈ Xbar M Q Z B :=
    (Xbar M Q Z B).mul_mem ((Xbar M Q Z B).inv_mem y.2) hlX
  have hone : (y : Mbar M Q)⁻¹ * l = 1 := by
    have hmem : (y : Mbar M Q)⁻¹ * l ∈ (⊥ : Subgroup (Mbar M Q)) := by
      rw [← hbot]
      exact Subgroup.mem_inf.mpr ⟨hprod, hyC⟩
    simpa using hmem
  have hy : (y : Mbar M Q) = l := by
    calc (y : Mbar M Q) = (y : Mbar M Q) * ((y : Mbar M Q)⁻¹ * l) := by
          rw [hone, mul_one]
      _ = l := by group
  have hyl : (⟨l, hlX⟩ : ↥(Xbar M Q Z B)) = y := by
    apply Subtype.ext
    exact hy.symm
  rw [hyl]
  exact hyL0

private theorem Ctx.sq_mem_Q_of_mbar_eq_mul (hc : Ctx M Q Z B) {x : ℕ} (hx : 2 ≤ x)
    (hU : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSU 4 2 x)
    {y : ↥(Xbar M Q Z B)} {l : ↥M} (hl : (l : G) ∈ LB M Q B) {c : ↥(H0 M Z)}
    (hcbar : (QuotientGroup.mk' (Q.subgroupOf M) (⟨(c : G), c.2.1⟩ : ↥M) : Mbar M Q) =
      (y : Mbar M Q)⁻¹ * QuotientGroup.mk' (Q.subgroupOf M) l)
    (hC : (y : Mbar M Q)⁻¹ * QuotientGroup.mk' (Q.subgroupOf M) l ∈
      Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))) :
    (c : G) * c ∈ Q := by
  classical
  let lbar : Mbar M Q := QuotientGroup.mk' (Q.subgroupOf M) l
  have hlbar_mem : lbar ∈ bar M Q (LB M Q B) :=
    (Tim37.mk_mem_bar_iff' (M := M) (Q := Q) (S := LB M Q B) le_sup_left l).mpr hl
  have hlbar2 : lbar * lbar = 1 := by
    simpa [pow_two] using hc.isElemAbelian_bar_LB.2 lbar hlbar_mem
  have hcommyl : (y : Mbar M Q)⁻¹ * lbar = lbar * (y : Mbar M Q)⁻¹ := by
    have h := Subgroup.mem_centralizer_iff.mp hC ((y : Mbar M Q)⁻¹)
      ((Xbar M Q Z B).inv_mem y.2)
    rw [mul_assoc] at h
    exact mul_left_cancel h
  have hsq : ((y : Mbar M Q)⁻¹ * lbar) * ((y : Mbar M Q)⁻¹ * lbar) =
      (y : Mbar M Q)⁻¹ * (y : Mbar M Q)⁻¹ := by
    calc ((y : Mbar M Q)⁻¹ * lbar) * ((y : Mbar M Q)⁻¹ * lbar)
        = (y : Mbar M Q)⁻¹ * (lbar * (y : Mbar M Q)⁻¹) * lbar := by group
      _ = (y : Mbar M Q)⁻¹ * ((y : Mbar M Q)⁻¹ * lbar) * lbar := by rw [← hcommyl]
      _ = ((y : Mbar M Q)⁻¹ * (y : Mbar M Q)⁻¹) * (lbar * lbar) := by group
      _ = (y : Mbar M Q)⁻¹ * (y : Mbar M Q)⁻¹ := by rw [hlbar2, mul_one]
  have hmemX : ((y : Mbar M Q)⁻¹ * lbar) * ((y : Mbar M Q)⁻¹ * lbar) ∈ Xbar M Q Z B := by
    rw [hsq]
    exact (Xbar M Q Z B).mul_mem ((Xbar M Q Z B).inv_mem y.2)
      ((Xbar M Q Z B).inv_mem y.2)
  have hmemC : ((y : Mbar M Q)⁻¹ * lbar) * ((y : Mbar M Q)⁻¹ * lbar) ∈
      Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)) :=
    Subgroup.mul_mem _ hC hC
  have hbot := Ctx.Xbar_inf_centralizer_eq_bot_of_psu4 hc hx hU
  have hone : ((y : Mbar M Q)⁻¹ * lbar) * ((y : Mbar M Q)⁻¹ * lbar) = 1 := by
    have hmem : ((y : Mbar M Q)⁻¹ * lbar) * ((y : Mbar M Q)⁻¹ * lbar) ∈
        (⊥ : Subgroup (Mbar M Q)) := by
      rw [← hbot]
      exact Subgroup.mem_inf.mpr ⟨hmemX, hmemC⟩
    simpa using hmem
  have hc2 : QuotientGroup.mk' (Q.subgroupOf M)
      (⟨(c : G) * c, M.mul_mem c.2.1 c.2.1⟩ : ↥M) = 1 := by
    have hprod : (⟨(c : G) * c, M.mul_mem c.2.1 c.2.1⟩ : ↥M) =
        (⟨(c : G), c.2.1⟩ : ↥M) * (⟨(c : G), c.2.1⟩ : ↥M) := by
      ext
      rfl
    rw [hprod, map_mul, hcbar, hone]
  exact (QuotientGroup.eq_one_iff
    (⟨(c : G) * c, M.mul_mem c.2.1 c.2.1⟩ : ↥M)).mp hc2

private theorem Ctx.phi_apply_eq_self_of_sq_mem_Q
    {K' : Type} [Field K'] [Finite K'] [CharP K' 2] {N : Type} [AddCommGroup N]
    [Module K' N] [FiniteDimensional K' N] {QN : QuadraticForm K' N}
    {K₀ : Type} [Field K₀] [Finite K₀] [CharP K₀ 2] {γ : G → K₀}
    {M₀ : Tim79.QuadModel Q Z K₀ γ} (hc : Ctx M Q Z B)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K₀] M₀.E))
    (φker : ∀ h : ↥(H0 M Z), φ h = 1 ↔ (h : G) ∈ Q)
    (ψ : ↥(Xbar M Q Z B) ≃* ↥(elementaryGroup QN))
    {ρV : ↥(elementaryGroup QN) →* (↥(cmComm M Q Z B K₀ γ M₀ φ) ≃ₗ[K₀]
      ↥(cmComm M Q Z B K₀ γ M₀ φ))}
    (hcompat : ∀ s : ↥(XbarH M Q Z B),
      ρV (ψ (xbarHToXbar M Q Z B s)) = cmCommAct hc φ s)
    (hs : OmegaSetting QN (cmCommQf B φ) ρV)
    (htop : commutatorSpace ρV.range = ⊤)
    (hfix : ∀ v : ↥(cmComm M Q Z B K₀ γ M₀ φ), (∀ g, ρV g v = v) → v = 0)
    (hK₂ : 2 < Nat.card K')
    {e f p p' u v : N} (hF : MinusThreeFrame QN e f p p' u v)
    (h8 : finrank K₀ ↥(cmComm M Q Z B K₀ γ M₀ φ) = 8)
    {c : ↥(H0 M Z)}
    (hcC' : (QuotientGroup.mk (⟨(c : G), c.2.1⟩ : ↥M) : Mbar M Q) ∈
      Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)))
    (hcc : (c : G) * c ∈ Q) :
    ∀ w : ↥(cmComm M Q Z B K₀ γ M₀ φ), φ c (w : M₀.E) = (w : M₀.E) := by
  classical
  obtain ⟨τ, hτv, hτcomm, hττ⟩ :=
    hc.exists_cmComm_restrict_of_mem_centralizer φ φker c hcC'
  have hττ1 : τ * τ = 1 := hττ hcc
  have hcommτ : ∀ g : ↥(elementaryGroup QN), τ * ρV g = ρV g * τ := by
    intro g
    obtain ⟨s', hs'⟩ := (ψ.surjective.comp (xbarHToXbar_surjective hc)) g
    have hs'g : ψ (xbarHToXbar M Q Z B s') = g := by
      simpa only [Function.comp_apply] using hs'
    rw [← hs'g, hcompat s']
    exact hτcomm s'
  have hτ1 : τ = 1 :=
    hs.eq_one_of_commute_of_mul_self htop hfix hK₂ hF h8 hττ1 hcommτ
  intro w
  have h1 : τ w = (1 : ↥(cmComm M Q Z B K₀ γ M₀ φ) ≃ₗ[K₀]
    ↥(cmComm M Q Z B K₀ γ M₀ φ)) w := by rw [hτ1]
  have h2 := congrArg (fun z : ↥(cmComm M Q Z B K₀ γ M₀ φ) => (z : M₀.E)) h1
  rw [hτv w] at h2
  simpa using h2

private theorem Ctx.cmCommAct_eq_phi_of_mem_coset
    {K' : Type} [Field K'] [Finite K'] [CharP K' 2] {N : Type} [AddCommGroup N]
    [Module K' N] [FiniteDimensional K' N] {QN : QuadraticForm K' N}
    {K₀ : Type} [Field K₀] [Finite K₀] [CharP K₀ 2] {γ : G → K₀}
    {M₀ : Tim79.QuadModel Q Z K₀ γ}
    (hc : Ctx M Q Z B) {x : ℕ} (hx : 2 ≤ x)
    (hU : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSU 4 2 x)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K₀] M₀.E))
    (φker : ∀ h : ↥(H0 M Z), φ h = 1 ↔ (h : G) ∈ Q)
    (ψ : ↥(Xbar M Q Z B) ≃* ↥(elementaryGroup QN))
    {ρV : ↥(elementaryGroup QN) →* (↥(cmComm M Q Z B K₀ γ M₀ φ) ≃ₗ[K₀]
      ↥(cmComm M Q Z B K₀ γ M₀ φ))}
    (hcompat : ∀ s : ↥(XbarH M Q Z B),
      ρV (ψ (xbarHToXbar M Q Z B s)) = cmCommAct hc φ s)
    (hs : OmegaSetting QN (cmCommQf B φ) ρV)
    (htop : commutatorSpace ρV.range = ⊤)
    (hfix : ∀ v : ↥(cmComm M Q Z B K₀ γ M₀ φ), (∀ g, ρV g v = v) → v = 0)
    (hK₂ : 2 < Nat.card K')
    {e f p p' u v : N} (hF : MinusThreeFrame QN e f p p' u v)
    (h8 : finrank K₀ ↥(cmComm M Q Z B K₀ γ M₀ φ) = 8)
    {y : ↥(Xbar M Q Z B)} {l : ↥M} (hl : (l : G) ∈ LB M Q B)
    (hC : (y : Mbar M Q)⁻¹ * (QuotientGroup.mk' (Q.subgroupOf M) l) ∈
      Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))) :
    ∀ w : ↥(cmComm M Q Z B K₀ γ M₀ φ),
      (ρV (ψ y) w : M₀.E) = φ ⟨(l : G), hc.LB_le_H0 hl⟩ w := by
  classical
  let C : Subgroup (Mbar M Q) :=
    Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))
  let lH : ↥(H0 M Z) := ⟨(l : G), hc.LB_le_H0 hl⟩
  obtain ⟨s, hs_eq⟩ := xbarHToXbar_surjective hc y
  let c : ↥(H0 M Z) := s⁻¹ * lH
  let cM : ↥M := ⟨(c : G), c.2.1⟩
  let sM : ↥M := ⟨((s : ↥(H0 M Z)) : G), ((s : ↥(H0 M Z)).2).1⟩
  let lbar : Mbar M Q := QuotientGroup.mk' (Q.subgroupOf M) l
  have hcM : cM = sM⁻¹ * l := by ext; rfl
  have hcbar : (QuotientGroup.mk' (Q.subgroupOf M) cM : Mbar M Q) =
      (y : Mbar M Q)⁻¹ * lbar := by
    rw [hcM, map_mul, map_inv,
      show (QuotientGroup.mk' (Q.subgroupOf M) sM : Mbar M Q) =
        (xbarHToXbar M Q Z B s : Mbar M Q) from (coe_xbarHToXbar s).symm, hs_eq]
  have hcc : (c : G) * c ∈ Q :=
    Ctx.sq_mem_Q_of_mbar_eq_mul hc hx hU hl (by simpa [cM, lbar] using hcbar) hC
  have hcC' : (QuotientGroup.mk (⟨(c : G), c.2.1⟩ : ↥M) : Mbar M Q) ∈ C := by
    rw [show (QuotientGroup.mk (⟨(c : G), c.2.1⟩ : ↥M) : Mbar M Q) =
      (QuotientGroup.mk' (Q.subgroupOf M) cM : Mbar M Q) from rfl, hcbar]
    exact hC
  have hτapply := Ctx.phi_apply_eq_self_of_sq_mem_Q hc φ φker ψ hcompat hs htop hfix
    hK₂ hF h8 hcC' hcc
  intro w
  have hρ : ρV (ψ y) = cmCommAct hc φ s := by
    rw [← hs_eq]
    exact hcompat s
  have hlH : lH = s * c := by
    rw [show c = s⁻¹ * lH from rfl]
    exact (mul_inv_cancel_left (s : ↥(H0 M Z)) lH).symm
  calc (ρV (ψ y) w : M₀.E) = ((cmCommAct hc φ s) w : M₀.E) := by rw [hρ]
    _ = φ (s : ↥(H0 M Z)) (w : M₀.E) := coe_cmCommAct hc φ s w
    _ = φ lH (w : M₀.E) := by
        rw [hlH, map_mul, LinearEquiv.mul_apply, hτapply w]
    _ = φ ⟨(l : G), hc.LB_le_H0 hl⟩ w := rfl

private theorem Ctx.exists_phi_eq_of_mem_map
    {K' : Type} [Field K'] [Finite K'] [CharP K' 2] {N : Type} [AddCommGroup N]
    [Module K' N] [FiniteDimensional K' N] {QN : QuadraticForm K' N}
    {K₀ : Type} [Field K₀] [Finite K₀] [CharP K₀ 2] {γ : G → K₀}
    {M₀ : Tim79.QuadModel Q Z K₀ γ}
    (hc : Ctx M Q Z B) {x : ℕ} (hx : 2 ≤ x)
    (hU : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSU 4 2 x)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K₀] M₀.E))
    (φker : ∀ h : ↥(H0 M Z), φ h = 1 ↔ (h : G) ∈ Q)
    (ψ : ↥(Xbar M Q Z B) ≃* ↥(elementaryGroup QN))
    {ρV : ↥(elementaryGroup QN) →* (↥(cmComm M Q Z B K₀ γ M₀ φ) ≃ₗ[K₀]
      ↥(cmComm M Q Z B K₀ γ M₀ φ))}
    (hcompat : ∀ s : ↥(XbarH M Q Z B),
      ρV (ψ (xbarHToXbar M Q Z B s)) = cmCommAct hc φ s)
    (hs : OmegaSetting QN (cmCommQf B φ) ρV)
    (htop : commutatorSpace ρV.range = ⊤)
    (hfix : ∀ v : ↥(cmComm M Q Z B K₀ γ M₀ φ), (∀ g, ρV g v = v) → v = 0)
    (hK₂ : 2 < Nat.card K')
    {e f p p' u v : N} (hF : MinusThreeFrame QN e f p p' u v)
    (h8 : finrank K₀ ↥(cmComm M Q Z B K₀ γ M₀ φ) = 8)
    {L₀ : Subgroup ↥(Xbar M Q Z B)}
    (hproj : ∀ y ∈ L₀, ∃ l ∈ bar M Q (LB M Q B),
      (y : Mbar M Q)⁻¹ * l ∈ Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)))
    {g : ↥(elementaryGroup QN)} (hg : g ∈ L₀.map ψ.toMonoidHom) :
    ∃ (y : ↥(Xbar M Q Z B)) (l : ↥M) (hl : (l : G) ∈ LB M Q B), y ∈ L₀ ∧
      ψ y = g ∧
      ∀ w : ↥(cmComm M Q Z B K₀ γ M₀ φ),
        (ρV (ψ y) w : M₀.E) = φ ⟨(l : G), hc.LB_le_H0 hl⟩ w := by
  obtain ⟨y, hyL0, hψy⟩ := Subgroup.mem_map.mp hg
  obtain ⟨lbar, hlbar, hC⟩ := hproj y hyL0
  obtain ⟨l, hlL, hl_eq⟩ := Subgroup.mem_map.mp hlbar
  have hl' : (l : G) ∈ LB M Q B := hlL
  have hC' : (y : Mbar M Q)⁻¹ * (QuotientGroup.mk' (Q.subgroupOf M) l) ∈
      Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)) := by
    rw [hl_eq]
    exact hC
  exact ⟨y, l, hl', hyL0, by simpa using hψy,
    Ctx.cmCommAct_eq_phi_of_mem_coset hc hx hU φ φker ψ hcompat hs htop hfix
      hK₂ hF h8 hl' hC'⟩

private theorem Ctx.rhoV_fix_b_of_mem_map
    {K' : Type} [Field K'] [Finite K'] [CharP K' 2] {N : Type} [AddCommGroup N]
    [Module K' N] [FiniteDimensional K' N] {QN : QuadraticForm K' N}
    {K₀ : Type} [Field K₀] [Finite K₀] [CharP K₀ 2] {γ : G → K₀}
    {M₀ : Tim79.QuadModel Q Z K₀ γ}
    (hc : Ctx M Q Z B) {x : ℕ} (hx : 2 ≤ x)
    (hU : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSU 4 2 x)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K₀] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    (φker : ∀ h : ↥(H0 M Z), φ h = 1 ↔ (h : G) ∈ Q)
    (ψ : ↥(Xbar M Q Z B) ≃* ↥(elementaryGroup QN))
    {ρV : ↥(elementaryGroup QN) →* (↥(cmComm M Q Z B K₀ γ M₀ φ) ≃ₗ[K₀]
      ↥(cmComm M Q Z B K₀ γ M₀ φ))}
    (hcompat : ∀ s : ↥(XbarH M Q Z B),
      ρV (ψ (xbarHToXbar M Q Z B s)) = cmCommAct hc φ s)
    (hs : OmegaSetting QN (cmCommQf B φ) ρV)
    (htop : commutatorSpace ρV.range = ⊤)
    (hfix : ∀ v : ↥(cmComm M Q Z B K₀ γ M₀ φ), (∀ g, ρV g v = v) → v = 0)
    (hK₂ : 2 < Nat.card K')
    {e f p p' u v : N} (hF : MinusThreeFrame QN e f p p' u v)
    (h8 : finrank K₀ ↥(cmComm M Q Z B K₀ γ M₀ φ) = 8)
    {L₀ : Subgroup ↥(Xbar M Q Z B)}
    (hproj : ∀ y ∈ L₀, ∃ l ∈ bar M Q (LB M Q B),
      (y : Mbar M Q)⁻¹ * l ∈ Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)))
    {b : M₀.E} (hbB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K₀, v = s • b)
    (hbV : b ∈ cmComm M Q Z B K₀ γ M₀ φ)
    {g : ↥(elementaryGroup QN)} (hg : g ∈ L₀.map ψ.toMonoidHom) :
    ρV g (⟨b, hbV⟩ : ↥(cmComm M Q Z B K₀ γ M₀ φ)) =
      ⟨b, hbV⟩ := by
  obtain ⟨y, l, hl, hyL0, hψy, hφl⟩ :=
    Ctx.exists_phi_eq_of_mem_map hc hx hU φ φker ψ hcompat hs htop hfix hK₂ hF
      h8 hproj hg
  rw [← hψy]
  refine Subtype.ext ?_
  rw [hφl ⟨b, hbV⟩]
  simpa using Ab38.LB_fix_b hc hbB hφπ ⟨(l : G), hc.LB_le_H0 hl⟩ hl

private theorem Ctx.sub_eq_smul_b_of_mem_map
    {K' : Type} [Field K'] [Finite K'] [CharP K' 2] {N : Type} [AddCommGroup N]
    [Module K' N] [FiniteDimensional K' N] {QN : QuadraticForm K' N}
    {K₀ : Type} [Field K₀] [Finite K₀] [CharP K₀ 2] {γ : G → K₀}
    {M₀ : Tim79.QuadModel Q Z K₀ γ}
    (hc : Ctx M Q Z B) {x : ℕ} (hx : 2 ≤ x)
    (hU : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSU 4 2 x)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K₀] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    (φker : ∀ h : ↥(H0 M Z), φ h = 1 ↔ (h : G) ∈ Q)
    (ψ : ↥(Xbar M Q Z B) ≃* ↥(elementaryGroup QN))
    {ρV : ↥(elementaryGroup QN) →* (↥(cmComm M Q Z B K₀ γ M₀ φ) ≃ₗ[K₀]
      ↥(cmComm M Q Z B K₀ γ M₀ φ))}
    (hcompat : ∀ s : ↥(XbarH M Q Z B),
      ρV (ψ (xbarHToXbar M Q Z B s)) = cmCommAct hc φ s)
    (hs : OmegaSetting QN (cmCommQf B φ) ρV)
    (htop : commutatorSpace ρV.range = ⊤)
    (hfix : ∀ v : ↥(cmComm M Q Z B K₀ γ M₀ φ), (∀ g, ρV g v = v) → v = 0)
    (hK₂ : 2 < Nat.card K')
    {e f p p' u v : N} (hF : MinusThreeFrame QN e f p p' u v)
    (h8 : finrank K₀ ↥(cmComm M Q Z B K₀ γ M₀ φ) = 8)
    {L₀ : Subgroup ↥(Xbar M Q Z B)}
    (hcover : ∀ l ∈ bar M Q (LB M Q B), ∃ y : ↥(Xbar M Q Z B), y ∈ L₀ ∧
      (y : Mbar M Q)⁻¹ * l ∈ Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)))
    (hproj : ∀ y ∈ L₀, ∃ l ∈ bar M Q (LB M Q B),
      (y : Mbar M Q)⁻¹ * l ∈ Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)))
    {b : M₀.E} (hbB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K₀, v = s • b)
    (hbperp : ∀ x ∈ Q, x ∈ Subgroup.centralizer (B : Set G) ↔
      M₀.B (M₀.π x) b = 0)
    (hbV : b ∈ cmComm M Q Z B K₀ γ M₀ φ)
    {g : ↥(elementaryGroup QN)} (hg : g ∈ L₀.map ψ.toMonoidHom) :
    ∀ y : ↥(cmComm M Q Z B K₀ γ M₀ φ),
      polar (cmCommQf B φ) ⟨b, hbV⟩ y = 0 →
      (∀ g' ∈ L₀.map ψ.toMonoidHom, ρV g' (ρV g y - y) = ρV g y - y) →
      ∃ c : K₀, ρV g y - y = c • (⟨b, hbV⟩ : ↥(cmComm M Q Z B K₀ γ M₀ φ)) := by
  intro w hwpol hwfix
  obtain ⟨y, l, hl, hyL0, hψy, hφl⟩ :=
    Ctx.exists_phi_eq_of_mem_map hc hx hU φ φker ψ hcompat hs htop hfix hK₂ hF
      h8 hproj hg
  let lH : ↥(H0 M Z) := ⟨(l : G), hc.LB_le_H0 hl⟩
  have hwb : M₀.B (w : M₀.E) b = 0 := by
    have h := hwpol
    rw [polar_cmCommQf] at h
    rw [Tim79.QuadModel.B_comm, h, neg_zero]
  have hmap : φ lH (w : M₀.E) - (w : M₀.E) ∈ M₀.img (Q ⊓ QB B) :=
    hc.map_sub_one_mem_img_inf_QB φ hφπ hbperp hl (hc.LB_le_H0 hl) hwb
  have hfixL : ∀ (l' : G) (_ : l' ∈ LB M Q B) (hl'H : l' ∈ H0 M Z),
      φ ⟨l', hl'H⟩ (φ lH (w : M₀.E) - (w : M₀.E)) =
        φ lH (w : M₀.E) - (w : M₀.E) := by
    intro l' hl' hl'H
    have hl'bar : (QuotientGroup.mk' (Q.subgroupOf M)
        (⟨l', hc.LB_le_M hl'⟩ : ↥M)) ∈ bar M Q (LB M Q B) :=
      (Tim37.mk_mem_bar_iff' (M := M) (Q := Q) (S := LB M Q B) le_sup_left _).mpr hl'
    obtain ⟨y', hy'L0, hC'⟩ := hcover _ hl'bar
    have hφl' := Ctx.cmCommAct_eq_phi_of_mem_coset hc hx hU φ φker ψ hcompat hs
      htop hfix hK₂ hF h8 hl' hC'
    have hg' : ψ y' ∈ L₀.map ψ.toMonoidHom :=
      Subgroup.mem_map.mpr ⟨y', hy'L0, rfl⟩
    have hcoe := congrArg (fun z : ↥(cmComm M Q Z B K₀ γ M₀ φ) => (z : M₀.E))
      (hwfix (ψ y') hg')
    rw [hφl' (ρV g w - w), ← hψy, Submodule.coe_sub, hφl w] at hcoe
    simpa using hcoe
  obtain ⟨c, hc_eq⟩ := hc.eq_smul_of_fixed_mem_img_inf_QB φ hφπ hbB hmap hfixL
  refine ⟨c, ?_⟩
  rw [← hψy]
  refine Subtype.ext ?_
  change (ρV (ψ y) w : M₀.E) - (w : M₀.E) = c • b
  rw [hφl w, hc_eq]

section Counting

variable {K₀ : Type} [Field K₀] [Finite K₀] [CharP K₀ 2] {γ : G → K₀}
  {M₀ : Tim79.QuadModel Q Z K₀ γ} {K' : Type} [Field K'] [Finite K'] [CharP K' 2]
  {N : Type} [AddCommGroup N] [Module K' N] [FiniteDimensional K' N]
  {QN : QuadraticForm K' N}

private theorem Ctx.exists_counting_facts
    (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) {x : ℕ}
    (hD : GlobalModelData M Q Z γ M₀) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K₀] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    (hK' : Nat.card K' = 2 ^ x) (hx2 : 2 ≤ x)
    (h8 : finrank K₀ ↥(cmComm M Q Z B K₀ γ M₀ φ) = 8)
    {a : G} (haL : a ∈ LB M Q B) (haA : IsA2 Q Z a)
    {s₀ : ↥(XbarH M Q Z B)} (hs₀a : ((s₀ : ↥(H0 M Z)) : G) = a)
    (hs₀ : xbarHToXbar M Q Z B s₀ =
      ⟨(QuotientGroup.mk (⟨a, hc.LB_le_M haL⟩ : ↥M) : Mbar M Q),
        mk_mem_Xbar_of_LB M Q Z B ⟨a, hc.LB_le_M haL⟩ haL haA⟩)
    {b : M₀.E} (hb0 : b ≠ 0) (hbV : b ∈ cmComm M Q Z B K₀ γ M₀ φ)
    (hbB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K₀, v = s • b)
    (ψ : ↥(Xbar M Q Z B) ≃* ↥(elementaryGroup QN))
    {ρV : ↥(elementaryGroup QN) →* (↥(cmComm M Q Z B K₀ γ M₀ φ) ≃ₗ[K₀]
      ↥(cmComm M Q Z B K₀ γ M₀ φ))}
    (hcompat : ∀ s : ↥(XbarH M Q Z B),
      ρV (ψ (xbarHToXbar M Q Z B s)) = cmCommAct hc φ s) :
    ∃ (b₀ : ↥(cmComm M Q Z B K₀ γ M₀ φ)) (hn4 : 4 ≤ n) (hK₂ : 2 < Nat.card K'),
      b₀ = ⟨b, hbV⟩ ∧ b₀ ≠ 0 ∧
      b₀ ∈ movedSpace (ρV (ψ (xbarHToXbar M Q Z B s₀))) ∧
      ((xbarHToXbar M Q Z B s₀ : ↥(Xbar M Q Z B)) : Mbar M Q) ∈ Ebar M Q Z B := by
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hdimE : Module.finrank K₀ M₀.E = 2 * n :=
    hD.finrank_E hw (by rw [hD.card]; omega)
  have hn4 : 4 ≤ n := by
    have hle : 8 ≤ 2 * n := by
      calc 8 = Module.finrank K₀ ↥(cmComm M Q Z B K₀ γ M₀ φ) := h8.symm
        _ ≤ Module.finrank K₀ M₀.E := Submodule.finrank_le _
        _ = 2 * n := hdimE
    omega
  have hK₂ : 2 < Nat.card K' := by
    rw [hK']
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ x := Nat.pow_le_pow_right (by norm_num) hx2
  let b₀ : ↥(cmComm M Q Z B K₀ γ M₀ φ) := ⟨b, hbV⟩
  have hb0' : b₀ ≠ 0 := fun h => hb0 (by simpa [b₀] using congrArg Subtype.val h)
  have hb₀s : b₀ ∈ movedSpace (ρV (ψ (xbarHToXbar M Q Z B s₀))) := by
    rw [hcompat s₀]
    exact Ctx.mem_movedSpace_cmCommAct_of_a2 hc hD φ hφπ hbB hbV s₀
      (hs₀a ▸ haL) (hs₀a ▸ haA)
  have hE : ((xbarHToXbar M Q Z B s₀ : ↥(Xbar M Q Z B)) : Mbar M Q) ∈ Ebar M Q Z B := by
    rw [hs₀]
    refine ⟨⟨⟨a, hc.LB_le_M haL⟩, rfl, haA⟩, 1, ?_⟩
    rw [one_mul, inv_one, mul_one]
    exact Subgroup.mem_map.mpr
      ⟨⟨a, hc.LB_le_M haL⟩, Subgroup.mem_subgroupOf.mpr haL, rfl⟩
  exact ⟨b₀, hn4, hK₂, rfl, hb0', hb₀s, hE⟩

private theorem Ctx.false_of_counting_bound
    (hc : Ctx M Q Z B) {n : ℕ} {x : ℕ} (hx2 : 2 ≤ x)
    (hU : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSU 4 2 x)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K₀] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    (φker : ∀ h : ↥(H0 M Z), φ h = 1 ↔ (h : G) ∈ Q)
    (ψ : ↥(Xbar M Q Z B) ≃* ↥(elementaryGroup QN))
    {ρV : ↥(elementaryGroup QN) →* (↥(cmComm M Q Z B K₀ γ M₀ φ) ≃ₗ[K₀]
      ↥(cmComm M Q Z B K₀ γ M₀ φ))}
    (hcompat : ∀ s : ↥(XbarH M Q Z B),
      ρV (ψ (xbarHToXbar M Q Z B s)) = cmCommAct hc φ s)
    (htop : commutatorSpace ρV.range = ⊤)
    (hfix : ∀ v : ↥(cmComm M Q Z B K₀ γ M₀ φ), (∀ g, ρV g v = v) → v = 0)
    (hK₂ : 2 < Nat.card K') {e f p p' u v : N}
    (hF : MinusThreeFrame QN e f p p' u v)
    (h8 : finrank K₀ ↥(cmComm M Q Z B K₀ γ M₀ φ) = 8)
    {L : Subgroup ↥(elementaryGroup QN)} (hL : IsPGroup 2 L)
    (hLc : ∀ g ∈ L, ∀ g' ∈ L, g * g' = g' * g)
    {L₀ : Subgroup ↥(Xbar M Q Z B)} (hLdef : L = L₀.map ψ.toMonoidHom)
    (hLcard : Nat.card L = Nat.card L₀)
    (hs : OmegaSetting QN (cmCommQf B φ) ρV)
    {s₀ : ↥(XbarH M Q Z B)} (hs₀L : ψ (xbarHToXbar M Q Z B s₀) ∈ L)
    (hL₀cover : ∀ l ∈ bar M Q (LB M Q B), ∃ y : ↥(Xbar M Q Z B), y ∈ L₀ ∧
      (y : Mbar M Q)⁻¹ * l ∈ Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)))
    (hL₀proj : ∀ y ∈ L₀, ∃ l ∈ bar M Q (LB M Q B),
      (y : Mbar M Q)⁻¹ * l ∈ Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)))
    (hL₀card : Nat.card Z ^ (n - 2) ≤ Nat.card L₀)
    {b : M₀.E} (hbV : b ∈ cmComm M Q Z B K₀ γ M₀ φ)
    (hbB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K₀, v = s • b)
    (hbperp : ∀ x ∈ Q, x ∈ Subgroup.centralizer B ↔ M₀.B (M₀.π x) b = 0)
    {b₀ : ↥(cmComm M Q Z B K₀ γ M₀ φ)} (hb₀eq : b₀ = ⟨b, hbV⟩) (hb0' : b₀ ≠ 0)
    (hb₀s : b₀ ∈ movedSpace (ρV (ψ (xbarHToXbar M Q Z B s₀))))
    (hψ : ∀ t : ↥(Xbar M Q Z B), (t : Mbar M Q) ∈ Ebar M Q Z B →
      IsOrthA2 QN ((ψ t : ↥(elementaryGroup QN)) : N ≃ₗ[K'] N))
    (hE : (xbarHToXbar M Q Z B s₀ : Mbar M Q) ∈ Ebar M Q Z B)
    (hK' : Nat.card K' = 2 ^ x) (hx : 2 ^ x = Nat.card Z) (hn4 : 4 ≤ n) : False := by
  have hLb : ∀ g ∈ L, ρV g b₀ = b₀ := by
    intro g hg
    rw [hLdef] at hg
    rw [hb₀eq]
    exact Ctx.rhoV_fix_b_of_mem_map hc hx2 hU φ hφπ φker ψ hcompat hs htop hfix
      hK₂ hF h8 hL₀proj hbB hbV hg
  have hstar : ∀ g ∈ L, ∀ y : ↥(cmComm M Q Z B K₀ γ M₀ φ),
      polar (cmCommQf B φ) b₀ y = 0 →
      (∀ g' ∈ L, ρV g' (ρV g y - y) = ρV g y - y) →
      ∃ c : K₀, ρV g y - y = c • b₀ := by
    intro g hg
    rw [hLdef] at hg ⊢
    intro y hy hfixL
    rw [hb₀eq] at hy ⊢
    exact Ctx.sub_eq_smul_b_of_mem_map hc hx2 hU φ hφπ φker ψ hcompat hs htop
      hfix hK₂ hF h8 hL₀cover hL₀proj hbB hbperp hbV hg y hy hfixL
  have hbound : Nat.card L ≤ Nat.card K' :=
    hs.natCard_le_of_fixed_comm htop hfix hK₂ hF h8 hL hLc hs₀L (hψ _ hE) hb0' hb₀s hLb hstar
  have hcard : Nat.card Z ^ (n - 2) ≤ Nat.card Z :=
    le_trans hL₀card
      (le_trans (le_of_eq hLcard.symm) (le_trans hbound (le_of_eq (by rw [hK', hx]))))
  have hpow : Nat.card Z ^ 2 ≤ Nat.card Z ^ (n - 2) :=
    Nat.pow_le_pow_right (by omega) (Nat.le_sub_of_add_le hn4)
  have hle : Nat.card Z ^ 2 ≤ Nat.card Z := le_trans hpow hcard
  have hlt : Nat.card Z < Nat.card Z ^ 2 := by
    calc Nat.card Z = Nat.card Z * 1 := (mul_one _).symm
      _ < Nat.card Z * Nat.card Z :=
          Nat.mul_lt_mul_of_pos_left (by omega) Nat.card_pos
      _ = Nat.card Z ^ 2 := (pow_two _).symm
  exact absurd hle (not_le.mpr hlt)

private theorem Ctx.false_of_counting_facts
    (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a) {x : ℕ} (hx : 2 ^ x = Nat.card Z)
    (hU : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSU 4 2 x) (hx2 : 2 ≤ x)
    (hD : GlobalModelData M Q Z γ M₀) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K₀] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    (φker : ∀ h : ↥(H0 M Z), φ h = 1 ↔ (h : G) ∈ Q)
    (hK' : Nat.card K' = 2 ^ x) (hndN : (polarBilin QN).Nondegenerate)
    (hdimN : finrank K' N = 2 * 3) {e f p p' u v : N}
    (hF : MinusThreeFrame QN e f p p' u v)
    (ψ : ↥(Xbar M Q Z B) ≃* ↥(elementaryGroup QN))
    (hψ : ∀ t : ↥(Xbar M Q Z B), (t : Mbar M Q) ∈ Ebar M Q Z B →
      IsOrthA2 QN ((ψ t : ↥(elementaryGroup QN)) : N ≃ₗ[K'] N))
    {ρV : ↥(elementaryGroup QN) →* (↥(cmComm M Q Z B K₀ γ M₀ φ) ≃ₗ[K₀]
      ↥(cmComm M Q Z B K₀ γ M₀ φ))}
    (hinj : Function.Injective ρV)
    (hiso : ∀ g v, cmCommQf B φ (ρV g v) = cmCommQf B φ v)
    (hfix : ∀ v : ↥(cmComm M Q Z B K₀ γ M₀ φ), (∀ g, ρV g v = v) → v = 0)
    (htop : commutatorSpace ρV.range = ⊤)
    (hsieg : ∀ s : ↥(XbarH M Q Z B), ((s : ↥(H0 M Z)) : G) ∈ LB M Q B →
      IsA2 Q Z ((s : ↥(H0 M Z)) : G) →
        IsLongRootElement (cmCommQf B φ) (ρV (ψ (xbarHToXbar M Q Z B s))))
    (hcompat : ∀ s : ↥(XbarH M Q Z B),
      ρV (ψ (xbarHToXbar M Q Z B s)) = cmCommAct hc φ s)
    (hnd : ∀ v : ↥(cmComm M Q Z B K₀ γ M₀ φ),
      (∀ w, polar (cmCommQf B φ) v w = 0) → v = 0)
    (h8 : finrank K₀ ↥(cmComm M Q Z B K₀ γ M₀ φ) = 8)
    {a : G} (haL : a ∈ LB M Q B) (haA : IsA2 Q Z a)
    {s₀ : ↥(XbarH M Q Z B)} (hs₀a : ((s₀ : ↥(H0 M Z)) : G) = a)
    (hs₀ : xbarHToXbar M Q Z B s₀ =
      ⟨(QuotientGroup.mk (⟨a, hc.LB_le_M haL⟩ : ↥M) : Mbar M Q),
        mk_mem_Xbar_of_LB M Q Z B ⟨a, hc.LB_le_M haL⟩ haL haA⟩)
    {b : M₀.E} (hbV : b ∈ cmComm M Q Z B K₀ γ M₀ φ)
    (hbB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K₀, v = s • b)
    (hbperp : ∀ x ∈ Q, x ∈ Subgroup.centralizer (B : Set G) ↔
      M₀.B (M₀.π x) b = 0)
    {b₀ : ↥(cmComm M Q Z B K₀ γ M₀ φ)} (hb₀eq : b₀ = ⟨b, hbV⟩) (hb0' : b₀ ≠ 0)
    (hb₀s : b₀ ∈ movedSpace (ρV (ψ (xbarHToXbar M Q Z B s₀))))
    (hE : ((xbarHToXbar M Q Z B s₀ : ↥(Xbar M Q Z B)) : Mbar M Q) ∈ Ebar M Q Z B)
    (hn4 : 4 ≤ n) (hK₂ : 2 < Nat.card K') : False := by
  obtain ⟨L₀, hL₀p, hL₀c, hL₀cover, hL₀proj, hL₀card⟩ :=
    hc.exists_proj_bar_LB_of_psu4 hw hn ha2 hU
  let L : Subgroup ↥(elementaryGroup QN) := L₀.map ψ.toMonoidHom
  have hL : IsPGroup 2 L := hL₀p.map ψ.toMonoidHom
  have hLc : ∀ g ∈ L, ∀ g' ∈ L, g * g' = g' * g := by
    intro g hg g' hg'
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hg'
    rw [← map_mul, ← map_mul, hL₀c y hy y' hy']
  have hLcard : Nat.card L = Nat.card L₀ := Subgroup.card_map_of_injective ψ.injective
  have ht₀bar_mem : (QuotientGroup.mk (⟨a, hc.LB_le_M haL⟩ : ↥M) : Mbar M Q) ∈
      bar M Q (LB M Q B) :=
    (Tim37.mk_mem_bar_iff' (M := M) (Q := Q) (S := LB M Q B) le_sup_left _).mpr haL
  have ht₀X : (QuotientGroup.mk (⟨a, hc.LB_le_M haL⟩ : ↥M) : Mbar M Q) ∈ Xbar M Q Z B :=
    mk_mem_Xbar_of_LB M Q Z B ⟨a, hc.LB_le_M haL⟩ haL haA
  have ht₀L₀ : (⟨(QuotientGroup.mk (⟨a, hc.LB_le_M haL⟩ : ↥M) : Mbar M Q), ht₀X⟩ :
      ↥(Xbar M Q Z B)) ∈ L₀ :=
    Ctx.mem_L0_of_mem_bar_of_mem_Xbar hc hx2 hU hL₀cover ht₀bar_mem ht₀X
  have hs₀L : ψ (xbarHToXbar M Q Z B s₀) ∈ L := by
    rw [hs₀]
    exact Subgroup.mem_map.mpr ⟨_, ht₀L₀, rfl⟩
  have hKcard : Nat.card K' = Nat.card K₀ := by
    rw [hK', hx, hD.card]
  have hs : OmegaSetting QN (cmCommQf B φ) ρV :=
    omegaSetting_of_exists (m := 3) hdimN (by norm_num) hKcard hndN hnd hinj hiso
      ⟨ψ (xbarHToXbar M Q Z B s₀), hψ _ hE,
        hsieg s₀ (hs₀a ▸ haL) (hs₀a ▸ haA)⟩
  exact Ctx.false_of_counting_bound hc hx2 hU φ hφπ φker ψ hcompat htop hfix hK₂ hF h8
    hL hLc rfl hLcard hs hs₀L hL₀cover hL₀proj hL₀card hbV hbB hbperp hb₀eq hb0' hb₀s hψ hE
    hK' hx hn4

end Counting

theorem Ctx.false_of_psu4_eight (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a) {x : ℕ} (hx : 2 ^ x = Nat.card Z)
    (hU : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSU 4 2 x) {X₁ X₂ : Subgroup G}
    (hZX₁ : Z ≤ X₁) (hX₁₂ : X₁ ≤ X₂) (_hX₂Q : X₂ ≤ Q) (hX₁ : ⁅X₁, XbarPre M Q Z B⁆ ≤ Z)
    (hX₂ : X₂ = Z ⊔ ⁅Q, XbarPre M Q Z B⁆) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = Nat.card Z) {X : Subgroup (GL (Fin 8) K)}
    (hX : NaturalRep (ι := Fin 8) K X (XbarPre M Q Z B) X₂ X₁ Q) : False := by
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hx2 : 2 ≤ x := by
    refine (Nat.pow_le_pow_iff_right (a := 2) (by norm_num : 1 < 2)).mp ?_
    calc 2 ^ 2 = 4 := by norm_num
      _ ≤ Nat.card Z := hq4
      _ = 2 ^ x := hx.symm
  obtain ⟨K₀, hK₀field, hK₀fin, hK₀char, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
  haveI : CharP K₀ 2 := hK₀char
  obtain ⟨φ, hφπ, φker, hφQ⟩ := exists_actionHom_H0 hc.hyp hD
  obtain ⟨K', _, _, _, N, _, _, _, QN, hK', hndN, hdimN, ⟨e, f, p, p', u, v, hF⟩, ψ, hψ⟩ :=
    hc.exists_omega_model_psu hx2 hU
  obtain ⟨ρV, hinj, hiso, hfix, htop, hsieg, hcompat⟩ :=
    hc.exists_cmComm_action_of_mulEquiv ha2 hD φ hφπ φker hφQ ψ
  obtain ⟨hnd, -⟩ := hc.cmComm_kantor_instance ha2 hD φ hφπ hφQ
  have hX₁eq : X₁ = Z := hc.eq_Z_of_le_commXbarPre hZX₁ (hX₂ ▸ hX₁₂) hX₁
  have hXnat : NaturalRep (ι := Fin 8) K X (XbarPre M Q Z B)
      (Z ⊔ ⁅Q, XbarPre M Q Z B⁆) Z Q := by
    rwa [hX₂, hX₁eq] at hX
  have h8 : finrank K₀ ↥(cmComm M Q Z B K₀ γ M₀ φ) = 8 :=
    hc.finrank_cmComm_eq_of_naturalRep hD φ hφπ hK hXnat
  obtain ⟨b, hb0, hbV, hbB, hbperp⟩ := hc.exists_b_mem_cmComm hD φ hφπ ha2
  have ⟨a, haL, haA⟩ := ha2
  obtain ⟨s₀, hs₀a, hs₀⟩ :=
    hc.exists_lift_a2 (a := ⟨a, hc.LB_le_M haL⟩) (h := ⟨haL, haA⟩)
  obtain ⟨b₀, hn4, hK₂, hb₀eq, hb0', hb₀s, hE⟩ :=
    Ctx.exists_counting_facts hc hw hD φ hφπ hK' hx2 h8 haL haA hs₀a hs₀ hb0 hbV hbB
      ψ hcompat
  exact Ctx.false_of_counting_facts hc hw hn ha2 hx hU hx2 hD φ hφπ φker hK' hndN hdimN
    hF ψ hψ hinj hiso hfix htop hsieg hcompat hnd h8 haL haA hs₀a hs₀ hbV hbB hbperp
    hb₀eq hb0' hb₀s hE hn4 hK₂

end CFSG.RankThree.GF2n.Stroth80

end
