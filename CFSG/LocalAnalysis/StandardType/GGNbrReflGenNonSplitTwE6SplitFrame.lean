module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTorus
public import CFSG.LieType.Chevalley.FoldedWeylIdentification
public import CFSG.LieType.Chevalley.GraphFixedRootMonomialQuotient
public import CFSG.Timmesfeld.Orders.ExceptionalTwistedTorus
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4TorusCent
import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
import CFSG.LieType.Chevalley.LangRootArithmeticDet
import CFSG.RankThree.PartOne.TCX.Tri.TorusCentral
import Mathlib.Algebra.Module.ZMod
import CFSG.Certificates.WordSubgroupRel
import CFSG.LieType.Multipliers.ProductKernel
import CFSG.LieType.Multipliers.U42Bridge
import CFSG.LieType.Multipliers.U43Action
import CFSG.LieType.Multipliers.U43BridgeInputs
import CFSG.LieType.Multipliers.U62Action
import CFSG.LieType.Multipliers.U62Bridge
import CFSG.LieType.Multipliers.U62Kernel
import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
import CFSG.Monster.B.Classical.PlaneAut
import CFSG.Monster.B.TwoA.Amalgam.Data
import CFSG.Monster.B.TwoA.Sp8.Par1
import CFSG.Monster.B.TwoA.Unitary.LinThree
import CFSG.RankThree.Chevalley.SteinbergBIE7ThreeA1
import CFSG.RankThree.PartOne.KD4T.Certs
import CFSG.RankThree.PartOne.S10.ThetaContract
import CFSG.RankThree.PartOne.TCX.Tri.PlaneSplit
import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
import CFSG.RankThree.Theta.ThreeComponentOrbitCover
import CFSG.Sporadic.Presentation.Common
import CFSG.Sporadic.SmallOddCore.CheckSpec
import CFSG.YGroups.Y322Central
import Certificates.Certificate10005
import Certificates.Certificate10006
import Certificates.Certificate10007
import Certificates.Certificate10008
import Certificates.Certificate10009
import Certificates.Certificate10010
import Certificates.Certificate10012
import Certificates.Certificate10013
import Certificates.Certificate10014
import Certificates.Certificate10016
import Certificates.Certificate10018
import Certificates.Certificate12041
import Certificates.Certificate12042
import Certificates.Certificate12043
import Certificates.Certificate12044
import Certificates.Certificate12045
import Certificates.Certificate12046
import Certificates.Certificate16015
import Certificates.Certificate16040
import Certificates.Certificate2154
import Certificates.Certificate2157
import Certificates.Certificate2267
import Certificates.Certificate2326
import Certificates.Certificate3006
import Certificates.Certificate3007
import Certificates.Certificate3008
import Certificates.Certificate3063
import Certificates.Certificate3077
import Certificates.Certificate3082
import Certificates.Certificate3083
import Certificates.Certificate8033
import Certificates.Certificate9130

public section

namespace CFSG.StandardType

namespace ExcFrames

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Timmesfeld.ExceptionalOrders CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.GH74.GLS.Stage2.Bender.Thm1

@[expose] noncomputable def twE6SplitTheta (p : ℕ) (s : Fin Tag.F4.rank → ZMod p) :
    Fin TwistTag.E6.tag.rank → ZMod p :=
  TableBExc.redMod .E6 p (TwistTag.foldMap TwistTag.E6 (TableBExc.liftMod .F4 p s))

private def orbitIdx (i : Fin TwistTag.E6.tag.rank) : Fin Tag.F4.rank :=
  ⟨(TwistTag.E6.orbitIndex i).val, (TwistTag.E6.orbitIndex i).isLt⟩

private theorem foldMap_apply_E6 (u : Fin Tag.F4.rank → ℤ) (i : Fin TwistTag.E6.tag.rank) :
    TwistTag.foldMap TwistTag.E6 u i = u (orbitIdx i) := by
  have h := TwistTag.foldMap_apply_apply TwistTag.E6 u i
  rw [h]
  exact congrArg u (Fin.ext rfl)

private theorem twE6SplitTheta_apply {p : ℕ} [NeZero p] (s : Fin Tag.F4.rank → ZMod p)
    (i : Fin TwistTag.E6.tag.rank) : twE6SplitTheta p s i = s (orbitIdx i) := by
  show ((TwistTag.foldMap TwistTag.E6 (TableBExc.liftMod .F4 p s) i : ℤ) : ZMod p) = s (orbitIdx i)
  rw [foldMap_apply_E6]
  show (((s (orbitIdx i)).val : ℤ) : ZMod p) = s (orbitIdx i)
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

theorem twE6SplitTheta_add {p : ℕ} [NeZero p] (s t : Fin Tag.F4.rank → ZMod p) :
    twE6SplitTheta p (s + t) = twE6SplitTheta p s + twE6SplitTheta p t := by
  funext i
  simp only [Pi.add_apply, twE6SplitTheta_apply]

theorem twE6SplitTheta_zero {p : ℕ} [NeZero p] :
    twE6SplitTheta p (0 : Fin Tag.F4.rank → ZMod p) = 0 := by
  funext i
  simp only [Pi.zero_apply, twE6SplitTheta_apply]

theorem twE6SplitTheta_smul {p : ℕ} [NeZero p] (c : ZMod p)
    (s : Fin Tag.F4.rank → ZMod p) :
    twE6SplitTheta p (c • s) = c • twE6SplitTheta p s := by
  let θ : (Fin Tag.F4.rank → ZMod p) →+ (Fin TwistTag.E6.tag.rank → ZMod p) :=
    { toFun := twE6SplitTheta p
      map_zero' := twE6SplitTheta_zero
      map_add' := twE6SplitTheta_add }
  exact ZMod.map_smul θ c s

private theorem twE6SplitTheta_perm {p : ℕ} [NeZero p] (s : Fin Tag.F4.rank → ZMod p)
    (i : Fin TwistTag.E6.tag.rank) :
    twE6SplitTheta p s (TwistTag.E6.perm i) = twE6SplitTheta p s i := by
  rw [twE6SplitTheta_apply, twE6SplitTheta_apply]
  congr 1
  revert i
  decide

theorem twE6SplitTheta_injective {p : ℕ} [NeZero p] :
    Function.Injective (twE6SplitTheta p) := by
  intro s t h
  have key : ∀ a : Fin Tag.F4.rank, ∃ i : Fin TwistTag.E6.tag.rank, orbitIdx i = a := by
    decide
  funext a
  obtain ⟨i, hi⟩ := key a
  have := congrFun h i
  rwa [twE6SplitTheta_apply, twE6SplitTheta_apply, hi] at this

private theorem redMod_foldMap_congr {p : ℕ} {u v : Fin Tag.F4.rank → ℤ}
    (h : TableBExc.redMod .F4 p u = TableBExc.redMod .F4 p v) :
    TableBExc.redMod TwistTag.E6.tag p (TwistTag.foldMap TwistTag.E6 u) =
      TableBExc.redMod TwistTag.E6.tag p (TwistTag.foldMap TwistTag.E6 v) := by
  funext i
  have := congrFun h (orbitIdx i)
  simp only [TableBExc.redMod] at this ⊢
  rw [foldMap_apply_E6, foldMap_apply_E6]
  exact this



private def orbitRep (a : Fin Tag.F4.rank) : Fin TwistTag.E6.tag.rank :=
  if a.val = 0 then ⟨0, by decide⟩ else if a.val = 1 then ⟨2, by decide⟩
    else if a.val = 2 then ⟨3, by decide⟩ else ⟨1, by decide⟩

private theorem exists_twE6SplitTheta_eq {p : ℕ} [NeZero p] {y : Fin TwistTag.E6.tag.rank → ZMod p}
    (hy : ∀ i, y (TwistTag.E6.perm i) = y i) : ∃ s, twE6SplitTheta p s = y := by
  have key : ∀ i : Fin TwistTag.E6.tag.rank,
      orbitRep (orbitIdx i) = i ∨ orbitRep (orbitIdx i) = TwistTag.E6.perm i := by decide
  refine ⟨fun a => y (orbitRep a), funext fun i => ?_⟩
  rw [twE6SplitTheta_apply]
  rcases key i with h | h
  · exact congrArg y h
  · exact (congrArg y h).trans (hy i)

private theorem frameCoord_comp_perm {p : ℕ} (y : Fin TwistTag.E6.tag.rank → ZMod p)
    (i : Fin TwistTag.E6.tag.rank) :
    frameCoord TwistTag.E6.tag p (fun j => y (TwistTag.E6.perm j)) i =
      frameCoord TwistTag.E6.tag p y (TwistTag.E6.perm i) := by
  simp only [frameCoord]
  rw [← Equiv.sum_comp TwistTag.E6.perm
    (fun j => ((TwistTag.E6.tag.symmetrizedCartan (TwistTag.E6.perm i) j : ℤ) : ZMod p) * y j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hS : TwistTag.E6.tag.symmetrizedCartan i j =
      TwistTag.E6.tag.symmetrizedCartan (TwistTag.E6.perm i) (TwistTag.E6.perm j) := by
    fin_cases i <;> fin_cases j <;> decide
  rw [hS]

theorem torusAct_twE6SplitTheta
    {p : ℕ} [NeZero p] (w : relWeylTwist TwistTag.E6)
    (s : Fin Tag.F4.rank → ZMod p) :
    TableBExc.torusAct TwistTag.E6.tag p w.1 (twE6SplitTheta p s) =
      twE6SplitTheta p (TableBExc.torusAct .F4 p (foldedWeylEquiv TwistTag.E6 w) s) := by
  set X : Fin TwistTag.E6.tag.rank → ℤ :=
    TwistTag.foldMap TwistTag.E6 (TableBExc.liftMod .F4 p s) with hX
  have h1 : TableBExc.torusAct TwistTag.E6.tag p w.1 (twE6SplitTheta p s) =
      TableBExc.redMod TwistTag.E6.tag p (w.1 • X) :=
    TableBExc.redMod_smul_eq (τ := TwistTag.E6.tag) (p := p) _ (TableBExc.redMod_liftMod _)
  have h2 : w.1 • X = TwistTag.foldMap TwistTag.E6
      ((show WeylGroup Tag.F4 from foldedWeylEquiv TwistTag.E6 w) • TableBExc.liftMod .F4 p s) :=
    smul_foldMap_foldedWeylEquiv (t := TwistTag.E6) w _
  rw [h1, h2]
  exact redMod_foldMap_congr (TableBExc.redMod_liftMod _).symm


theorem torusCoordHom_zetaVec_E6
    {K : Type} [Field K] {p : ℕ} [NeZero p] {ζ : Kˣ}
    (hζ : ζ ^ p = 1) (x : Fin TwistTag.E6.tag.rank → ZMod p) :
    ((torusCoordHom TwistTag.E6.tag K (TableBExc.E6Three.zetaVec ζ hζ x) :
        torusGroup TwistTag.E6.tag K) : ModGL TwistTag.E6.tag K) =
      frameDiag (τ := TwistTag.E6.tag) ζ hζ x := by
  rw [CFSG.RankThree.PartOne.TCX.Tri.torusCoordHom_eq_rootDiagUnit, frameDiag]
  congr 1
  funext j
  simp only [zpowMatrix, MonoidHom.coe_mk, OneHom.coe_mk, TableBExc.E6Three.zetaVec, frameCoord]
  rw [ofAdd_sum, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [TableBExc.E6Three.zmodPowHom_zpow]
  have hsymm : TwistTag.E6.tag.symmetrizedCartan = TwistTag.E6.tag.cartan := by
    rw [Tag.symmetrizedCartan]
    exact one_mul _
  have hc : TwistTag.E6.tag.cartan j i = TwistTag.E6.tag.cartan i j := by
    fin_cases i <;> fin_cases j <;> rfl
  rw [hsymm, hc]

theorem frameDiag_twE6SplitTheta_mem
    {K : Type} [Field K] {σ : K →+* K} {p : ℕ} [NeZero p]
    {ζ : Kˣ} (hζ : ζ ^ p = 1) (hζσ : σ (ζ : K) = ζ) (s : Fin Tag.F4.rank → ZMod p) :
    frameDiag (τ := TwistTag.E6.tag) ζ hζ (twE6SplitTheta p s) ∈
      graphFixedRootGroup TwistTag.E6 K σ := by
  refine compatTorus_le_graphFixedRootGroup (t := TwistTag.E6) (K := K) σ
    ((mem_compatTorus σ).2
      ⟨fun i => ζ ^ (twE6SplitTheta p s i).val, (mem_compatSubgroup σ).2 fun i => ?_,
        torusCoordHom_zetaVec_E6 hζ _⟩)
  have hperm : twE6SplitTheta p s (TwistTag.E6.perm i) = twE6SplitTheta p s i :=
    twE6SplitTheta_perm s i
  rw [hperm]
  refine Units.ext ?_
  change ((ζ ^ (twE6SplitTheta p s i).val : Kˣ) : K) = σ ((ζ ^ (twE6SplitTheta p s i).val : Kˣ) : K)
  rw [Units.val_pow_eq_pow_val, map_pow, hζσ]

@[expose] noncomputable def twE6SplitFrameHom
    {K : Type} [Field K] (σ : K →+* K) {p : ℕ}
    [Fact p.Prime] (ζ : Kˣ) (hζ : ζ ^ p = 1) (hζσ : σ (ζ : K) = ζ) :
    Multiplicative (Fin Tag.F4.rank → ZMod p) →* ↥(graphFixedRootGroup TwistTag.E6 K σ) where
  toFun s := ⟨frameDiag (τ := TwistTag.E6.tag) ζ hζ (twE6SplitTheta p (Multiplicative.toAdd s)),
    frameDiag_twE6SplitTheta_mem hζ hζσ _⟩
  map_one' := Subtype.ext (by
    change frameDiag (τ := TwistTag.E6.tag) ζ hζ (twE6SplitTheta p 0) = 1
    rw [twE6SplitTheta_zero, frameDiag_zero])
  map_mul' s t := Subtype.ext (by
    change frameDiag (τ := TwistTag.E6.tag) ζ hζ
        (twE6SplitTheta p (Multiplicative.toAdd s + Multiplicative.toAdd t)) =
      frameDiag (τ := TwistTag.E6.tag) ζ hζ (twE6SplitTheta p (Multiplicative.toAdd s)) *
        frameDiag (τ := TwistTag.E6.tag) ζ hζ (twE6SplitTheta p (Multiplicative.toAdd t))
    rw [twE6SplitTheta_add, frameDiag_add])

theorem twE6SplitFrameHom_apply
    {K : Type} [Field K] (σ : K →+* K) {p : ℕ} [Fact p.Prime]
    {ζ : Kˣ} (hζ : ζ ^ p = 1) (hζσ : σ (ζ : K) = ζ) (s : Fin Tag.F4.rank → ZMod p) :
    ((twE6SplitFrameHom σ ζ hζ hζσ (Multiplicative.ofAdd s) :
        ↥(graphFixedRootGroup TwistTag.E6 K σ)) : ModGL TwistTag.E6.tag K) =
      frameDiag (τ := TwistTag.E6.tag) ζ hζ (twE6SplitTheta p s) := rfl

theorem twE6SplitFrameHom_injective
    {K : Type} [Field K] (σ : K →+* K) {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) (hζσ : σ (ζ : K) = ζ) :
    Function.Injective (twE6SplitFrameHom σ ζ hζ hζσ) := by
  have hdet : IsUnit ((TwistTag.E6.tag.symmetrizedCartan.det : ℤ) : ZMod p) := by
    have hsymm : TwistTag.E6.tag.symmetrizedCartan = TwistTag.E6.tag.cartan := by
      rw [Tag.symmetrizedCartan]
      exact one_mul _
    have h3 : TwistTag.E6.tag.cartan.det = 3 := det_cartan_E6
    rw [hsymm, h3, isUnit_iff_ne_zero, Ne, show ((3 : ℤ) : ZMod p) = ((3 : ℕ) : ZMod p) by simp,
      ZMod.natCast_eq_zero_iff]
    intro h
    have := Nat.le_of_dvd (by norm_num) h
    omega
  intro s t hst
  exact Multiplicative.toAdd.injective (twE6SplitTheta_injective
    (frameDiag_injective hζo hζ hdet (congrArg Subtype.val hst)))

theorem twE6SplitFrameHom_conj
    {K : Type} [Field K] (σ : K →+* K) {p : ℕ} [Fact p.Prime]
    {ζ : Kˣ} (hζ : ζ ^ p = 1) (hζσ : σ (ζ : K) = ζ)
    {x : ↥(graphFixedRootGroup TwistTag.E6 K σ)}
    (hx : (x : ModGL TwistTag.E6.tag K) ∈ graphFixedRootMonomial TwistTag.E6 K σ)
    (s : Fin Tag.F4.rank → ZMod p) :
    x * twE6SplitFrameHom σ ζ hζ hζσ (Multiplicative.ofAdd s) * x⁻¹ =
      twE6SplitFrameHom σ ζ hζ hζσ (Multiplicative.ofAdd (TableBExc.torusAct .F4 p
        (foldedWeylEquiv TwistTag.E6
          ⟨graphFixedRootWeylHom TwistTag.E6 K σ ⟨(x : ModGL TwistTag.E6.tag K), hx⟩,
            (graphFixedRootWeylHom_range TwistTag.E6 K σ).le
              ⟨⟨(x : ModGL TwistTag.E6.tag K), hx⟩, rfl⟩⟩) s)) := by
  apply Subtype.ext
  let n : ↥(graphFixedRootMonomial TwistTag.E6 K σ) := ⟨(x : ModGL TwistTag.E6.tag K), hx⟩
  obtain ⟨t, htT, ht_eq⟩ := graphFixedRootMonomial_eq_canonicalRep_mul_torus TwistTag.E6 σ n
  set w : WeylGroup TwistTag.E6.tag := graphFixedRootWeylHom TwistTag.E6 K σ n with hwdef
  have hwmem : w ∈ relWeylTwist TwistTag.E6 :=
    (graphFixedRootWeylHom_range TwistTag.E6 K σ).le ⟨n, rfl⟩
  set nw : ModGL TwistTag.E6.tag K := canonicalRep (coxeterSystem TwistTag.E6.tag) K w
  set d : ModGL TwistTag.E6.tag K := frameDiag (τ := TwistTag.E6.tag) ζ hζ (twE6SplitTheta p s)
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup htT
  have hcomm : t * d = d * t := by
    rw [hb]
    change rootDiagUnit _ b *
        rootDiagUnit _ _ =
      rootDiagUnit _ _ *
        rootDiagUnit _ b
    rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
  have hx' : (x : ModGL TwistTag.E6.tag K) = nw * t := ht_eq
  change (x : ModGL TwistTag.E6.tag K) * d * (x : ModGL TwistTag.E6.tag K)⁻¹ =
    frameDiag (τ := TwistTag.E6.tag) ζ hζ (twE6SplitTheta p (TableBExc.torusAct .F4 p
      (foldedWeylEquiv TwistTag.E6 ⟨w, hwmem⟩) s))
  calc (x : ModGL TwistTag.E6.tag K) * d * (x : ModGL TwistTag.E6.tag K)⁻¹
      = nw * (t * d * t⁻¹) * nw⁻¹ := by rw [hx']; group
    _ = nw * d * nw⁻¹ := by rw [hcomm, mul_inv_cancel_right]
    _ = frameDiag (τ := TwistTag.E6.tag) ζ hζ
          (TableBExc.torusAct TwistTag.E6.tag p w (twE6SplitTheta p s)) :=
        canonicalRep_conj_frameDiag ζ hζ w _
    _ = _ := congrArg (frameDiag (τ := TwistTag.E6.tag) ζ hζ)
          (torusAct_twE6SplitTheta ⟨w, hwmem⟩ s)

theorem exists_realization_twE6Split_weyl
    {K : Type} [Field K] (σ : K →+* K) {p : ℕ} [Fact p.Prime]
    {ζ : Kˣ} (hζ : ζ ^ p = 1) (hζσ : σ (ζ : K) = ζ) (w : WeylGroup Tag.F4) :
    ∃ x : ↥(graphFixedRootGroup TwistTag.E6 K σ), ∀ s : Fin Tag.F4.rank → ZMod p,
      x * twE6SplitFrameHom σ ζ hζ hζσ (Multiplicative.ofAdd s) * x⁻¹ =
        twE6SplitFrameHom σ ζ hζ hζσ
          (Multiplicative.ofAdd (TableBExc.torusAct .F4 p w s)) := by
  let wsub : ↥(relWeylTwist TwistTag.E6) := (foldedWeylEquiv TwistTag.E6).symm w
  have hn : canonicalRep (coxeterSystem TwistTag.E6.tag) K wsub.1 ∈
      graphFixedRootMonomial TwistTag.E6 K σ :=
    canonicalRep_mem_graphFixedRootMonomial TwistTag.E6 K σ wsub.2
  refine ⟨⟨_, graphFixedRootMonomial_le TwistTag.E6 K σ hn⟩, fun s => Subtype.ext ?_⟩
  change canonicalRep (coxeterSystem TwistTag.E6.tag) K wsub.1 *
      frameDiag (τ := TwistTag.E6.tag) ζ hζ (twE6SplitTheta p s) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) K wsub.1)⁻¹ =
    frameDiag (τ := TwistTag.E6.tag) ζ hζ
      (twE6SplitTheta p (TableBExc.torusAct .F4 p w s))
  rw [canonicalRep_conj_frameDiag, torusAct_twE6SplitTheta]
  congr 3
  exact MulEquiv.apply_symm_apply _ _


theorem exists_realization_twE6Split
    {K : Type} [Field K] (σ : K →+* K) {p : ℕ} [Fact p.Prime]
    {ζ : Kˣ} (hζ : ζ ^ p = 1) (hζσ : σ (ζ : K) = ζ) (i : Fin Tag.F4.rank) :
    ∃ x : ↥(graphFixedRootGroup TwistTag.E6 K σ), ∀ s : Fin Tag.F4.rank → ZMod p,
      x * twE6SplitFrameHom σ ζ hζ hζσ (Multiplicative.ofAdd s) * x⁻¹ =
        twE6SplitFrameHom σ ζ hζ hζσ
          (Multiplicative.ofAdd (TableBExc.torusAct .F4 p (simple Tag.F4 i) s)) := by
  exact exists_realization_twE6Split_weyl σ hζ hζσ (simple Tag.F4 i)

theorem frameDiag_twE6SplitTheta_eq_rootDiagUnit {K : Type} [Field K] {p : ℕ} [NeZero p]
    {ζ : Kˣ} (hζ : ζ ^ p = 1) (s : Fin Tag.F4.rank → ZMod p) :
    ∃ c : Fin Tag.E6.rank → Kˣ, (∀ i, c i ^ p = 1) ∧ c ⟨0, by decide⟩ = c ⟨5, by decide⟩ ∧
      c ⟨2, by decide⟩ = c ⟨4, by decide⟩ ∧
      frameDiag (τ := TwistTag.E6.tag) ζ hζ (twE6SplitTheta p s) = rootDiagUnit Tag.E6 c := by
  set y := frameCoord TwistTag.E6.tag p (twE6SplitTheta p s) with hydef
  have hsym : ∀ i, y (TwistTag.E6.perm i) = y i := fun i => by
    rw [hydef, ← frameCoord_comp_perm]
    congr 1
    funext j
    exact twE6SplitTheta_perm s j
  have h05 : y ⟨5, by decide⟩ = y ⟨0, by decide⟩ := hsym ⟨0, by decide⟩
  have h24 : y ⟨4, by decide⟩ = y ⟨2, by decide⟩ := hsym ⟨2, by decide⟩
  refine ⟨fun i => ζ ^ (y i).val, fun i => ?_, ?_, ?_, rfl⟩
  · change (ζ ^ (y i).val) ^ p = 1
    rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  · exact congrArg (fun k : ZMod p => ζ ^ k.val) h05.symm
  · exact congrArg (fun k : ZMod p => ζ ^ k.val) h24.symm

theorem exists_frameDiag_twE6SplitTheta_eq {K : Type} [Field K] {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) {c : Fin Tag.E6.rank → Kˣ}
    (hc : ∀ i, c i ^ p = 1) (h05 : c ⟨0, by decide⟩ = c ⟨5, by decide⟩)
    (h24 : c ⟨2, by decide⟩ = c ⟨4, by decide⟩) :
    ∃ s, frameDiag (τ := TwistTag.E6.tag) ζ hζ (twE6SplitTheta p s) = rootDiagUnit Tag.E6 c := by
  have hdet : IsUnit ((TwistTag.E6.tag.symmetrizedCartan.det : ℤ) : ZMod p) := by
    have hsymm : TwistTag.E6.tag.symmetrizedCartan = TwistTag.E6.tag.cartan := by
      rw [Tag.symmetrizedCartan]
      exact one_mul _
    have h3 : TwistTag.E6.tag.cartan.det = 3 := det_cartan_E6
    rw [hsymm, h3, isUnit_iff_ne_zero, Ne, show ((3 : ℤ) : ZMod p) = ((3 : ℕ) : ZMod p) by simp,
      ZMod.natCast_eq_zero_iff]
    intro h
    have := Nat.le_of_dvd (by norm_num) h
    omega
  have hcp : c ^ p = 1 := funext fun i => by simpa using hc i
  obtain ⟨x, hx⟩ := TableBExc.E6Three.exists_zetaVec_eq (τ := TwistTag.E6.tag) hζo hζ hcp
  obtain ⟨y, hy⟩ :=
    (Finite.injective_iff_surjective.mp (frameCoord_injective (τ := TwistTag.E6.tag) hdet)) x
  have hcsym : ∀ i, c (TwistTag.E6.perm i) = c i := by
    intro i
    fin_cases i
    · exact h05.symm
    · rfl
    · exact h24.symm
    · rfl
    · exact h24
    · exact h05
  have hxsym : (fun i => x (TwistTag.E6.perm i)) = x := by
    apply TableBExc.E6Three.zetaVec_injective (τ := TwistTag.E6.tag) hζo hζ
    funext i
    have := congrFun hx (TwistTag.E6.perm i)
    rw [TableBExc.E6Three.zetaVec_apply] at this ⊢
    rw [this, hcsym i, ← congrFun hx i, TableBExc.E6Three.zetaVec_apply]
  have hysym : ∀ i, y (TwistTag.E6.perm i) = y i := by
    have h1 : frameCoord TwistTag.E6.tag p (fun j => y (TwistTag.E6.perm j)) =
        frameCoord TwistTag.E6.tag p y := by
      funext i
      rw [frameCoord_comp_perm, hy]
      exact congrFun hxsym i
    exact congrFun (frameCoord_injective (τ := TwistTag.E6.tag) hdet h1)
  obtain ⟨s, hs⟩ := exists_twE6SplitTheta_eq hysym
  refine ⟨s, ?_⟩
  rw [hs, frameDiag, hy, hx]
  rfl

end ExcFrames

end CFSG.StandardType

end
