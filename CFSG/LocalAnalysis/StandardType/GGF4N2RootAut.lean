module

public import CFSG.LinearAlgebra.LinearGroups.Perfect

public import CFSG.GH74.Generic.S1.RAutLin


public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldAction

public import CFSG.LocalAnalysis.StandardType.GGF4N2RootCharts
public import CFSG.LocalAnalysis.StandardType.GGPComponentInvolutionNormalizer
public import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoPSL
public import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoPSLLevi
public import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoPSLCent
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
public import CFSG.Fischer.Aut.Complete
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentAut
public import CFSG.LocalAnalysis.StandardType.GGRootNormInner
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionLinear

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreQuotient
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofCoverLie
public import CFSG.RankThree.SteinbergR3ELinearRegularUnipotent
public import CFSG.ClassicalGroups.SpecialLinear.CyclicRootGroups

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoOmMinus
public import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoOmMinusConj
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerMinus
public import CFSG.LieType.Universal.Spin.Chevalley.Commutator
public import CFSG.HardMathSupport.Foote.Proving.OrderSL4
public import CFSG.Models.PGLOrders

public import CFSG.RankThree.PartOne.AUTSL.Interface

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGAutPSLAux

public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearBasic

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCTFieldTwist

public import CFSG.Quasithin.EmptyFaithful.ModGRed1

public import CFSG.LocalAnalysis.StandardType.GGTPNI1TypeAHelp
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupEightLinear
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CBlockLinA
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalAdjoint
public import CFSG.GH74.Generic.Front.Final
public import CFSG.GH74.Generic.FrontEnd
public import CFSG.GH74.Generic.S1.Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCTField
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotFieldNormalizePSL
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.EmptyFaithful.ModGSolv
public import CFSG.Sporadic.McL

public section

namespace CFSG.StandardType

open Matrix CFSG.RankThree.PartOne.K159
open CFSG.ClassicalGroups.SpecialLinear
open CFSG.LocalAnalysis.ComponentInitial.LinearCover
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F] [CharP F 2] [Finite F]

private lemma mulAut_conj_mul_conj {G : Type} [Group G] (a : MulAut G) (g : G) :
    a * MulAut.conj g = MulAut.conj (a g) * a := by
  ext x
  change a (g * x * g⁻¹) = a g * a x * (a g)⁻¹
  rw [map_mul, map_mul, map_inv]

private lemma centralizer_conj_eq_fixAut {G : Type} [Group G]
    (hZ : Subgroup.center G = ⊥) (r : G) :
    Subgroup.centralizer ({MulAut.conj r} : Set (MulAut G)) =
      CFSG.Fischer.fixAut r := by
  ext a
  rw [Subgroup.mem_centralizer_singleton_iff, CFSG.Fischer.mem_fixAut]
  constructor
  · intro h
    have h1 : MulAut.conj (a r) = MulAut.conj r := by
      have h2 : MulAut.conj (a r) * a = MulAut.conj r * a := by
        calc
          MulAut.conj (a r) * a = a * MulAut.conj r := (mulAut_conj_mul_conj a r).symm
          _ = MulAut.conj r * a := h
      exact mul_right_cancel h2
    exact CFSG.Fischer.mulAutConj_injective hZ h1
  · intro h
    rw [mulAut_conj_mul_conj, h]

private abbrev SL4 (F : Type) [Field F] := SpecialLinearGroup (Fin 4) F
private abbrev PSL4 (F : Type) [Field F] := projectiveSL 4 F

private theorem pCoreOf_fixAut_conj_le_inner
    (hF : 4 ≤ Nat.card F) (T : Subgroup (MulAut (SL4 F)))
    (hInn : CFSG.Fischer.innerAut (SL4 F) ≤ T) (g : SL4 F) :
    CFSG.Open.pCoreOf 2
        (T ⊓ CFSG.Fischer.fixAut (g * AutPSL.rootInv (K := F) (m := 3) (by omega) * g⁻¹)) ≤
      CFSG.Fischer.innerAut (SL4 F) := by
  have hZ : Subgroup.center (SL4 F) = ⊥ :=
    CFSG.RankThree.PartOne.K159.Klein.center_sl4_eq_bot
  have hFbig : 4 ≤ Nat.card F := hF
  let e : PSL4 F ≃* SL4 F := projectiveSLFourEquivSL F
  let ψ0 : PSL4 F →* MulAut (SL4 F) :=
    (MulAut.conj : SL4 F →* MulAut (SL4 F)).comp
      ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom)
  let ψ : PSL4 F →* T :=
    ψ0.codRestrict T (fun p => hInn (show ψ0 p ∈ CFSG.Fischer.innerAut (SL4 F) from
      ⟨MulAut.conj g (e p), rfl⟩))
  have hψ0inj : Function.Injective ψ0 := by
    dsimp [ψ0]
    exact (CFSG.Fischer.mulAutConj_injective hZ).comp
      ((MulAut.conj g).injective.comp e.injective)
  have hψinj : Function.Injective ψ := fun p q h =>
    hψ0inj (Subtype.ext_iff.mp h)
  have hrootPSL : e (KGPSL.rootInvPSL 3 F (by omega)) =
      AutPSL.rootInv (K := F) (m := 3) (by omega) := rfl
  have hψroot : ψ (KGPSL.rootInvPSL 3 F (by omega)) =
      ⟨MulAut.conj (g * AutPSL.rootInv (K := F) (m := 3) (by omega) * g⁻¹),
        hInn ⟨_, rfl⟩⟩ := by
    apply Subtype.ext
    change ψ0 (KGPSL.rootInvPSL 3 F (by omega)) =
      MulAut.conj (g * AutPSL.rootInv (K := F) (m := 3) (by omega) * g⁻¹)
    dsimp [ψ0]
    rw [hrootPSL]
  have hψrange : ψ.range = (CFSG.Fischer.innerAut (SL4 F)).subgroupOf T := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      rw [Subgroup.mem_subgroupOf]
      exact ⟨MulAut.conj g (e p), rfl⟩
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      obtain ⟨s, hs⟩ := CFSG.Fischer.mem_innerAut.mp hx
      let p : PSL4 F := e.symm (g⁻¹ * s * g)
      refine ⟨p, ?_⟩
      apply Subtype.ext
      change ψ0 p = (x : MulAut (SL4 F))
      rw [← hs]
      dsimp [ψ0, p]
      simp only [MulEquiv.apply_symm_apply, MulAut.conj_apply]
      group
  have hC : Subgroup.centralizer (ψ.range : Set T) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    apply Subtype.ext
    have hxcent : (x : MulAut (SL4 F)) ∈
        Subgroup.centralizer ((CFSG.Fischer.innerAut (SL4 F)) : Set (MulAut (SL4 F))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨s, hs⟩ := CFSG.Fischer.mem_innerAut.mp hy
      let p : PSL4 F := e.symm (g⁻¹ * s * g)
      have hψp : ψ p = ⟨MulAut.conj s, hInn ⟨s, rfl⟩⟩ := by
        apply Subtype.ext
        change ψ0 p = MulAut.conj s
        dsimp [ψ0, p]
        simp only [MulEquiv.apply_symm_apply, MulAut.conj_apply]
        group
      have hcomm : ψ p * x = x * ψ p :=
        Subgroup.mem_centralizer_iff.mp hx (ψ p) ⟨p, rfl⟩
      have hcomm' : MulAut.conj s * (x : MulAut (SL4 F)) =
          (x : MulAut (SL4 F)) * MulAut.conj s := by
        simpa [hψp] using congrArg (fun z : T => (z : MulAut (SL4 F))) hcomm
      simpa [hs] using hcomm'
    have hxbot : (x : MulAut (SL4 F)) ∈ (⊥ : Subgroup (MulAut (SL4 F))) := by
      rw [← CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.centralizer_conj_range_eq_bot
        (K := SL4 F) hZ]
      exact hxcent
    exact Subgroup.mem_bot.mp hxbot
  have hψnormal : ψ.range.Normal := by
    rw [hψrange]
    exact (CFSG.Fischer.innerAut_normal (G := SL4 F)).subgroupOf T
  have hnorm : Subgroup.normalizer (ψ.range : Set T) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr hψnormal
  let r : SL4 F := g * AutPSL.rootInv (K := F) (m := 3) (by omega) * g⁻¹
  have hlevi : KGPSL.KGOTwoPSLLeviInput 3 F (by omega) := by
    intro c hc A hA1 hA2 h hh hkey
    exact KGPSL.eq_one_of_conj_levi (m := 3) (K := F) (by omega) (Or.inr hFbig)
      hc hA1 hA2 hh hkey
  have hmain := KGPSL.pCoreOf_le_range_of_rootInv
    (m := 3) (K := F) (by omega) (Or.inr hFbig)
    (Q := KGPSL.radical (K := F) (m := 3) (by omega))
    (KGPSL.centralizer_rootInv_eq_sup (K := F) (m := 3) (by omega))
    (KGPSL.leviFull_le_normalizer_radical (K := F) (m := 3) (by omega))
    (KGPSL.disjoint_radical_leviFull (K := F) (m := 3) (by omega))
    (KGPSL.pCoreOf_centralizer_rootInv (K := F) (m := 3) (by omega))
    hlevi (G := T) hψinj hC
  have hH_eq : (T ⊓ CFSG.Fischer.fixAut r).subgroupOf T =
      Subgroup.centralizer
        ({ψ (KGPSL.rootInvPSL 3 F (by omega))} : Set T) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    have hψroot_coe : (ψ (KGPSL.rootInvPSL 3 F (by omega)) : MulAut (SL4 F)) =
        MulAut.conj r := by
      rw [hψroot]
    constructor
    · rintro ⟨-, hxfix⟩
      have hxcent : (x : MulAut (SL4 F)) ∈
          Subgroup.centralizer ({MulAut.conj r} : Set (MulAut (SL4 F))) := by
        rwa [centralizer_conj_eq_fixAut hZ r]
      have hxcomm := Subgroup.mem_centralizer_singleton_iff.mp hxcent
      apply Subtype.ext
      change (x : MulAut (SL4 F)) * (ψ (KGPSL.rootInvPSL 3 F (by omega)) : MulAut (SL4 F)) =
        (ψ (KGPSL.rootInvPSL 3 F (by omega)) : MulAut (SL4 F)) * (x : MulAut (SL4 F))
      rw [hψroot_coe]
      exact hxcomm
    · intro hxcomm
      refine ⟨x.2, ?_⟩
      have hxcomm' : (x : MulAut (SL4 F)) * MulAut.conj r =
          MulAut.conj r * (x : MulAut (SL4 F)) := by
        simpa [hψroot_coe] using congrArg (fun z : T => (z : MulAut (SL4 F))) hxcomm
      rw [← centralizer_conj_eq_fixAut hZ r]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hxcomm'
  have hmain' : CFSG.Open.pCoreOf 2
        ((T ⊓ CFSG.Fischer.fixAut r).subgroupOf T) ≤ ψ.range := by
    rw [hnorm] at hmain
    simp only [top_inf_eq] at hmain
    rwa [← hH_eq] at hmain
  have h1 : (CFSG.Open.pCoreOf 2 (T ⊓ CFSG.Fischer.fixAut r)).subgroupOf T ≤ ψ.range := by
    simpa only [GGRootNorm.pCoreOf_subgroupOf
      (H := T ⊓ CFSG.Fischer.fixAut r) (K := T) inf_le_left] using hmain'
  have h2 := Subgroup.map_mono h1 (f := T.subtype)
  rw [Subgroup.map_subgroupOf_eq_of_le
      (H := CFSG.Open.pCoreOf 2 (T ⊓ CFSG.Fischer.fixAut r)) (K := T)
      ((GGRootNorm.pCoreOf_le (T ⊓ CFSG.Fischer.fixAut r)).trans inf_le_left),
    hψrange, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hInn] at h2
  exact h2

private theorem conj_tv03_eq_of_conj_tv03_eq {t u : F} (ht : t ≠ 0)
    {s : SL4 F} (h : MulAut.conj s (tv03 t) = tv03 t) :
    MulAut.conj s (tv03 u) = tv03 u := by
  let sM : Matrix (Fin 4) (Fin 4) F := (s : Matrix (Fin 4) (Fin 4) F)
  let sI : Matrix (Fin 4) (Fin 4) F := ((s⁻¹ : SL4 F) : Matrix (Fin 4) (Fin 4) F)
  have hs : sM * sI = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hmat : sM * (1 + Matrix.single 0 3 t) * sI = 1 + Matrix.single 0 3 t := by
    have := congrArg (fun z : SL4 F => (z : Matrix (Fin 4) (Fin 4) F)) h
    simpa [sM, sI, MulAut.conj_apply, coe_tv03, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv] using this
  have hA : sM * Matrix.single 0 3 t * sI = Matrix.single 0 3 t := by
    have h1 : (1 : Matrix (Fin 4) (Fin 4) F) + sM * Matrix.single 0 3 t * sI =
        1 + Matrix.single 0 3 t := by
      calc
        (1 : Matrix (Fin 4) (Fin 4) F) + sM * Matrix.single 0 3 t * sI =
            sM * (1 + Matrix.single 0 3 t) * sI := by
          rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc, hs]
        _ = 1 + Matrix.single 0 3 t := hmat
    exact add_left_cancel h1
  let E : Matrix (Fin 4) (Fin 4) F := Matrix.single 0 3 1
  have hsingle : ∀ x : F, Matrix.single 0 3 x = x • E := by
    intro x
    ext i j
    simp [E, Matrix.single_apply, Matrix.smul_apply]
  have hA' : sM * (t • E) * sI = t • E := by
    simpa only [hsingle, sM, sI] using hA
  have hA1 : sM * E * sI = E := by
    have h2 : t • (sM * E * sI) = t • E := by
      simpa [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, sM, sI] using hA'
    ext i j
    exact mul_left_cancel₀ ht (by
      have := congrFun (congrFun h2 i) j
      simpa [Matrix.smul_apply, smul_eq_mul] using this)
  have hu : sM * Matrix.single 0 3 u * sI = Matrix.single 0 3 u := by
    have := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => u • M) hA1
    simpa only [hsingle, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc] using this
  rw [MulAut.conj_apply]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_tv03]
  dsimp [sM, sI]
  change (s : Matrix (Fin 4) (Fin 4) F) * (1 + Matrix.single 0 3 u) *
      ((s⁻¹ : SL4 F) : Matrix (Fin 4) (Fin 4) F) =
    1 + Matrix.single 0 3 u
  calc
    sM * (1 + Matrix.single 0 3 u) * sI =
        1 + sM * Matrix.single 0 3 u * sI := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc, hs]
    _ = 1 + Matrix.single 0 3 u := by rw [hu]

private theorem pCoreOf_fixAut_le_inner_of_mem_rootR
    (hF : 4 ≤ Nat.card F) (T : Subgroup (MulAut (SL4 F)))
    (hInn : CFSG.Fischer.innerAut (SL4 F) ≤ T)
    {r : SL4 F} (hr : r ∈ rootR F) (hr1 : r ≠ 1) :
    CFSG.Open.pCoreOf 2 (T ⊓ CFSG.Fischer.fixAut r) ≤
      CFSG.Fischer.innerAut (SL4 F) := by
  rw [rootR] at hr
  obtain ⟨t, ht_eq⟩ :=
    (CFSG.ClassicalGroups.SpecialLinear.mem_rootGroup
      (K := F) (hij := (by decide : (0 : Fin 4) ≠ 3))).mp hr
  have ht0 : t ≠ 0 := by
    intro h0
    apply hr1
    rw [← ht_eq, h0, Matrix.SpecialLinearGroup.transvection_coeff_zero]
  obtain ⟨g, hg⟩ := exists_conj_transvection_eq (F := F) (m := 3) (by omega)
    (i := (0 : Fin 4)) (j := (3 : Fin 4)) (by decide) (c := t) ht0
  have hg' : g * r * g⁻¹ =
      AutPSL.rootInv (K := F) (m := 3) (by omega) := by
    calc
      g * r * g⁻¹ = g * Matrix.SpecialLinearGroup.transvection
          (by decide : (0 : Fin 4) ≠ 3) t * g⁻¹ := by
        rw [ht_eq]
      _ = ggInvSL (3 + 1) 1 F := hg
      _ = AutPSL.rootInv (K := F) (m := 3) (by omega) :=
        AutPSL.ggInvSL_eq_rootInv (K := F) (m := 3) (by omega)
  have hcore := pCoreOf_fixAut_conj_le_inner (F := F) hF T hInn g⁻¹
  have hconj : g⁻¹ * AutPSL.rootInv (K := F) (m := 3) (by omega) * g = r := by
    calc
      g⁻¹ * AutPSL.rootInv (K := F) (m := 3) (by omega) * g =
          g⁻¹ * (g * r * g⁻¹) * g := by rw [hg']
      _ = r := by group
  have hcore' : CFSG.Open.pCoreOf 2
      (T ⊓ CFSG.Fischer.fixAut (g⁻¹ * AutPSL.rootInv (K := F) (m := 3) (by omega) * g)) ≤
      CFSG.Fischer.innerAut (SL4 F) := by
    simpa only [inv_inv] using hcore
  rwa [hconj] at hcore'

theorem rootAut_pCoreOf_fixes_rootR
    (hF : 4 ≤ Nat.card F) (T : Subgroup (MulAut (SpecialLinearGroup (Fin 4) F)))
    (hInn : (MulAut.conj : SpecialLinearGroup (Fin 4) F →*
      MulAut (SpecialLinearGroup (Fin 4) F)).range ≤ T)
    {r : SpecialLinearGroup (Fin 4) F} (hr : r ∈ rootR F) (hr1 : r ≠ 1) :
    ∀ a ∈ CFSG.Assembly.pCoreOf 2 (T ⊓ CFSG.Fischer.fixAut r),
      ∀ v ∈ rootR F, a v = v := by
  intro a ha v hv
  have hle := pCoreOf_fixAut_le_inner_of_mem_rootR (F := F) hF T hInn hr hr1
  have hinner : a ∈ CFSG.Fischer.innerAut (SpecialLinearGroup (Fin 4) F) := hle ha
  have hfix : a ∈ CFSG.Fischer.fixAut r := (GGRootNorm.pCoreOf_le _ ha).2
  obtain ⟨s, hs⟩ := CFSG.Fischer.mem_innerAut.mp hinner
  rw [rootR] at hr hv
  obtain ⟨t, ht⟩ :=
    (CFSG.ClassicalGroups.SpecialLinear.mem_rootGroup
      (K := F) (hij := (by decide : (0 : Fin 4) ≠ 3))).mp hr
  obtain ⟨u, hu⟩ :=
    (CFSG.ClassicalGroups.SpecialLinear.mem_rootGroup
      (K := F) (hij := (by decide : (0 : Fin 4) ≠ 3))).mp hv
  have ht0 : t ≠ 0 := by
    intro h0
    apply hr1
    rw [← ht, h0, Matrix.SpecialLinearGroup.transvection_coeff_zero]
  have hfix_apply : MulAut.conj s
      (Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 4) ≠ 3) t) =
      Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 4) ≠ 3) t := by
    have hfix' : a r = r := by simpa [CFSG.Fischer.mem_fixAut] using hfix
    rw [← hs] at hfix'
    rw [← ht] at hfix'
    exact hfix'
  have hfix' : MulAut.conj s (tv03 t) = tv03 t := by
    apply Subtype.ext
    have hmat := congrArg (fun z : SL4 F => (z : Matrix (Fin 4) (Fin 4) F)) hfix_apply
    rw [MulAut.conj_apply]
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_tv03]
    simpa [MulAut.conj_apply, Matrix.SpecialLinearGroup.coe_mul, coe_tv03,
      Matrix.SpecialLinearGroup.transvection_coe] using hmat
  have hfixu := conj_tv03_eq_of_conj_tv03_eq (F := F) (t := t) (u := u) ht0 hfix'
  have hfixu' : MulAut.conj s
      (Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 4) ≠ 3) u) =
      Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 4) ≠ 3) u := by
    apply Subtype.ext
    have hmat := congrArg (fun z : SL4 F => (z : Matrix (Fin 4) (Fin 4) F)) hfixu
    rw [MulAut.conj_apply]
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_tv03]
    simpa [MulAut.conj_apply, Matrix.SpecialLinearGroup.coe_mul, coe_tv03,
      Matrix.SpecialLinearGroup.transvection_coe] using hmat
  rw [← hs]
  rw [← hu]
  exact hfixu'

end CFSG.StandardType

namespace CFSG.StandardType
open Matrix CFSG.RankThree.PartOne.K159
open CFSG.ClassicalGroups.SpecialLinear
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
variable {F : Type} [Field F] [CharP F 2] [Finite F]

private abbrev PSL6 (F : Type) [Field F] := projectiveSL 6 F

private theorem psl6_pCoreOf_fixAut_conj_le_inner
    (hF : Nat.card F = 4) (T : Subgroup (MulAut (PSL6 F)))
    (hInn : CFSG.Fischer.innerAut (PSL6 F) ≤ T) (g : PSL6 F) :
    CFSG.Open.pCoreOf 2
        (T ⊓ CFSG.Fischer.fixAut
          (g * KGPSL.rootInvPSL 5 F (by omega) * g⁻¹)) ≤
      CFSG.Fischer.innerAut (PSL6 F) := by
  have hZ : Subgroup.center (PSL6 F) = ⊥ :=
    CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot
      (n := 6) (k := F) (by omega)
  have hFbig : 4 ≤ Nat.card F := by rw [hF]
  let ψ0 : PSL6 F →* MulAut (PSL6 F) :=
    (MulAut.conj : PSL6 F →* MulAut (PSL6 F)).comp (MulAut.conj g).toMonoidHom
  let ψ : PSL6 F →* T :=
    ψ0.codRestrict T (fun p => hInn (show ψ0 p ∈ CFSG.Fischer.innerAut (PSL6 F) from
      ⟨MulAut.conj g p, rfl⟩))
  have hψ0inj : Function.Injective ψ0 := by
    dsimp [ψ0]
    exact (CFSG.Fischer.mulAutConj_injective hZ).comp (MulAut.conj g).injective
  have hψinj : Function.Injective ψ := fun p q h =>
    hψ0inj (Subtype.ext_iff.mp h)
  have hψroot : ψ (KGPSL.rootInvPSL 5 F (by omega)) =
      ⟨MulAut.conj (g * KGPSL.rootInvPSL 5 F (by omega) * g⁻¹),
        hInn ⟨_, rfl⟩⟩ := by
    apply Subtype.ext
    change ψ0 (KGPSL.rootInvPSL 5 F (by omega)) =
      MulAut.conj (g * KGPSL.rootInvPSL 5 F (by omega) * g⁻¹)
    dsimp [ψ0]
  have hψrange : ψ.range = (CFSG.Fischer.innerAut (PSL6 F)).subgroupOf T := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      rw [Subgroup.mem_subgroupOf]
      exact ⟨MulAut.conj g p, rfl⟩
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      obtain ⟨s, hs⟩ := CFSG.Fischer.mem_innerAut.mp hx
      refine ⟨(MulAut.conj g).symm s, ?_⟩
      apply Subtype.ext
      change ψ0 ((MulAut.conj g).symm s) = (x : MulAut (PSL6 F))
      rw [← hs]
      change ψ0 ((MulAut.conj g).symm s) = MulAut.conj s
      dsimp [ψ0]
      congr 1
      group
  have hC : Subgroup.centralizer (ψ.range : Set T) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    apply Subtype.ext
    have hxcent : (x : MulAut (PSL6 F)) ∈
        Subgroup.centralizer ((CFSG.Fischer.innerAut (PSL6 F)) : Set (MulAut (PSL6 F))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨s, hs⟩ := CFSG.Fischer.mem_innerAut.mp hy
      have hψp : ψ ((MulAut.conj g).symm s) =
          ⟨MulAut.conj s, hInn ⟨s, rfl⟩⟩ := by
        apply Subtype.ext
        change ψ0 ((MulAut.conj g).symm s) = MulAut.conj s
        dsimp [ψ0]
        congr 1
        group
      have hcomm : ψ ((MulAut.conj g).symm s) * x = x * ψ ((MulAut.conj g).symm s) :=
        Subgroup.mem_centralizer_iff.mp hx _ ⟨_, rfl⟩
      have hcomm' : MulAut.conj s * (x : MulAut (PSL6 F)) =
          (x : MulAut (PSL6 F)) * MulAut.conj s := by
        have hc := congrArg (fun z : T => (z : MulAut (PSL6 F))) hcomm
        rw [hψp] at hc
        simpa using hc
      simpa [hs] using hcomm'
    have hxbot : (x : MulAut (PSL6 F)) ∈ (⊥ : Subgroup (MulAut (PSL6 F))) := by
      rw [← CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.centralizer_conj_range_eq_bot
        (K := PSL6 F) hZ]
      exact hxcent
    exact Subgroup.mem_bot.mp hxbot
  have hψnormal : ψ.range.Normal := by
    rw [hψrange]
    exact (CFSG.Fischer.innerAut_normal (G := PSL6 F)).subgroupOf T
  have hnorm : Subgroup.normalizer (ψ.range : Set T) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr hψnormal
  let r : PSL6 F := g * KGPSL.rootInvPSL 5 F (by omega) * g⁻¹
  have hlevi : KGPSL.KGOTwoPSLLeviInput 5 F (by omega) := by
    intro c hc A hA1 hA2 h hh hkey
    exact KGPSL.eq_one_of_conj_levi (m := 5) (K := F) (by omega) (Or.inl (by omega))
      hc hA1 hA2 hh hkey
  have hmain := KGPSL.pCoreOf_le_range_of_rootInv
    (m := 5) (K := F) (by omega) (Or.inl (by omega))
    (Q := KGPSL.radical (K := F) (m := 5) (by omega))
    (KGPSL.centralizer_rootInv_eq_sup (K := F) (m := 5) (by omega))
    (KGPSL.leviFull_le_normalizer_radical (K := F) (m := 5) (by omega))
    (KGPSL.disjoint_radical_leviFull (K := F) (m := 5) (by omega))
    (KGPSL.pCoreOf_centralizer_rootInv (K := F) (m := 5) (by omega))
    hlevi (G := T) hψinj hC
  have hH_eq : (T ⊓ CFSG.Fischer.fixAut r).subgroupOf T =
      Subgroup.centralizer
        ({ψ (KGPSL.rootInvPSL 5 F (by omega))} : Set T) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    have hψroot_coe : (ψ (KGPSL.rootInvPSL 5 F (by omega)) : MulAut (PSL6 F)) =
        MulAut.conj r := by
      rw [hψroot]
    constructor
    · rintro ⟨-, hxfix⟩
      have hxcent : (x : MulAut (PSL6 F)) ∈
          Subgroup.centralizer ({MulAut.conj r} : Set (MulAut (PSL6 F))) := by
        rw [centralizer_conj_eq_fixAut hZ r]
        exact hxfix
      have hxcomm := Subgroup.mem_centralizer_singleton_iff.mp hxcent
      apply Subtype.ext
      change (x : MulAut (PSL6 F)) *
          (ψ (KGPSL.rootInvPSL 5 F (by omega)) : MulAut (PSL6 F)) =
        (ψ (KGPSL.rootInvPSL 5 F (by omega)) : MulAut (PSL6 F)) *
          (x : MulAut (PSL6 F))
      rw [hψroot_coe]
      exact hxcomm
    · intro hxcomm
      refine ⟨x.2, ?_⟩
      have hxcomm' : (x : MulAut (PSL6 F)) * MulAut.conj r =
          MulAut.conj r * (x : MulAut (PSL6 F)) := by
        simpa [hψroot_coe] using congrArg (fun z : T => (z : MulAut (PSL6 F))) hxcomm
      rw [← centralizer_conj_eq_fixAut hZ r]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hxcomm'
  have hmain' : CFSG.Open.pCoreOf 2
        ((T ⊓ CFSG.Fischer.fixAut r).subgroupOf T) ≤ ψ.range := by
    rw [hnorm] at hmain
    simp only [top_inf_eq] at hmain
    rwa [← hH_eq] at hmain
  have h1 : (CFSG.Open.pCoreOf 2 (T ⊓ CFSG.Fischer.fixAut r)).subgroupOf T ≤ ψ.range := by
    simpa only [GGRootNorm.pCoreOf_subgroupOf
      (H := T ⊓ CFSG.Fischer.fixAut r) (K := T) inf_le_left] using hmain'
  have h2 := Subgroup.map_mono h1 (f := T.subtype)
  rw [Subgroup.map_subgroupOf_eq_of_le
      (H := CFSG.Open.pCoreOf 2 (T ⊓ CFSG.Fischer.fixAut r)) (K := T)
      ((GGRootNorm.pCoreOf_le (T ⊓ CFSG.Fischer.fixAut r)).trans inf_le_left),
    hψrange, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hInn] at h2
  exact h2

end CFSG.StandardType

namespace CFSG.StandardType

open Matrix CFSG.ClassicalGroups.SpecialLinear

variable {F : Type} [Field F] [CharP F 2] [Finite F]

private theorem conj_transvection_eq_of_conj_transvection_eq
    {i j : Fin 6} (hij : i ≠ j) {t u : F} (ht : t ≠ 0)
    {s : SpecialLinearGroup (Fin 6) F}
    (h : MulAut.conj s (SpecialLinearGroup.transvection hij t) =
      SpecialLinearGroup.transvection hij t) :
    MulAut.conj s (SpecialLinearGroup.transvection hij u) =
      SpecialLinearGroup.transvection hij u := by
  let sM : Matrix (Fin 6) (Fin 6) F :=
    (s : Matrix (Fin 6) (Fin 6) F)
  let sI : Matrix (Fin 6) (Fin 6) F :=
    ((s⁻¹ : SpecialLinearGroup (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)
  have hs : sM * sI = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hmat : sM * (1 + Matrix.single i j t) * sI =
      1 + Matrix.single i j t := by
    have := congrArg (fun z : SpecialLinearGroup (Fin 6) F =>
      (z : Matrix (Fin 6) (Fin 6) F)) h
    simpa [sM, sI, MulAut.conj_apply, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv] using this
  have hA : sM * Matrix.single i j t * sI = Matrix.single i j t := by
    have h1 : (1 : Matrix (Fin 6) (Fin 6) F) +
        sM * Matrix.single i j t * sI = 1 + Matrix.single i j t := by
      calc
        (1 : Matrix (Fin 6) (Fin 6) F) + sM * Matrix.single i j t * sI =
            sM * (1 + Matrix.single i j t) * sI := by
          rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc, hs]
        _ = 1 + Matrix.single i j t := hmat
    exact add_left_cancel h1
  let E : Matrix (Fin 6) (Fin 6) F := Matrix.single i j 1
  have hsingle : ∀ x : F, Matrix.single i j x = x • E := by
    intro x
    ext a b
    simp [E, Matrix.single_apply, Matrix.smul_apply]
  have hA' : sM * (t • E) * sI = t • E := by
    simpa only [hsingle, sM, sI] using hA
  have hA1 : sM * E * sI = E := by
    have h2 : t • (sM * E * sI) = t • E := by
      simpa [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, sM, sI] using hA'
    ext a b
    exact mul_left_cancel₀ ht (by
      have := congrFun (congrFun h2 a) b
      simpa [Matrix.smul_apply, smul_eq_mul] using this)
  have hu : sM * Matrix.single i j u * sI = Matrix.single i j u := by
    have := congrArg (fun M : Matrix (Fin 6) (Fin 6) F => u • M) hA1
    simpa only [hsingle, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc] using this
  rw [MulAut.conj_apply]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe]
  dsimp [sM, sI]
  change (s : Matrix (Fin 6) (Fin 6) F) * (1 + Matrix.single i j u) *
      ((s⁻¹ : SpecialLinearGroup (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
    1 + Matrix.single i j u
  calc
    sM * (1 + Matrix.single i j u) * sI =
        1 + sM * Matrix.single i j u * sI := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc, hs]
    _ = 1 + Matrix.single i j u := by rw [hu]

end CFSG.StandardType

namespace CFSG.StandardType

open Matrix CFSG.ClassicalGroups.SpecialLinear
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F] [CharP F 2] [Finite F]

private theorem pCoreOf_fixAut_le_inner_of_mem_projectiveRoot
    (hF : Nat.card F = 4) (i j : Fin 6) (hij : i ≠ j)
    (T : Subgroup (MulAut (PSL6 F)))
    (hInn : CFSG.Fischer.innerAut (PSL6 F) ≤ T)
    {r : PSL6 F} (hr : r ∈ (rootGroup F hij).map (proj 6 F)) (hr1 : r ≠ 1) :
    CFSG.Open.pCoreOf 2 (T ⊓ CFSG.Fischer.fixAut r) ≤
      CFSG.Fischer.innerAut (PSL6 F) := by
  obtain ⟨x, hxroot, hxr⟩ := Subgroup.mem_map.mp hr
  have hx1 : x ≠ 1 := by
    intro hx; apply hr1; rw [← hxr, hx, map_one]
  obtain ⟨t, ht⟩ :=
    (CFSG.ClassicalGroups.SpecialLinear.mem_rootGroup
      (K := F) (hij := hij)).mp hxroot
  have ht0 : t ≠ 0 := by
    intro h0
    apply hx1
    rw [← ht, h0, Matrix.SpecialLinearGroup.transvection_coeff_zero]
  obtain ⟨y, hy⟩ := exists_conj_transvection_eq (F := F) (m := 5) (by omega)
    (i := i) (j := j) hij (c := t) ht0
  have hyproj : proj 6 F y * r * (proj 6 F y)⁻¹ =
      KGPSL.rootInvPSL 5 F (by omega) := by
    have h := congrArg (proj 6 F) hy
    rw [map_mul, map_mul, map_inv, ht, hxr] at h
    calc
      proj 6 F y * r * (proj 6 F y)⁻¹ = proj 6 F (ggInvSL (5 + 1) 1 F) := h
      _ = KGPSL.rootInvPSL 5 F (by omega) := by
        congr 1
        exact AutPSL.ggInvSL_eq_rootInv (K := F) (m := 5) (by omega)
  have hconj : (proj 6 F y)⁻¹ * KGPSL.rootInvPSL 5 F (by omega) * (proj 6 F y) = r := by
    calc
      (proj 6 F y)⁻¹ * KGPSL.rootInvPSL 5 F (by omega) * (proj 6 F y) =
          (proj 6 F y)⁻¹ * (proj 6 F y * r * (proj 6 F y)⁻¹) * (proj 6 F y) := by
        rw [hyproj]
      _ = r := by group
  have hcore := psl6_pCoreOf_fixAut_conj_le_inner (F := F) hF T hInn (proj 6 F y)⁻¹
  have hcore' : CFSG.Open.pCoreOf 2
      (T ⊓ CFSG.Fischer.fixAut
        ((proj 6 F y)⁻¹ * KGPSL.rootInvPSL 5 F (by omega) * (proj 6 F y))) ≤
      CFSG.Fischer.innerAut (PSL6 F) := by
    simpa only [inv_inv] using hcore
  rwa [hconj] at hcore'

end CFSG.StandardType

namespace CFSG.StandardType

open Matrix CFSG.ClassicalGroups.SpecialLinear
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F] [CharP F 2] [Finite F]

theorem psl6_rootAut_pCoreOf_fixes
    (hF : Nat.card F = 4) (i j : Fin 6) (hij : i ≠ j)
    (T : Subgroup (MulAut (projectiveSL 6 F)))
    (hInn : (MulAut.conj : projectiveSL 6 F →* MulAut (projectiveSL 6 F)).range ≤ T)
    {r : projectiveSL 6 F} (hr : r ∈ (rootGroup F hij).map (proj 6 F)) (hr1 : r ≠ 1) :
    ∀ a ∈ CFSG.Assembly.pCoreOf 2 (T ⊓ CFSG.Fischer.fixAut r),
      ∀ v ∈ (rootGroup F hij).map (proj 6 F), a v = v := by
  intro a ha v hv
  have hle := pCoreOf_fixAut_le_inner_of_mem_projectiveRoot (F := F) hF i j hij T hInn hr hr1
  have hinner : a ∈ CFSG.Fischer.innerAut (projectiveSL 6 F) := hle ha
  have hfix : a ∈ CFSG.Fischer.fixAut r := (GGRootNorm.pCoreOf_le _ ha).2
  obtain ⟨s, hs⟩ := CFSG.Fischer.mem_innerAut.mp hinner
  obtain ⟨x, hxroot, hxr⟩ := Subgroup.mem_map.mp hr
  obtain ⟨y, hyroot, hyr⟩ := Subgroup.mem_map.mp hv
  obtain ⟨t, ht⟩ :=
    (CFSG.ClassicalGroups.SpecialLinear.mem_rootGroup
      (K := F) (hij := hij)).mp hxroot
  obtain ⟨u, hu⟩ :=
    (CFSG.ClassicalGroups.SpecialLinear.mem_rootGroup
      (K := F) (hij := hij)).mp hyroot
  have hx1 : x ≠ 1 := by
    intro hx; apply hr1; rw [← hxr, hx, map_one]
  have ht0 : t ≠ 0 := by
    intro h0
    apply hx1
    rw [← ht, h0, Matrix.SpecialLinearGroup.transvection_coeff_zero]
  have hx2 : x * x = 1 := by
    rw [← ht, ← Matrix.SpecialLinearGroup.transvection_add, CharTwo.add_self_eq_zero,
      Matrix.SpecialLinearGroup.transvection_coeff_zero]
  have hfix_s : MulAut.conj s r = r := by
    have hfix' : a r = r := by simpa [CFSG.Fischer.mem_fixAut] using hfix
    rw [← hs] at hfix'
    exact hfix'
  have hscent : s ∈ Subgroup.centralizer ({r} : Set (projectiveSL 6 F)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := hfix_s
    rw [MulAut.conj_apply] at h
    calc
      s * r = (s * r * s⁻¹) * s := by group
      _ = r * s := by rw [h]
  have hRcard : Nat.card (scalars 6 F) = 3 := by
    rw [CFSG.LocalAnalysis.RankFourTheoremC.card_scalars_eq_gcd (n := 6) (K := F)
      (by norm_num), hF]
    norm_num
  have hRodd : Odd (Nat.card (scalars 6 F)) := by
    rw [hRcard]
    norm_num
  have hmapcent := CFSG.ComponentClassification.UnbalancedLayer.map_centralizer_eq
    (H := SpecialLinearGroup (Fin 6) F) (R := scalars 6 F) hRodd (t := x) hx2
  have hsmap : s ∈ Subgroup.map (QuotientGroup.mk' (scalars 6 F))
      (Subgroup.centralizer ({x} : Set (SpecialLinearGroup (Fin 6) F))) := by
    rw [hmapcent]
    have hxr' : QuotientGroup.mk' (scalars 6 F) x = r := hxr
    simpa [hxr'] using hscent
  obtain ⟨c, hcx, hcs⟩ := Subgroup.mem_map.mp hsmap
  change proj 6 F c = s at hcs
  have hcx_comm : c * x = x * c :=
    Subgroup.mem_centralizer_singleton_iff.mp hcx
  have hc_conj : MulAut.conj c x = x := by
    rw [MulAut.conj_apply, hcx_comm]
    group
  have hc_t : MulAut.conj c (SpecialLinearGroup.transvection hij t) =
      SpecialLinearGroup.transvection hij t := by
    rw [ht]
    exact hc_conj
  have hc_u := conj_transvection_eq_of_conj_transvection_eq (F := F) hij ht0 hc_t
    (u := u)
  have hc_y : MulAut.conj c y = y := by
    rw [← hu]
    exact hc_u
  rw [← hs]
  rw [← hyr]
  calc
    MulAut.conj s (proj 6 F y) = MulAut.conj (proj 6 F c) (proj 6 F y) := by
      rw [hcs]
    _ = proj 6 F (MulAut.conj c y) := by
      simp [MulAut.conj_apply, map_mul]
    _ = proj 6 F y := by rw [hc_y]

end CFSG.StandardType

namespace CFSG.StandardType

section MinusNativeRoot

open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CliffordAlgebra

theorem minusRootAut_pCoreOf_fixes_longRoot {F : Type} [Field F] [Finite F] [CharP F 2]
    {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (T : Subgroup (MulAut (spinGroup (quadMinus 4 F b c))))
    (hInn : (MulAut.conj : spinGroup (quadMinus 4 F b c) →*
      MulAut (spinGroup (quadMinus 4 F b c))).range ≤ T)
    {x : Multiplicative F →* spinGroup (quadMinus 4 F b c)}
    (hx : x = (minusFrame 4 b c).longRoot (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩)
      (by simp) true true)
    {r : spinGroup (quadMinus 4 F b c)} (hr : r ∈ x.range) (hr1 : r ≠ 1) :
    ∀ a ∈ CFSG.Assembly.pCoreOf 2 (T ⊓ CFSG.Fischer.fixAut r),
      ∀ v ∈ x.range, a v = v := by
  let i0 : Fin (4 - 1) := ⟨0, by omega⟩
  let j0 : Fin (4 - 1) := ⟨1, by omega⟩
  have hij0 : i0 ≠ j0 := by simp [i0, j0]
  let S := spinGroup (quadMinus 4 F b c)
  let Q := quadMinus 4 F b c
  let Frm := minusFrame 4 b c
  let A : CliffordAlgebra Q :=
    ι Q (Frm.vec i0 true) * ι Q (Frm.vec j0 true)
  let x0 : S := Frm.longRoot (i := i0) (j := j0) hij0 true true (.ofAdd 1)
  have hZ : Subgroup.center S = ⊥ :=
    PsiDiag.SpinM.center_eq_bot (K := F) (n := 4) (b := b) (c := c) hirr (by norm_num)
  have hInnInj : Function.Injective (MulAut.conj : S →* MulAut S) :=
    CFSG.Fischer.mulAutConj_injective hZ
  obtain ⟨z, hzr⟩ := MonoidHom.mem_range.mp hr
  let t : F := Multiplicative.toAdd z
  have hz : z = Multiplicative.ofAdd t := (ofAdd_toAdd z).symm
  have hr_eq : r = Frm.longRoot (i := i0) (j := j0) hij0 true true (.ofAdd t) := by
    rw [← hzr, hz, hx]
  have ht0 : t ≠ 0 := by
    intro h0
    apply hr1
    rw [hr_eq, h0]
    exact map_one (Frm.longRoot (i := i0) (j := j0) hij0 true true)
  obtain ⟨w, hw⟩ := KGOm.exists_conj_longRoot_std_minus
    (K := F) (n := 4) (b := b) (c := c) (i := i0) (j := j0)
    (by norm_num : 4 ≤ 4) hirr hij0 true true (a := t) ht0
  let ψ0 : S →* MulAut S :=
    (MulAut.conj : S →* MulAut S).comp (MulAut.conj w).toMonoidHom
  let ψ : S →* T := ψ0.codRestrict T (fun s => hInn ⟨w * s * w⁻¹, rfl⟩)
  have hψ0inj : Function.Injective ψ0 := by
    dsimp [ψ0]
    exact hInnInj.comp (MulAut.conj w).injective
  have hψinj : Function.Injective ψ := by
    intro p q hpq
    exact hψ0inj (Subtype.ext_iff.mp hpq)
  have hψroot : (ψ x0 : MulAut S) = MulAut.conj r := by
    change ψ0 x0 = MulAut.conj r
    dsimp [ψ0]
    change MulAut.conj (w * Frm.longRoot (i := i0) (j := j0) hij0 true true (.ofAdd 1) * w⁻¹) =
      MulAut.conj r
    rw [hw, hr_eq]
  have hψrange : ψ.range = (CFSG.Fischer.innerAut S).subgroupOf T := by
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      rw [Subgroup.mem_subgroupOf, CFSG.Fischer.mem_innerAut]
      refine ⟨w * s * w⁻¹, ?_⟩
      change MulAut.conj (w * s * w⁻¹) = ψ0 s
      rfl
    · intro hy
      rw [Subgroup.mem_subgroupOf, CFSG.Fischer.mem_innerAut] at hy
      obtain ⟨u, hu⟩ := hy
      refine ⟨w⁻¹ * u * w, ?_⟩
      apply Subtype.ext
      change MulAut.conj (w * (w⁻¹ * u * w) * w⁻¹) = (y : MulAut S)
      rw [← hu]
      congr 1
      group
  have hψnormal : ψ.range.Normal := by
    rw [hψrange]
    exact (CFSG.Fischer.innerAut_normal (G := S)).subgroupOf T
  have hnorm : Subgroup.normalizer (ψ.range : Set T) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr hψnormal
  have hcent : Subgroup.centralizer ({ψ x0} : Set T) =
      (T ⊓ CFSG.Fischer.fixAut r).subgroupOf T := by
    ext y
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      CFSG.Fischer.mem_fixAut]
    constructor
    · intro hcomm
      refine ⟨y.2, ?_⟩
      have hcomm' : (y : MulAut S) * MulAut.conj r = MulAut.conj r * (y : MulAut S) := by
        have hcast := congrArg (fun u : T => (u : MulAut S)) hcomm
        simpa [hψroot] using hcast
      have hconj : MulAut.conj ((y : MulAut S) r) = MulAut.conj r := by
        rw [← CFSG.Fischer.mul_conj_mul_inv]
        calc (y : MulAut S) * MulAut.conj r * (y : MulAut S)⁻¹ =
            (MulAut.conj r * (y : MulAut S)) * (y : MulAut S)⁻¹ := by rw [hcomm']
          _ = MulAut.conj r := by group
      exact hInnInj hconj
    · rintro ⟨-, hfixr⟩
      have hconj : MulAut.conj ((y : MulAut S) r) = MulAut.conj r := by rw [hfixr]
      have hcomm' : (y : MulAut S) * MulAut.conj r = MulAut.conj r * (y : MulAut S) := by
        rw [← CFSG.Fischer.mul_conj_mul_inv] at hconj
        calc (y : MulAut S) * MulAut.conj r =
            ((y : MulAut S) * MulAut.conj r * (y : MulAut S)⁻¹) * (y : MulAut S) := by group
          _ = MulAut.conj r * (y : MulAut S) := by rw [hconj]
      apply Subtype.ext
      simpa [hψroot] using hcomm'
  have hcent_inner : Subgroup.centralizer (ψ.range : Set T) =
      (Subgroup.centralizer ((CFSG.Fischer.innerAut S) : Set (MulAut S))).subgroupOf T := by
    rw [hψrange]
    ext y
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro hy u hu
      have hmem := hy ⟨u, hInn hu⟩ (Subgroup.mem_subgroupOf.mpr hu)
      exact congrArg (fun v : T => (v : MulAut S)) hmem
    · intro hy u hu
      exact Subtype.ext (hy (u : MulAut S) (Subgroup.mem_subgroupOf.mp hu))
  have hC : Subgroup.centralizer (ψ.range : Set T) = ⊥ := by
    rw [hcent_inner, eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    have hy' : (y : MulAut S) ∈
        Subgroup.centralizer ((CFSG.Fischer.innerAut S) : Set (MulAut S)) :=
      Subgroup.mem_subgroupOf.mp hy
    have hy1 : (y : MulAut S) = 1 :=
      CFSG.Fischer.eq_one_of_commute_innerAut hZ fun s =>
        (hy' (MulAut.conj s) ⟨s, rfl⟩).symm
    simpa using hy1
  have hmain := KGOm.pCoreOf_le_range_of_longRoot_minus
    (K := F) (n := 4) (b := b) (c := c) (hn4 := by norm_num)
    (hirr := hirr) (G := T) (ψ := ψ) hψinj hC
  have hpcore : CFSG.Assembly.pCoreOf 2 ((T ⊓ CFSG.Fischer.fixAut r).subgroupOf T) ≤
      ψ.range := by
    rw [hnorm, hcent] at hmain
    simpa using hmain
  have hle : CFSG.Assembly.pCoreOf 2 (T ⊓ CFSG.Fischer.fixAut r) ≤
      CFSG.Fischer.innerAut S := by
    have h1 : (CFSG.Assembly.pCoreOf 2 (T ⊓ CFSG.Fischer.fixAut r)).subgroupOf T ≤ ψ.range := by
      rwa [← GGRootNorm.pCoreOf_subgroupOf (H := T ⊓ CFSG.Fischer.fixAut r) (K := T)
        (inf_le_left : T ⊓ CFSG.Fischer.fixAut r ≤ T)]
    have h2 := Subgroup.map_mono h1 (f := T.subtype)
    rw [Subgroup.map_subgroupOf_eq_of_le
        (H := CFSG.Assembly.pCoreOf 2 (T ⊓ CFSG.Fischer.fixAut r)) (K := T)
        ((GGRootNorm.pCoreOf_le (T ⊓ CFSG.Fischer.fixAut r)).trans
          (inf_le_left : T ⊓ CFSG.Fischer.fixAut r ≤ T))] at h2
    rw [hψrange] at h2
    rw [Subgroup.map_subgroupOf_eq_of_le
        (H := CFSG.Fischer.innerAut S) (K := T) hInn] at h2
    exact h2
  intro a ha v hv
  have hinner : a ∈ CFSG.Fischer.innerAut S := hle ha
  obtain ⟨s, hs⟩ := CFSG.Fischer.mem_innerAut.mp hinner
  have hfixr : a r = r := CFSG.Fischer.mem_fixAut.mp (GGRootNorm.pCoreOf_le _ ha).2
  have hconj_fix : MulAut.conj s r = r := by rw [hs]; exact hfixr
  have hcoe : ∀ u : F,
      (↑(Frm.longRoot (i := i0) (j := j0) hij0 true true (.ofAdd u)) : CliffordAlgebra Q) =
        1 + u • A := by
    intro u
    exact HypFrame.coe_longRoot (F := Frm.toHypFrame) hij0 true true u
  have hca : (↑s : CliffordAlgebra Q) * (1 + t • A) * ↑(s⁻¹ : S) = 1 + t • A := by
    have h := congrArg (fun u : S => (u : CliffordAlgebra Q)) hconj_fix
    rw [MulAut.conj_apply, Submonoid.coe_mul, Submonoid.coe_mul, hr_eq, hcoe t] at h
    simpa [A] using h
  have hB : ι Q (spinAction Q s (Frm.vec i0 true)) *
      ι Q (spinAction Q s (Frm.vec j0 true)) = A := by
    have h := hca
    rw [coe_mul_one_add_smul_mul_coe_inv] at h
    exact smul_right_injective (M := CliffordAlgebra Q) ht0 (add_left_cancel h)
  have hfixu : ∀ u : F,
      MulAut.conj s (Frm.longRoot (i := i0) (j := j0) hij0 true true (.ofAdd u)) =
        Frm.longRoot (i := i0) (j := j0) hij0 true true (.ofAdd u) := by
    intro u
    apply Subtype.ext
    rw [MulAut.conj_apply, Submonoid.coe_mul, Submonoid.coe_mul, hcoe u,
      coe_mul_one_add_smul_mul_coe_inv, hB]
  obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hv
  calc a (x u) = MulAut.conj s (x u) := by rw [hs]
    _ = MulAut.conj s (Frm.longRoot (i := i0) (j := j0) hij0 true true u) := by rw [hx]
    _ = Frm.longRoot (i := i0) (j := j0) hij0 true true u := by
      rw [show u = Multiplicative.ofAdd (Multiplicative.toAdd u) from
        (ofAdd_toAdd u).symm]
      exact hfixu (Multiplicative.toAdd u)
    _ = x u := by rw [hx]

theorem minusRootAut_pCoreOf_fixes_longRoot_canonical {F : Type} [Field F] [Finite F]
    [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (T : Subgroup (MulAut (spinGroup (quadMinus 4 F b c))))
    (hInn : (MulAut.conj : spinGroup (quadMinus 4 F b c) →*
      MulAut (spinGroup (quadMinus 4 F b c))).range ≤ T)
    {r : spinGroup (quadMinus 4 F b c)}
    (hr : r ∈ ((minusFrame 4 b c).longRoot (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩)
      (by simp) true true).range)
    (hr1 : r ≠ 1) :
    ∀ a ∈ CFSG.Assembly.pCoreOf 2 (T ⊓ CFSG.Fischer.fixAut r),
      ∀ v ∈ ((minusFrame 4 b c).longRoot (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩)
        (by simp) true true).range, a v = v := by
  exact minusRootAut_pCoreOf_fixes_longRoot (F := F) hirr T hInn
    (x := (minusFrame 4 b c).longRoot (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩)
      (by simp) true true) rfl hr hr1


end MinusNativeRoot

section ActualRootCharts

open CFSG.Open CFSG.Assembly
open CFSG.ClassicalGroups.SpecialLinear CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.LieType.Universal.Spin.Twisted (minusFrame)

private lemma mulEquiv_map_ne_one {S S' : Type} [Group S] [Group S']
    (e : S ≃* S') {x : S} (hx : x ≠ 1) : e x ≠ 1 := by
  intro h
  apply hx
  apply e.injective
  simpa using h

private lemma map_mem_of_map_eq {S S' : Type} [Group S] [Group S']
    (e : S ≃* S') {R : Subgroup S} {R' : Subgroup S'}
    (hRmap : R.map e.toMonoidHom = R') {x : S} (hx : x ∈ R) : e x ∈ R' := by
  rw [← hRmap]
  exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩

theorem ggF4N2RootAction_sl4
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact (Nat.Prime p)]
    {A R : Subgroup G}
    (hOdd : Odd (Nat.card ↥(CFSG.Assembly.LargeEvenPPrimeCoreOf p A)))
    (hZ : Odd (Nat.card ↥(Subgroup.center (↥A ⧸ CFSG.pPrimeCore p ↥A))))
    (hRA : R ≤ A) {r : G} (hrR : r ∈ R) (hr2 : orderOf r = 2)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    (e : ggPComponentRootQuotient p A ≃* Matrix.SpecialLinearGroup (Fin 4) F)
    (hRmap : (ggPComponentRootImage p A R).map e.toMonoidHom = rootR F) :
    ∀ (T : Subgroup (MulAut (ggPComponentRootQuotient p A))),
      CFSG.Fischer.innerAut (ggPComponentRootQuotient p A) ≤ T →
      ∀ f : ↥(T ⊓ CFSG.Fischer.fixAut
          (ggPComponentRootInvolutionImage p A (r := r) (hRA hrR))),
        f ∈ CFSG.pCore 2 ↥(T ⊓ CFSG.Fischer.fixAut
          (ggPComponentRootInvolutionImage p A (r := r) (hRA hrR))) →
        ∀ x : ggPComponentRootQuotient p A,
          x ∈ ggPComponentRootImage p A R →
          (f : MulAut (ggPComponentRootQuotient p A)) x = x := by
  haveI : CharP F 2 :=
    CFSG.SectionRank.charP_of_natCard_eq_pow (p := 2) (f := 2) (by rw [hF]; norm_num)
  let rq : ggPComponentRootQuotient p A :=
    ggPComponentRootInvolutionImage p A (r := r) (hRA hrR)
  have hrne : rq ≠ 1 :=
    ggPComponentRootInvolutionImage_ne_one hOdd hZ hRA hrR hr2
  have hre : e rq ≠ 1 := mulEquiv_map_ne_one e hrne
  have hroot_mem : e rq ∈ rootR F :=
    map_mem_of_map_eq e hRmap (ggPComponentRootInvolutionImage_mem hRA hrR)
  exact hRoot_of_native e (ggPComponentRootImage p A R) rq (rootR F) hRmap
    (fun T' hInn' a ha v hv =>
      rootAut_pCoreOf_fixes_rootR (F := F) hF.ge T' hInn' hroot_mem hre a ha v hv)

theorem ggF4N2RootAction_psl6
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact (Nat.Prime p)]
    {A R : Subgroup G}
    (hOdd : Odd (Nat.card ↥(CFSG.Assembly.LargeEvenPPrimeCoreOf p A)))
    (hZ : Odd (Nat.card ↥(Subgroup.center (↥A ⧸ CFSG.pPrimeCore p ↥A))))
    (hRA : R ≤ A) {r : G} (hrR : r ∈ R) (hr2 : orderOf r = 2)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    (i j : Fin 6) (hij : i ≠ j)
    (e : ggPComponentRootQuotient p A ≃* projectiveSL 6 F)
    (hRmap : (ggPComponentRootImage p A R).map e.toMonoidHom =
      (rootGroup F hij).map (proj 6 F)) :
    ∀ (T : Subgroup (MulAut (ggPComponentRootQuotient p A))),
      CFSG.Fischer.innerAut (ggPComponentRootQuotient p A) ≤ T →
      ∀ f : ↥(T ⊓ CFSG.Fischer.fixAut
          (ggPComponentRootInvolutionImage p A (r := r) (hRA hrR))),
        f ∈ CFSG.pCore 2 ↥(T ⊓ CFSG.Fischer.fixAut
          (ggPComponentRootInvolutionImage p A (r := r) (hRA hrR))) →
        ∀ x : ggPComponentRootQuotient p A,
          x ∈ ggPComponentRootImage p A R →
          (f : MulAut (ggPComponentRootQuotient p A)) x = x := by
  haveI : CharP F 2 :=
    CFSG.SectionRank.charP_of_natCard_eq_pow (p := 2) (f := 2) (by rw [hF]; norm_num)
  let rq : ggPComponentRootQuotient p A :=
    ggPComponentRootInvolutionImage p A (r := r) (hRA hrR)
  have hrne : rq ≠ 1 :=
    ggPComponentRootInvolutionImage_ne_one hOdd hZ hRA hrR hr2
  have hre : e rq ≠ 1 := mulEquiv_map_ne_one e hrne
  have hroot_mem : e rq ∈ (rootGroup F hij).map (proj 6 F) :=
    map_mem_of_map_eq e hRmap (ggPComponentRootInvolutionImage_mem hRA hrR)
  exact hRoot_of_native e (ggPComponentRootImage p A R) rq
    ((rootGroup F hij).map (proj 6 F)) hRmap
    (fun T' hInn' a ha v hv =>
      psl6_rootAut_pCoreOf_fixes (F := F) hF i j hij T' hInn' hroot_mem hre a ha v hv)

theorem ggF4N2RootAction_minus
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact (Nat.Prime p)]
    {A R : Subgroup G}
    (hOdd : Odd (Nat.card ↥(CFSG.Assembly.LargeEvenPPrimeCoreOf p A)))
    (hZ : Odd (Nat.card ↥(Subgroup.center (↥A ⧸ CFSG.pPrimeCore p ↥A))))
    (hRA : R ≤ A) {r : G} (hrR : r ∈ R) (hr2 : orderOf r = 2)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4) {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (e : ggPComponentRootQuotient p A ≃* spinGroup (quadMinus 4 F b c))
    (hRmap : (ggPComponentRootImage p A R).map e.toMonoidHom =
      ((minusFrame 4 b c).longRoot (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩)
        (by simp) true true).range) :
    ∀ (T : Subgroup (MulAut (ggPComponentRootQuotient p A))),
      CFSG.Fischer.innerAut (ggPComponentRootQuotient p A) ≤ T →
      ∀ f : ↥(T ⊓ CFSG.Fischer.fixAut
          (ggPComponentRootInvolutionImage p A (r := r) (hRA hrR))),
        f ∈ CFSG.pCore 2 ↥(T ⊓ CFSG.Fischer.fixAut
          (ggPComponentRootInvolutionImage p A (r := r) (hRA hrR))) →
        ∀ x : ggPComponentRootQuotient p A,
          x ∈ ggPComponentRootImage p A R →
          (f : MulAut (ggPComponentRootQuotient p A)) x = x := by
  haveI : CharP F 2 :=
    CFSG.SectionRank.charP_of_natCard_eq_pow (p := 2) (f := 2) (by rw [hF]; norm_num)
  let rq : ggPComponentRootQuotient p A :=
    ggPComponentRootInvolutionImage p A (r := r) (hRA hrR)
  have hrne : rq ≠ 1 :=
    ggPComponentRootInvolutionImage_ne_one hOdd hZ hRA hrR hr2
  have hre : e rq ≠ 1 := mulEquiv_map_ne_one e hrne
  have hroot_mem : e rq ∈
      ((minusFrame 4 b c).longRoot (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩)
        (by simp) true true).range :=
    map_mem_of_map_eq e hRmap (ggPComponentRootInvolutionImage_mem hRA hrR)
  exact hRoot_of_native e (ggPComponentRootImage p A R) rq
    (((minusFrame 4 b c).longRoot (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩)
      (by simp) true true).range) hRmap
    (fun T' hInn' a ha v hv =>
      minusRootAut_pCoreOf_fixes_longRoot_canonical (F := F) hirr T' hInn'
        hroot_mem hre a ha v hv)


end ActualRootCharts

section MarkedRootInjection
open CFSG.Assembly

theorem ggPComponentRoot_inf_pPrimeCore_eq_bot_of_simple
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact (Nat.Prime p)]
    {A J : Subgroup G} [IsSimpleGroup J] (hJA : J ≤ A)
    (hpJ : p ∣ Nat.card J) :
    J ⊓ LargeEvenPPrimeCoreOf p A = ⊥ := by
  classical
  let Q : Subgroup ↥A := CFSG.pPrimeCore p ↥A
  let QG : Subgroup G := LargeEvenPPrimeCoreOf p A
  have hQGA : QG ≤ A := by
    change (CFSG.pPrimeCore p ↥A).map A.subtype ≤ A
    exact Subgroup.map_subtype_le _
  have hQeq : Q = QG.subgroupOf A := by
    apply Subgroup.map_injective A.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hQGA]
    change (CFSG.pPrimeCore p ↥A).map A.subtype = QG
    rfl
  have hcopQG : Nat.Coprime p (Nat.card QG) := by
    change Nat.Coprime p (Nat.card ((CFSG.pPrimeCore p ↥A).map A.subtype))
    rw [Subgroup.card_map_of_injective A.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  let N : Subgroup J := (J ⊓ QG).subgroupOf J
  have hcore_conj : ∀ g ∈ J, ∀ z ∈ QG, g * z * g⁻¹ ∈ QG := by
    intro g hg z hz
    change z ∈ (CFSG.pPrimeCore p ↥A).map A.subtype at hz
    obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
    change g * (z' : G) * g⁻¹ ∈ (CFSG.pPrimeCore p ↥A).map A.subtype
    refine Subgroup.mem_map.mpr ⟨⟨g, hJA hg⟩ * z' * ⟨g, hJA hg⟩⁻¹, ?_, by simp⟩
    exact (inferInstance : (CFSG.pPrimeCore p ↥A).Normal).conj_mem z' hz' ⟨g, hJA hg⟩
  have hNnormal : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨?_, ?_⟩
    · exact J.mul_mem (J.mul_mem g.2 hn.1) (J.inv_mem g.2)
    · exact hcore_conj g g.2 n hn.2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hNbot | hNtop
  · rw [eq_bot_iff]
    intro z hz
    have hzN : (⟨z, hz.1⟩ : J) ∈ N := Subgroup.mem_subgroupOf.mpr hz
    rw [hNbot] at hzN
    exact Subgroup.mem_bot.mpr (Subtype.ext_iff.mp (Subgroup.mem_bot.mp hzN))
  · exfalso
    have hJleQ : J ≤ QG := by
      intro j hj
      have hmemN : (⟨j, hj⟩ : J) ∈ N := by
        rw [hNtop]
        exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp hmemN).2
    have hdvd : p ∣ Nat.card QG := hpJ.trans (Subgroup.card_dvd_of_le hJleQ)
    exact ((Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp hcopQG) hdvd

theorem ggPComponentRoot_inclusion_injective_of_simple
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact (Nat.Prime p)]
    {A J : Subgroup G} [IsSimpleGroup J] (hJA : J ≤ A)
    (hpJ : p ∣ Nat.card J) (hZJ : Subgroup.center J = ⊥) :
    Function.Injective
      ((QuotientGroup.mk' (ggPComponentRootKernelInA p A)).comp
        (Subgroup.inclusion hJA)) := by
  classical
  let Q : Subgroup ↥A := CFSG.pPrimeCore p ↥A
  let QG : Subgroup G := LargeEvenPPrimeCoreOf p A
  have hQGA : QG ≤ A := by
    change (CFSG.pPrimeCore p ↥A).map A.subtype ≤ A
    exact Subgroup.map_subtype_le _
  have hQeq : Q = QG.subgroupOf A := by
    apply Subgroup.map_injective A.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hQGA]
    change (CFSG.pPrimeCore p ↥A).map A.subtype = QG
    rfl
  have hJQbot : J ⊓ QG = ⊥ :=
    ggPComponentRoot_inf_pPrimeCore_eq_bot_of_simple (p := p) hJA hpJ
  let Aq := ↥A ⧸ Q
  let Z : Subgroup Aq := Subgroup.center Aq
  let Jq : Subgroup Aq := (J.subgroupOf A).map (QuotientGroup.mk' Q)
  let φ : J.subgroupOf A →* Aq := (QuotientGroup.mk' Q).comp (J.subgroupOf A).subtype
  have hφker : φ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxQ : (x : ↥A) ∈ Q := by
      exact (QuotientGroup.eq_one_iff (N := Q) (x : ↥A)).mp hx
    have hxQG : (x : G) ∈ QG := by
      rw [hQeq] at hxQ
      exact Subgroup.mem_subgroupOf.mp hxQ
    have hxJQ : (x : G) ∈ J ⊓ QG := ⟨x.2, hxQG⟩
    rw [hJQbot] at hxJQ
    have hx1 : (x : G) = 1 := Subgroup.mem_bot.mp hxJQ
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subtype.ext hx1))
  have hφinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hφker
  let φq : J.subgroupOf A →* Jq :=
    { toFun := fun x => ⟨φ x, Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp }
  have hφqinj : Function.Injective φq := by
    intro x y hxy
    apply hφinj
    exact congrArg Subtype.val hxy
  have hφqsurj : Function.Surjective φq := by
    intro y
    rcases Subgroup.mem_map.mp y.2 with ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    change QuotientGroup.mk' Q x = (y : Aq)
    exact hxy
  let eJq : J.subgroupOf A ≃* Jq := MulEquiv.ofBijective φq ⟨hφqinj, hφqsurj⟩
  let eJqFull : J ≃* Jq := (Subgroup.subgroupOfEquivOfLe hJA).symm.trans eJq
  have hZJq : Subgroup.center Jq = ⊥ := by
    have hmap := Subgroup.map_center_eq eJqFull
    rw [hZJ] at hmap
    simpa using hmap.symm
  have hJqZbot : Jq ⊓ Z = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxcenter : (⟨x, hx.1⟩ : Jq) ∈ Subgroup.center Jq := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_center_iff.mp hx.2 (y : Aq))
    rw [hZJq] at hxcenter
    have hx1 : x = 1 := congrArg Subtype.val (Subgroup.mem_bot.mp hxcenter)
    exact Subgroup.mem_bot.mpr hx1
  let K : Subgroup ↥A := CFSG.StandardType.ggPComponentRootKernelInA p A
  have hK : K = Z.comap (QuotientGroup.mk' Q) := rfl
  rw [← MonoidHom.ker_eq_bot_iff]
  rw [eq_bot_iff]
  intro j hj
  rw [MonoidHom.mem_ker] at hj
  let a : ↥A := Subgroup.inclusion hJA j
  have haK : a ∈ K := (QuotientGroup.eq_one_iff (N := K) a).mp hj
  have haZ : QuotientGroup.mk' Q a ∈ Z := by
    rw [hK] at haK
    exact Subgroup.mem_comap.mp haK
  have haJ : a ∈ J.subgroupOf A := by
    rw [Subgroup.mem_subgroupOf]
    exact j.2
  have haJq : QuotientGroup.mk' Q a ∈ Jq :=
    Subgroup.mem_map.mpr ⟨a, haJ, rfl⟩
  have haint : QuotientGroup.mk' Q a ∈ Jq ⊓ Z := ⟨haJq, haZ⟩
  rw [hJqZbot] at haint
  have haQ : a ∈ Q :=
    (QuotientGroup.eq_one_iff (N := Q) a).mp (Subgroup.mem_bot.mp haint)
  have haQG : (a : G) ∈ QG := by
    have : a ∈ QG.subgroupOf A := by
      rw [← hQeq]
      exact haQ
    exact Subgroup.mem_subgroupOf.mp this
  have haJQG : (a : G) ∈ J ⊓ QG := ⟨j.2, haQG⟩
  rw [hJQbot] at haJQG
  have ha1 : (a : G) = 1 := Subgroup.mem_bot.mp haJQG
  have hj1G : (j : G) = 1 := by simpa [a] using ha1
  exact Subgroup.mem_bot.mpr (Subtype.ext hj1G)

theorem ggPComponentRoot_not_mulEquiv_of_dvd_card
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact (Nat.Prime p)]
    {A J : Subgroup G} [IsSimpleGroup J] (hJA : J ≤ A)
    (hpJ : p ∣ Nat.card J) (hZJ : Subgroup.center J = ⊥)
    {Q : Type} [Group Q] [Finite Q] {ell : ℕ}
    (hellJ : ell ∣ Nat.card J) (hellQ : ¬ ell ∣ Nat.card Q) :
    IsEmpty (ggPComponentRootQuotient p A ≃* Q) := by
  refine ⟨fun e => ?_⟩
  have hinj := ggPComponentRoot_inclusion_injective_of_simple (p := p) hJA hpJ hZJ
  have hcomp_inj : Function.Injective
      (e.toMonoidHom.comp
        ((QuotientGroup.mk' (ggPComponentRootKernelInA p A)).comp
          (Subgroup.inclusion hJA))) :=
    e.injective.comp hinj
  have hdvd : Nat.card J ∣ Nat.card Q :=
    Subgroup.card_dvd_of_injective _ hcomp_inj
  exact hellQ (hellJ.trans hdvd)

theorem ggPComponentRoot_inclusion_injective_sl4
    {G : Type} [Group G] [Finite G] [Fact (Nat.Prime 5)]
    {A J : Subgroup G} (hJA : J ≤ A)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    (eJ : J ≃* Matrix.SpecialLinearGroup (Fin 4) F) :
    Function.Injective
      ((QuotientGroup.mk' (ggPComponentRootKernelInA 5 A)).comp
        (Subgroup.inclusion hJA)) := by
  classical
  haveI : CharP F 2 :=
    CFSG.SectionRank.charP_of_natCard_eq_pow (p := 2) (f := 2) (by rw [hF]; norm_num)
  haveI : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 4) F) :=
    (CFSG.RankThree.PartOne.K159.Klein.sl4_isSimpleGroup_and_perfect (K := F)).1
  haveI : IsSimpleGroup J := eJ.isSimpleGroup
  have hpJ : 5 ∣ Nat.card J := by
    have hcard : Nat.card J = Nat.card (Matrix.SpecialLinearGroup (Fin 4) F) :=
      Nat.card_congr eJ.toEquiv
    rw [hcard]
    haveI : Fintype F := Fintype.ofFinite F
    have hF' : Fintype.card F = 4 := by
      rw [← Nat.card_eq_fintype_card]
      exact hF
    rw [CFSG.HardMathSupport.Foote.Proving.natCard_SL4_field, hF']
    refine ⟨4 ^ 6 * 3 * (4 ^ 3 - 1) * (4 ^ 4 - 1), ?_⟩
    norm_num
  have hZJ : Subgroup.center J = ⊥ := by
    have hmap := Subgroup.map_center_eq eJ
    rw [CFSG.RankThree.PartOne.K159.Klein.center_sl4_eq_bot] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective (H := Subgroup.center J)
      (f := eJ.toMonoidHom) eJ.injective).mp hmap
  exact ggPComponentRoot_inclusion_injective_of_simple (p := 5) hJA hpJ hZJ

theorem ggPComponentRoot_not_psl216_of_sl4
    {G : Type} [Group G] [Finite G] [Fact (Nat.Prime 5)]
    {A J : Subgroup G} (hJA : J ≤ A)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    (eJ : J ≃* Matrix.SpecialLinearGroup (Fin 4) F) :
    IsEmpty (ggPComponentRootQuotient 5 A ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 4)) := by
  classical
  haveI : CharP F 2 :=
    CFSG.SectionRank.charP_of_natCard_eq_pow (p := 2) (f := 2) (by rw [hF]; norm_num)
  haveI : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 4) F) :=
    (CFSG.RankThree.PartOne.K159.Klein.sl4_isSimpleGroup_and_perfect (K := F)).1
  haveI : IsSimpleGroup J := eJ.isSimpleGroup
  have h7J : 7 ∣ Nat.card J := by
    have hcard : Nat.card J = Nat.card (Matrix.SpecialLinearGroup (Fin 4) F) :=
      Nat.card_congr eJ.toEquiv
    rw [hcard]
    haveI : Fintype F := Fintype.ofFinite F
    have hF' : Fintype.card F = 4 := by
      rw [← Nat.card_eq_fintype_card]
      exact hF
    rw [CFSG.HardMathSupport.Foote.Proving.natCard_SL4_field, hF']
    norm_num
  have h7PSL : ¬ 7 ∣ Nat.card
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 4)) := by
    have hcard : Nat.card
        (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 4)) = 4080 := by
      have ePSL : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 4) ≃*
          CFSG.PGLModel.projSL 2 (GaloisField 2 4) :=
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 _).trans
          (CFSG.PGLModel.projSLEquivStatedProj 2 _).symm
      rw [Nat.card_congr ePSL.toEquiv]
      exact CFSG.PGLModel.card_projSL_two_sixteen
    rw [hcard]
    norm_num
  refine ⟨fun e => ?_⟩
  have hinj := ggPComponentRoot_inclusion_injective_sl4 hJA hF eJ
  have hcomp_inj : Function.Injective
      (e.toMonoidHom.comp
        ((QuotientGroup.mk' (ggPComponentRootKernelInA 5 A)).comp
          (Subgroup.inclusion hJA))) :=
    e.injective.comp hinj
  have hdvd : 7 ∣ Nat.card
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 4)) :=
    h7J.trans (Subgroup.card_dvd_of_injective _ hcomp_inj)
  exact h7PSL hdvd


end MarkedRootInjection

section BadLineQuotientCharts

open Matrix CFSG.Assembly CFSG.ClassicalGroups.SpecialLinear

theorem exists_pComponentRootQuotientEquiv_of_sup_of_dvd
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {X A J : Subgroup G}
    (hA : LargeEvenPComponent p X A) (hJA : J ≤ A)
    (hAeq : A = J ⊔ LargeEvenPPrimeCoreOf p A)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    (eJ : J ≃* SpecialLinearGroup (Fin 4) F)
    (hpJ : p ∣ Nat.card J) :
    ∃ e : ggPComponentRootQuotient p A ≃* SpecialLinearGroup (Fin 4) F,
      (∀ j : J,
        e (QuotientGroup.mk' (ggPComponentRootKernelInA p A) ⟨j, hJA j.2⟩) = eJ j) ∧
      ggPComponentRootKernelInA p A = CFSG.pPrimeCore p A := by
  haveI : CharP F 2 := CFSG.SectionRank.charP_of_natCard_eq_pow (p := 2) (f := 2) (by rw [hF]; norm_num)
  let Q : Subgroup ↥A := CFSG.pPrimeCore p A
  let QG : Subgroup G := LargeEvenPPrimeCoreOf p A
  have hQGA : QG ≤ A := by
    change (CFSG.pPrimeCore p A).map A.subtype ≤ A
    exact Subgroup.map_subtype_le _
  have hQeq : Q = QG.subgroupOf A := by
    apply Subgroup.map_injective A.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hQGA]
    change (CFSG.pPrimeCore p A).map A.subtype = QG
    rfl
  have hcopQG : Nat.Coprime p (Nat.card QG) := by
    change Nat.Coprime p (Nat.card ((CFSG.pPrimeCore p A).map A.subtype))
    rw [Subgroup.card_map_of_injective A.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  haveI : IsSimpleGroup (SpecialLinearGroup (Fin 4) F) :=
    (CFSG.RankThree.PartOne.K159.Klein.sl4_isSimpleGroup_and_perfect (K := F)).1
  haveI : IsSimpleGroup J := eJ.isSimpleGroup
  have hZJ : Subgroup.center J = ⊥ := by
    have hmap := Subgroup.map_center_eq eJ
    rw [CFSG.RankThree.PartOne.K159.Klein.center_sl4_eq_bot] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective (H := Subgroup.center J)
      (f := eJ.toMonoidHom) eJ.injective).mp hmap
  have hJQbot : J ⊓ QG = ⊥ := by
    let N : Subgroup J := (J ⊓ QG).subgroupOf J
    have hcore_conj : ∀ g ∈ J, ∀ z ∈ QG, g * z * g⁻¹ ∈ QG := by
      intro g hg z hz
      change z ∈ (CFSG.pPrimeCore p A).map A.subtype at hz
      obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
      change g * (z' : G) * g⁻¹ ∈ (CFSG.pPrimeCore p A).map A.subtype
      refine Subgroup.mem_map.mpr ⟨⟨g, hJA hg⟩ * z' * ⟨g, hJA hg⟩⁻¹, ?_, by simp⟩
      exact (inferInstance : (CFSG.pPrimeCore p ↥A).Normal).conj_mem z' hz' ⟨g, hJA hg⟩
    have hNnormal : N.Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      refine ⟨?_, ?_⟩
      · exact J.mul_mem (J.mul_mem g.2 hn.1) (J.inv_mem g.2)
      · exact hcore_conj g g.2 n hn.2
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hNbot | hNtop
    · rw [eq_bot_iff]
      intro z hz
      have hzN : (⟨z, hz.1⟩ : J) ∈ N := Subgroup.mem_subgroupOf.mpr hz
      rw [hNbot] at hzN
      exact Subgroup.mem_bot.mpr (Subtype.ext_iff.mp (Subgroup.mem_bot.mp hzN))
    · exfalso
      have hJleQ : J ≤ QG := by
        intro j hj
        have hmemN : (⟨j, hj⟩ : J) ∈ N := by
          rw [hNtop]
          exact Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf.mp hmemN).2
      have hdvd : p ∣ Nat.card QG := hpJ.trans (Subgroup.card_dvd_of_le hJleQ)
      exact ((Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp hcopQG) hdvd
  have hJQbotJ : (J ⊓ QG).subgroupOf J = ⊥ := by
    rw [hJQbot, Subgroup.bot_subgroupOf]
  let φ : J →* ↥A ⧸ Q := (QuotientGroup.mk' Q).comp (Subgroup.inclusion hJA)
  have hφker : φ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro j hj
    rw [Subgroup.mem_bot]
    have hj1 : φ j = 1 := MonoidHom.mem_ker.mp hj
    have hmemQ : (Subgroup.inclusion hJA j : ↥A) ∈ Q := by
      have hmk : QuotientGroup.mk' Q (Subgroup.inclusion hJA j) = 1 := by
        simpa [φ] using hj1
      exact (QuotientGroup.eq_one_iff _).mp hmk
    have hmemQG : (j : G) ∈ QG := by
      rw [hQeq] at hmemQ
      exact Subgroup.mem_subgroupOf.mp hmemQ
    have hmemJQ : j ∈ (J ⊓ QG).subgroupOf J :=
      Subgroup.mem_subgroupOf.mpr ⟨j.2, hmemQG⟩
    rw [hJQbotJ] at hmemJQ
    exact Subgroup.mem_bot.mp hmemJQ
  have hsupA : (J.subgroupOf A) ⊔ Q = ⊤ := by
    calc (J.subgroupOf A) ⊔ Q = (J.subgroupOf A) ⊔ (QG.subgroupOf A) := by rw [hQeq]
      _ = (J ⊔ QG).subgroupOf A := (Subgroup.subgroupOf_sup hJA hQGA).symm
      _ = A.subgroupOf A := by rw [hAeq]
      _ = ⊤ := Subgroup.subgroupOf_self A
  have hmap_eq : (J.subgroupOf A).map (QuotientGroup.mk' Q) =
      ((J.subgroupOf A) ⊔ Q).map (QuotientGroup.mk' Q) := by
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]
  have hφrange0 : φ.range = (J.subgroupOf A).map (QuotientGroup.mk' Q) := by
    dsimp [φ]
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hφrange : φ.range = ⊤ := by
    rw [hφrange0, hmap_eq, hsupA,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Q)]
  let φe : J ≃* ↥A ⧸ Q :=
    MulEquiv.ofBijective φ
      ⟨(MonoidHom.ker_eq_bot_iff φ).mp hφker, MonoidHom.range_eq_top.mp hφrange⟩
  have hZquot : Subgroup.center (↥A ⧸ Q) = ⊥ := by
    have hmap := Subgroup.map_center_eq φe
    rw [hZJ] at hmap
    simpa using hmap.symm
  have hKQ : ggPComponentRootKernelInA p A = Q := by
    change (Subgroup.center (↥A ⧸ Q)).comap (QuotientGroup.mk' Q) = Q
    rw [hZquot, MonoidHom.comap_bot, QuotientGroup.ker_mk']
  let e : ggPComponentRootQuotient p A ≃* SpecialLinearGroup (Fin 4) F :=
    (QuotientGroup.quotientMulEquivOfEq hKQ).trans (φe.symm.trans eJ)
  refine ⟨e, ?_, hKQ⟩
  intro j
  dsimp [e]
  change eJ (φe.symm (φ j)) = eJ j
  exact congrArg eJ (MulEquiv.symm_apply_apply φe j)

theorem exists_pComponentRootQuotientEquiv_of_sup_five
    {G : Type} [Group G] [Finite G] [Fact (Nat.Prime 5)]
    {X A J : Subgroup G}
    (hA : LargeEvenPComponent 5 X A) (hJA : J ≤ A)
    (hAeq : A = J ⊔ LargeEvenPPrimeCoreOf 5 A)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    (eJ : J ≃* SpecialLinearGroup (Fin 4) F) :
    ∃ e : ggPComponentRootQuotient 5 A ≃* SpecialLinearGroup (Fin 4) F,
      (∀ j : J,
        e (QuotientGroup.mk' (ggPComponentRootKernelInA 5 A) ⟨j, hJA j.2⟩) = eJ j) ∧
      ggPComponentRootKernelInA 5 A = CFSG.pPrimeCore 5 A := by
  have h5J : 5 ∣ Nat.card J := by
    have hcard : Nat.card J = Nat.card (SpecialLinearGroup (Fin 4) F) := Nat.card_congr eJ.toEquiv
    rw [hcard]
    haveI : Fintype F := Fintype.ofFinite F
    have hF' : Fintype.card F = 4 := by
      rw [← Nat.card_eq_fintype_card]
      exact hF
    rw [CFSG.HardMathSupport.Foote.Proving.natCard_SL4_field, hF']
    refine ⟨4 ^ 6 * 3 * (4 ^ 3 - 1) * (4 ^ 4 - 1), ?_⟩
    norm_num
  exact exists_pComponentRootQuotientEquiv_of_sup_of_dvd
    (p := 5) (X := X) (A := A) (J := J) hA hJA hAeq hF eJ h5J

theorem ggPComponentRootImage_map_of_chart
    {G N M : Type} [Group G] [Finite G] [Group N] [Group M]
    {p : ℕ} [Fact p.Prime] {A R : Subgroup G}
    (ψ : N →* A) (Q : Subgroup N)
    (hR : Q.map (A.subtype.comp ψ) = R)
    (f : ggPComponentRootQuotient p A →* M) (ρ : N →* M)
    (h : ∀ n, f (QuotientGroup.mk' (ggPComponentRootKernelInA p A) (ψ n)) = ρ n) :
    (ggPComponentRootImage p A R).map f = Q.map ρ := by
  have hRA : R ≤ A := by
    rw [← hR]
    rintro _ ⟨n, -, rfl⟩
    exact (ψ n).2
  have hsub : R.subgroupOf A = Q.map ψ := by
    apply Subgroup.map_injective A.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hRA, Subgroup.map_map]
    exact hR.symm
  rw [ggPComponentRootImage, hsub, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext n
  exact h n


theorem ggPComponentRootImage_map_eq_rootR
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {A J : Subgroup G} (hJA : J ≤ A)
    {F : Type} [Field F]
    (eJ : J ≃* SpecialLinearGroup (Fin 4) F)
    (e : ggPComponentRootQuotient p A ≃* SpecialLinearGroup (Fin 4) F)
    (he : ∀ j : J,
      e (QuotientGroup.mk' (ggPComponentRootKernelInA p A) ⟨j, hJA j.2⟩) = eJ j) :
    (ggPComponentRootImage p A
      ((rootR F).map (J.subtype.comp eJ.symm.toMonoidHom))).map e.toMonoidHom = rootR F := by
  simpa only [Subgroup.map_id, ← MonoidHom.comp_assoc, Subgroup.subtype_comp_inclusion] using
    (ggPComponentRootImage_map_of_chart
      ((Subgroup.inclusion hJA).comp eJ.symm.toMonoidHom) (rootR F)
      rfl e.toMonoidHom
      (MonoidHom.id (SpecialLinearGroup (Fin 4) F))
      (fun x => by simpa [Subgroup.inclusion] using he (eJ.symm x)))

theorem exists_badLineQuotientChart
    {G : Type} [Group G] [Finite G] [Fact (Nat.Prime 5)]
    {X A J : Subgroup G}
    (hA : LargeEvenPComponent 5 X A) (hJA : J ≤ A)
    (hAeq : A = J ⊔ LargeEvenPPrimeCoreOf 5 A)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    (eJ : J ≃* SpecialLinearGroup (Fin 4) F) :
    ∃ e : ggPComponentRootQuotient 5 A ≃* SpecialLinearGroup (Fin 4) F,
      (∀ j : J,
        e (QuotientGroup.mk' (ggPComponentRootKernelInA 5 A) ⟨j, hJA j.2⟩) = eJ j) ∧
      ggPComponentRootKernelInA 5 A = CFSG.pPrimeCore 5 A ∧
      (ggPComponentRootImage 5 A
        ((rootR F).map (J.subtype.comp eJ.symm.toMonoidHom))).map e.toMonoidHom = rootR F := by
  obtain ⟨e, he, hK⟩ :=
    exists_pComponentRootQuotientEquiv_of_sup_five (X := X) (A := A) (J := J)
      hA hJA hAeq hF eJ
  refine ⟨e, he, hK, ?_⟩
  exact ggPComponentRootImage_map_eq_rootR hJA eJ e he


end BadLineQuotientCharts

theorem commutator_eq_bot_of_largeEvenPComponent_rootAction_of_rootChart
    {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact (Nat.Prime p)] {X A R U : Subgroup G}
    (hA : CFSG.Assembly.LargeEvenPComponent p X A)
    (hOdd : Odd (Nat.card ↥(CFSG.Assembly.LargeEvenPPrimeCoreOf p A)))
    (hZ : Odd (Nat.card ↥(Subgroup.center (↥A ⧸ CFSG.pPrimeCore p ↥A))))
    (hRA : R ≤ A) [hRelem : CFSG.IsElementaryAbelian 2 ↥R]
    {r : G} (hrR : r ∈ R) (hr2 : orderOf r = 2)
    (hUN0 : U ≤ X ⊓ Subgroup.centralizer ({r} : Set G))
    (hUnormal0 : (U.subgroupOf (X ⊓ Subgroup.centralizer ({r} : Set G))).Normal)
    (hUtwo : IsPGroup 2 ↥U)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    (e : CFSG.StandardType.ggPComponentRootQuotient p A ≃*
      Matrix.SpecialLinearGroup (Fin 4) F)
    (hRmap : (CFSG.StandardType.ggPComponentRootImage p A R).map e.toMonoidHom =
      CFSG.StandardType.rootR F) :
    ⁅R, U⁆ = ⊥ := by
  exact commutator_eq_bot_of_largeEvenPComponent_rootAction
    (p := p) (X := X) (A := A) (R := R) (U := U) hA hOdd hZ hRA hrR hr2
    hUN0 hUnormal0 hUtwo (ggF4N2RootAction_sl4 hOdd hZ hRA hrR hr2 hF e hRmap)

end CFSG.StandardType

namespace CFSG.StandardType

open CFSG.StandardType
open Matrix

private noncomputable def highRoot : Fin 3 → ℤ := fun _ => 1

private theorem highRoot_toStd :
    CFSG.LieType.Universal.SpecialLinear.toStd 3 highRoot =
      Pi.single 0 1 - Pi.single 3 1 := by
  ext a
  fin_cases a <;> simp [highRoot, CFSG.LieType.Universal.SpecialLinear.toStd]

private theorem highRoot_mem_roots :
    highRoot ∈ CFSG.LieType.RootSystem.roots
      (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 3) ∅ := by
  rw [CFSG.LieType.Universal.SpecialLinear.roots_eq]
  exact ⟨0, 3, by decide, highRoot_toStd⟩

private theorem rootR_eq_specialRootGroup (F : Type) [Field F] :
    rootR F = CFSG.LieType.Universal.SpecialLinear.rootGroup 3 F highRoot := by
  rw [CFSG.LieType.Universal.SpecialLinear.rootGroup_eq (m := 3) (F := F)
    (i := 0) (j := 3) (by decide) highRoot_toStd]
  ext g
  rw [CFSG.ClassicalGroups.SpecialLinear.mem_rootGroup,
    CFSG.LieType.Universal.SpecialLinear.mem_rootSubgroup]

private theorem root30_eq_specialRootGroup_neg (F : Type) [Field F] :
    CFSG.ClassicalGroups.SpecialLinear.rootGroup F (by decide : (3 : Fin 4) ≠ 0) =
      CFSG.LieType.Universal.SpecialLinear.rootGroup 3 F (-highRoot) := by
  rw [CFSG.LieType.Universal.SpecialLinear.rootGroup_eq (m := 3) (F := F)
    (i := 3) (j := 0) (by decide) ?_]
  · ext g
    rw [CFSG.ClassicalGroups.SpecialLinear.mem_rootGroup,
      CFSG.LieType.Universal.SpecialLinear.mem_rootSubgroup]
  · rw [CFSG.LieType.Universal.SpecialLinear.toStd_neg, highRoot_toStd, neg_sub]

private theorem rootSubgroup_map_conj_signedPermutation (F : Type) [Field F] [CharP F 2]
    (w : Equiv.Perm (Fin 4)) {a b : Fin 4} (hab : a ≠ b) :
    (CFSG.LieType.Universal.SpecialLinear.rootSubgroup 3 F hab).map
        (MulAut.conj (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.signedPermutation 4 F w)).toMonoidHom =
      CFSG.LieType.Universal.SpecialLinear.rootSubgroup 3 F (w.injective.ne hab) := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨c, rfl⟩ := (CFSG.LieType.Universal.SpecialLinear.mem_rootSubgroup (m := 3) (F := F) hab x).mp hx
    exact (CFSG.LieType.Universal.SpecialLinear.mem_rootSubgroup (m := 3) (F := F) (w.injective.ne hab) _).mpr
      ⟨c, by
        simpa [MulAut.conj_apply] using
          (CFSG.QuasithinUnique.K1.signedPermutation_conj_transvection (K := F) w hab c).symm⟩
  · intro hg
    obtain ⟨c, rfl⟩ := (CFSG.LieType.Universal.SpecialLinear.mem_rootSubgroup (m := 3) (F := F) (w.injective.ne hab) _).mp hg
    refine ⟨SpecialLinearGroup.transvection hab c, ?_, ?_⟩
    · exact (CFSG.LieType.Universal.SpecialLinear.mem_rootSubgroup (m := 3) (F := F) hab _).mpr ⟨c, rfl⟩
    · simpa [MulAut.conj_apply] using
        CFSG.QuasithinUnique.K1.signedPermutation_conj_transvection (K := F) w hab c

private theorem root30_eq_rootR_map_conj_swap (F : Type) [Field F] [CharP F 2] :
    CFSG.ClassicalGroups.SpecialLinear.rootGroup F (by decide : (3 : Fin 4) ≠ 0) =
      (rootR F).map
        (MulAut.conj (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.signedPermutation 4 F
          (Equiv.swap 0 3))).toMonoidHom := by
  rw [rootR_eq_specialRootGroup, root30_eq_specialRootGroup_neg]
  rw [CFSG.LieType.Universal.SpecialLinear.rootGroup_eq (m := 3) (F := F)
      (i := 3) (j := 0) (by decide) (by
        rw [CFSG.LieType.Universal.SpecialLinear.toStd_neg, highRoot_toStd, neg_sub]),
    CFSG.LieType.Universal.SpecialLinear.rootGroup_eq (m := 3) (F := F)
      (i := 0) (j := 3) (by decide) highRoot_toStd]
  simpa using (rootSubgroup_map_conj_signedPermutation F (Equiv.swap 0 3)
    (by decide : (0 : Fin 4) ≠ 3)).symm


private theorem specialRootGroup_image_std_zero (F : Type) [Field F] [Finite F]
    (A : GL (Fin 4) F) (σ : F ≃+* F) :
    ∃ v : SpecialLinearGroup (Fin 4) F,
      (CFSG.LieType.Universal.SpecialLinear.rootGroup 3 F highRoot).map
        ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 F A *
          CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 4) F σ).toMonoidHom) =
      (CFSG.LieType.Universal.SpecialLinear.rootGroup 3 F highRoot).map
        (MulAut.conj v).toMonoidHom := by
  obtain ⟨v, hv⟩ := CFSG.StandardType.RCKRP.irgL_exists_conj_rootGroup_slConjugation
    (m := 3) (by norm_num) A
  refine ⟨v, ?_⟩
  have hstep :
      (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 F A *
        CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 4) F σ).toMonoidHom =
      (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 F A).toMonoidHom.comp
        (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 4) F σ).toMonoidHom := by
    rfl
  rw [hstep, ← Subgroup.map_map,
    CFSG.StandardType.RCKRP.irgL_rootGroup_map_slFieldAut σ highRoot_mem_roots]
  exact hv highRoot_mem_roots

private theorem specialRootGroup_image_std_one (F : Type) [Field F] [Finite F]
    (A : GL (Fin 4) F) (σ : F ≃+* F) :
    ∃ v : SpecialLinearGroup (Fin 4) F,
      (CFSG.LieType.Universal.SpecialLinear.rootGroup 3 F highRoot).map
        ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 F A *
          CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 4) F σ *
            CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 4 F).toMonoidHom) =
      (CFSG.LieType.Universal.SpecialLinear.rootGroup 3 F (-highRoot)).map
        (MulAut.conj v).toMonoidHom := by
  obtain ⟨v, hv⟩ := CFSG.StandardType.RCKRP.irgL_exists_conj_rootGroup_slConjugation
    (m := 3) (by norm_num) A
  refine ⟨v, ?_⟩
  have hneg : -highRoot ∈ CFSG.LieType.RootSystem.roots
      (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 3) ∅ :=
    CFSG.StandardType.RCKRP.irgL_neg_mem_roots highRoot_mem_roots
  have hstep :
      (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 F A *
        CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 4) F σ *
          CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 4 F).toMonoidHom =
      ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 F A).toMonoidHom.comp
        (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 4) F σ).toMonoidHom).comp
          (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 4 F).toMonoidHom := by
    rfl
  rw [hstep, ← Subgroup.map_map, ← Subgroup.map_map,
    CFSG.StandardType.RCKRP.irgL_rootGroup_map_slGraphAut highRoot_mem_roots,
    CFSG.StandardType.RCKRP.irgL_rootGroup_map_slFieldAut σ hneg]
  exact hv hneg


theorem rootR_marking_invariant (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = 4)
    (α : MulAut (Matrix.SpecialLinearGroup (Fin 4) F)) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (rootR F).map α.toMonoidHom =
        (rootR F).map (MulAut.conj g).toMonoidHom := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := by
    apply charP_of_card_eq_prime_pow (p := 2) (f := 2)
    rw [← Nat.card_eq_fintype_card, hF]
    norm_num
  obtain ⟨A, σ, ε, hε, hα⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_eq_std_of_mulAut_sl
      (n := 4) (K := F) (by norm_num) α
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · obtain ⟨v, hv⟩ := specialRootGroup_image_std_zero F A σ
    refine ⟨v, ?_⟩
    simp only [pow_zero, mul_one] at hα
    rw [rootR_eq_specialRootGroup, hα, hv]
  · obtain ⟨v, hv⟩ := specialRootGroup_image_std_one F A σ
    let w : Matrix.SpecialLinearGroup (Fin 4) F :=
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.signedPermutation 4 F (Equiv.swap 0 3)
    refine ⟨v * w, ?_⟩
    simp only [pow_one] at hα
    rw [rootR_eq_specialRootGroup, hα, hv]
    have hw :
        CFSG.LieType.Universal.SpecialLinear.rootGroup 3 F (-highRoot) =
          (CFSG.LieType.Universal.SpecialLinear.rootGroup 3 F highRoot).map
            (MulAut.conj w).toMonoidHom := by
      rw [← root30_eq_specialRootGroup_neg, ← rootR_eq_specialRootGroup]
      exact root30_eq_rootR_map_conj_swap F
    rw [hw, Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.mul_apply]

end CFSG.StandardType

namespace CFSG.StandardType

open CFSG.SeitzReduction.E6Pilot
open Matrix

variable {F : Type} [Field F]

private def n2BlockFourMatHom : Matrix (Fin 4) (Fin 4) F →* Matrix (Fin 6) (Fin 6) F where
  toFun := blockFourMat
  map_one' := blockFourMat_one
  map_mul' := blockFourMat_mul

private noncomputable def n2BlockFourGLHom : GL (Fin 4) F →* GL (Fin 6) F :=
  Units.map n2BlockFourMatHom

private noncomputable def n2BlockFourGL (A : GL (Fin 4) F) : GL (Fin 6) F :=
  n2BlockFourGLHom A

private theorem coe_n2BlockFourGL (A : GL (Fin 4) F) :
    ((n2BlockFourGL A : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = blockFourMat A := by
  rw [n2BlockFourGL, n2BlockFourGLHom, Units.coe_map]
  rfl

private theorem n2BlockFourGL_inv (A : GL (Fin 4) F) :
    (n2BlockFourGL A)⁻¹ = n2BlockFourGL A⁻¹ :=
  map_inv n2BlockFourGLHom A


private theorem blockFourMat_transpose (A : Matrix (Fin 4) (Fin 4) F) :
    blockFourMat Aᵀ = (blockFourMat A)ᵀ := by
  ext i j
  obtain ⟨x, rfl⟩ := e46.surjective i
  obtain ⟨y, rfl⟩ := e46.surjective j
  rw [blockFourMat_apply, Matrix.transpose_apply, blockFourMat_apply]
  rcases x with x | x <;> rcases y with y | y <;>
    simp [Matrix.fromBlocks, Matrix.one_apply, eq_comm]

private theorem blockFour_slFieldAut_apply (σ : F ≃+* F)
    (g : SpecialLinearGroup (Fin 4) F) :
    blockFour (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut
      (Fin 4) F σ g) =
      CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut
        (Fin 6) F σ (blockFour g) := by
  change blockFour (SpecialLinearGroup.map σ.toRingHom g) =
    SpecialLinearGroup.map σ.toRingHom (blockFour g)
  exact blockFour_map σ.toRingHom g

private theorem blockFour_slGraphAut_apply (g : SpecialLinearGroup (Fin 4) F) :
    blockFour (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 4 F g) =
      CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 6 F (blockFour g) := by
  apply Subtype.ext
  calc
    ((blockFour (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 4 F g) :
        SpecialLinearGroup (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)
        = (blockFourMat (((g⁻¹ : SpecialLinearGroup (Fin 4) F) :
            Matrix (Fin 4) (Fin 4) F)))ᵀ := by
          rw [coe_blockFour,
            CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut_matrix]
          exact blockFourMat_transpose _
    _ = ((((blockFour g)⁻¹ : SpecialLinearGroup (Fin 6) F) :
            Matrix (Fin 6) (Fin 6) F))ᵀ := by
          rw [← coe_blockFour (g⁻¹), ← map_inv blockFour g]
    _ = ((CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 6 F
          (blockFour g) : SpecialLinearGroup (Fin 6) F) :
            Matrix (Fin 6) (Fin 6) F) := by
          rw [CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut_matrix]


private theorem blockFour_slConjugation_apply (A : GL (Fin 4) F)
    (g : SpecialLinearGroup (Fin 4) F) :
    blockFour (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
      4 F A g) =
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
        6 F (n2BlockFourGL A) (blockFour g) := by
  apply Subtype.ext
  rw [coe_blockFour,
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix,
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix,
    coe_blockFour]
  rw [n2BlockFourGL_inv, coe_n2BlockFourGL, coe_n2BlockFourGL]
  rw [blockFourMat_mul, blockFourMat_mul]


private theorem blockFour_stdAut_apply (A : GL (Fin 4) F) (σ : F ≃+* F) (ε : ℕ) (hε : ε ≤ 1)
    (g : SpecialLinearGroup (Fin 4) F) :
    blockFour
      (((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 F A) *
        (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut
          (Fin 4) F σ) *
        (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 4 F) ^ ε) g) =
      (((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
          6 F (n2BlockFourGL A)) *
        (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut
          (Fin 6) F σ) *
        (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 6 F) ^ ε)
          (blockFour g)) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · simp only [pow_zero, mul_one, MulAut.mul_apply]
    rw [blockFour_slConjugation_apply, blockFour_slFieldAut_apply]
  · simp only [pow_one, MulAut.mul_apply]
    rw [blockFour_slConjugation_apply, blockFour_slFieldAut_apply,
      blockFour_slGraphAut_apply]

theorem sl4_exists_blockFour_extension (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = 4) (α : MulAut (Matrix.SpecialLinearGroup (Fin 4) F)) :
    ∃ β : MulAut (Matrix.SpecialLinearGroup (Fin 6) F),
      β.toMonoidHom.comp (blockFour (K := F)) =
        (blockFour (K := F)).comp α.toMonoidHom := by
  classical
  obtain ⟨A, σ, ε, hε, hα⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_eq_std_of_mulAut_sl
      (n := 4) (K := F) (by norm_num) α
  let β : MulAut (Matrix.SpecialLinearGroup (Fin 6) F) :=
    (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
      6 F (n2BlockFourGL A)) *
      (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 6) F σ) *
      (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 6 F) ^ ε
  refine ⟨β, ?_⟩
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  rw [hα]
  exact congrArg (fun x : Matrix.SpecialLinearGroup (Fin 6) F =>
      (x : Matrix (Fin 6) (Fin 6) F))
    (blockFour_stdAut_apply A σ ε hε g).symm

end CFSG.StandardType

namespace CFSG.StandardType

open Matrix

variable {F : Type} [Field F] [Finite F]

theorem sl6_ker_map_eq_of_le_center [CharP F 2] (hF : Nat.card F = 4)
    {Q : Type} [Group Q] (ψ : Matrix.SpecialLinearGroup (Fin 6) F →* Q)
    (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 6) F))
    (β : MulAut (Matrix.SpecialLinearGroup (Fin 6) F)) :
    ψ.ker.map β.toMonoidHom = ψ.ker := by
  classical
  let C : Subgroup (Matrix.SpecialLinearGroup (Fin 6) F) :=
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 6) F)
  have hcardC : Nat.card C = 3 := by
    dsimp [C]
    rw [CFSG.OrderReductions.LinearOrders.card_specialLinear_center F 6 (by norm_num), hF]
    norm_num
  have hcard_dvd : Nat.card ψ.ker ∣ 3 := by
    rw [← hcardC]
    exact Subgroup.card_dvd_of_le hker
  have hcard : Nat.card ψ.ker = 1 ∨ Nat.card ψ.ker = 3 :=
    (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hcard_dvd
  have hker_bot_or_top : ψ.ker = ⊥ ∨ ψ.ker = C := by
    rcases hcard with h1 | h3
    · left
      exact Subgroup.eq_bot_of_card_le ψ.ker (by omega)
    · right
      apply Subgroup.eq_of_le_of_card_ge hker
      rw [hcardC, h3]
  have hcenter_map : C.map β.toMonoidHom = C := by
    dsimp [C]
    simpa using (Subgroup.map_center_eq β)
  rcases hker_bot_or_top with hbot | htop
  · rw [hbot, Subgroup.map_bot]
  · rw [htop, hcenter_map]

theorem sl6_exists_quotient_aut_of_center_kernel [CharP F 2] (hF : Nat.card F = 4)
    {Q : Type} [Group Q] (ψ : Matrix.SpecialLinearGroup (Fin 6) F →* Q)
    (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 6) F))
    (β : MulAut (Matrix.SpecialLinearGroup (Fin 6) F)) :
    ∃ βQ : MulAut Q,
      βQ.toMonoidHom.comp ψ = ψ.comp β.toMonoidHom := by
  have hβker : ψ.ker.map β.toMonoidHom = ψ.ker :=
    sl6_ker_map_eq_of_le_center hF ψ hψ hker β
  obtain ⟨βQ, hβQ⟩ :=
    CFSG.Quasithin.ModG.exists_aut_of_ker ψ hψ β hβker
  refine ⟨βQ, ?_⟩
  apply MonoidHom.ext
  intro x
  exact hβQ x

end CFSG.StandardType

namespace CFSG.StandardType

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Glauberman Matrix

private theorem pointwiseCentralizer_solvable_of_centralizer_and_outer
    {G : Type*} [Group G] (M : Subgroup G)
    [Group.IsSolvable (Subgroup.centralizer (M : Set G))]
    [Group.IsSolvable (Outer G)] : Group.IsSolvable (pointwiseCentralizer M) := by
  let C := Subgroup.centralizer (M : Set G)
  let A := pointwiseCentralizer M
  let f : C →* A :=
    ((MulAut.conj : G →* MulAut G).comp C.subtype).codRestrict A (by
      intro c
      apply CFSG.Glauberman.mem_pointwiseCentralizer.mpr
      intro x hx
      change (c : G) * x * (c : G)⁻¹ = x
      rw [← Subgroup.mem_centralizer_iff.mp c.2 x hx]
      group)
  let q : A →* Outer G := (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner G)).comp A.subtype
  apply Group.isSolvable_of_ker_le_range f q
  intro a ha
  have hai : (a : MulAut G) ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner G :=
    (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp ha)
  obtain ⟨g, hg⟩ := hai
  have hgC : g ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hfix : (a : MulAut G) x = x := CFSG.Glauberman.mem_pointwiseCentralizer.mp a.2 x hx
    rw [← hg] at hfix
    change g * x * g⁻¹ = x at hfix
    exact (mul_inv_eq_iff_eq_mul.mp hfix).symm
  exact ⟨⟨g, hgC⟩, Subtype.ext hg⟩

theorem sl4_pointwiseCentralizer_coordSL3_solvable
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4) (i₀ : Fin 4) :
    Group.IsSolvable (pointwiseCentralizer
      (CFSG.RankThree.CALinearPlane.coordBlockSL F ({i₀}ᶜ : Finset (Fin 4)))) := by
  let S := Matrix.SpecialLinearGroup (Fin 4) F
  let M : Subgroup S := CFSG.RankThree.CALinearPlane.coordBlockSL F
    ({i₀}ᶜ : Finset (Fin 4))
  let C := Subgroup.centralizer (M : Set S)
  have hdiag : ∀ g : C, ((g : S) : Matrix (Fin 4) (Fin 4) F) =
      Matrix.diagonal (fun i => ((g : S) : Matrix (Fin 4) (Fin 4) F) i i) := by
    intro g
    apply (tpta_commutant_coordBlockSL_diag (K := F) (d := 4) (i₀ := i₀)
      (by norm_num) (h := Matrix.SpecialLinearGroup.toGL (g : S)) ?_).1
    intro j hj
    have hcomm : j * (g : S) = (g : S) * j :=
      Subgroup.mem_centralizer_iff.mp g.2 j hj
    exact congrArg (fun z : S => (z : Matrix (Fin 4) (Fin 4) F)) hcomm.symm
  letI : Group.IsSolvable C := Group.isSolvable_of_comm (by
    intro g h
    apply Subtype.ext
    apply Subtype.ext
    change ((g : S) : Matrix (Fin 4) (Fin 4) F) *
        ((h : S) : Matrix (Fin 4) (Fin 4) F) =
      ((h : S) : Matrix (Fin 4) (Fin 4) F) * ((g : S) : Matrix (Fin 4) (Fin 4) F)
    rw [hdiag g, hdiag h, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _)
  let P := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 4 F
  have hOutPcard : Nat.card (Outer P) ≤ 4 := Nat.le_of_dvd (by norm_num)
    (CFSG.OddStandard.AltStdSec.card_outer_dvd_four hF)
  letI : Group.IsSolvable (Outer P) :=
    CFSG.ComponentClassification.CatalogueSchreierAlternating.solvable_of_card_le_four hOutPcard
  letI : Group.IsSolvable (Outer S) :=
    CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSLFourEquivSL F)
  exact pointwiseCentralizer_solvable_of_centralizer_and_outer M

theorem sl4_perfect_action_fixing_coordSL3_eq_one
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4) (i₀ : Fin 4)
    {P : Type*} [Group P] [Group.IsPerfect P]
    (α : P →* MulAut (Matrix.SpecialLinearGroup (Fin 4) F))
    (hfix : ∀ g : P, ∀ x ∈ CFSG.RankThree.CALinearPlane.coordBlockSL F
      ({i₀}ᶜ : Finset (Fin 4)), α g x = x) (g : P) : α g = 1 := by
  let M := CFSG.RankThree.CALinearPlane.coordBlockSL F ({i₀}ᶜ : Finset (Fin 4))
  let C := pointwiseCentralizer M
  letI : Group.IsSolvable C := sl4_pointwiseCentralizer_coordSL3_solvable F hF i₀
  let f : P →* C := α.codRestrict C (fun g => CFSG.Glauberman.mem_pointwiseCentralizer.mpr (hfix g))
  exact congrArg Subtype.val
    (CFSG.LocalAnalysis.GLTheoremA.T123CB.eq_one_of_perfect_of_isSolvable f g)

theorem sl4_pointwiseCentralizer_actualSL3_solvable
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4) (i₀ : Fin 4)
    {J : Type*} [Group J] (e : Matrix.SpecialLinearGroup (Fin 4) F ≃* J) :
    Group.IsSolvable (pointwiseCentralizer
      ((CFSG.RankThree.CALinearPlane.coordBlockSL F ({i₀}ᶜ : Finset (Fin 4))).map
        e.toMonoidHom)) := by
  let M := CFSG.RankThree.CALinearPlane.coordBlockSL F ({i₀}ᶜ : Finset (Fin 4))
  let A := pointwiseCentralizer (M.map e.toMonoidHom)
  let C := pointwiseCentralizer M
  letI : Group.IsSolvable C := sl4_pointwiseCentralizer_coordSL3_solvable F hF i₀
  let f : A →* C := ((MulAut.congr e.symm).toMonoidHom.comp A.subtype).codRestrict C (by
    intro a
    apply CFSG.Glauberman.mem_pointwiseCentralizer.mpr
    intro x hx
    have hfix := CFSG.Glauberman.mem_pointwiseCentralizer.mp a.2 (e x)
      (Subgroup.mem_map_of_mem e.toMonoidHom hx)
    change e.symm ((a : MulAut J) (e x)) = x
    rw [hfix, e.symm_apply_apply])
  apply Group.isSolvable_of_isSolvable_injective (f := f)
  intro a b hab
  have h' := congrArg Subtype.val hab
  apply Subtype.ext
  exact (MulAut.congr e.symm).injective h'

end CFSG.StandardType

namespace CFSG.StandardType
open Matrix CFSG.ComponentClassification.CatalogueBHigherLinearAction

theorem sl4_slConjugation_eq_inner (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = 4) (A : GL (Fin 4) F) :
    ∃ s : Matrix.SpecialLinearGroup (Fin 4) F,
      slConjugation 4 F A = MulAut.conj s := by
  let u : Fˣ := (GeneralLinearGroup.det A)⁻¹
  have hu3 : u ^ 3 = 1 := by
    have h := pow_card_eq_one' (x := u)
    simpa [Nat.card_units, hF] using h
  let B : GL (Fin 4) F := GeneralLinearGroup.scalar (Fin 4) u * A
  have hB : GeneralLinearGroup.det B = 1 := by
    dsimp [B]
    rw [map_mul, GeneralLinearGroup.det_scalar]
    simp only [Fintype.card_fin]
    rw [show u ^ 4 = u by rw [pow_succ, hu3, one_mul]]
    exact inv_mul_cancel _
  let s : Matrix.SpecialLinearGroup (Fin 4) F :=
    ⟨(B : Matrix (Fin 4) (Fin 4) F), by
      have h := congrArg (fun x : Fˣ => (x : F)) hB
      simpa [GeneralLinearGroup.val_det_apply] using h⟩
  have hs : Matrix.SpecialLinearGroup.toGL s = B := by
    apply Units.ext
    rfl
  refine ⟨s, ?_⟩
  have hBA : slConjugation 4 F B = slConjugation 4 F A := by
    dsimp [B]
    rw [map_mul, slConjugation_scalar, one_mul]
  rw [← hBA, ← hs]
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  rw [slConjugation_matrix]
  rfl

open CFSG.RankThree.CALinearPlane
open CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.ComponentClassification.CatalogueBGraphForm

private theorem n2_coordBlockSL_mem_slFieldAut
    {F : Type} [Field F] {n : ℕ} (σ : F ≃+* F)
    {S : Finset (Fin n)} {g : Matrix.SpecialLinearGroup (Fin n) F}
    (hg : g ∈ coordBlockSL F S) : slFieldAut (Fin n) F σ g ∈ coordBlockSL F S := by
  rw [mem_coordBlockSL_iff] at hg ⊢
  intro i j hij
  change σ ((g : Matrix (Fin n) (Fin n) F) i j) = (1 : Matrix (Fin n) (Fin n) F) i j
  rw [hg i j hij]
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

private theorem n2_coordBlockSL_map_slFieldAut
    {F : Type} [Field F] {n : ℕ} (σ : F ≃+* F) (S : Finset (Fin n)) :
    (coordBlockSL F S).map (slFieldAut (Fin n) F σ).toMonoidHom = coordBlockSL F S := by
  apply le_antisymm
  · rintro g ⟨x,hx,rfl⟩
    exact n2_coordBlockSL_mem_slFieldAut σ hx
  · intro g hg
    refine Subgroup.mem_map.mpr ⟨slFieldAut (Fin n) F σ.symm g,
      n2_coordBlockSL_mem_slFieldAut σ.symm hg, ?_⟩
    apply Subtype.ext
    ext i j
    exact σ.apply_symm_apply _

private theorem n2_coordBlockSL_mem_slGraphAut
    {F : Type} [Field F] {n : ℕ}
    {S : Finset (Fin n)} {g : Matrix.SpecialLinearGroup (Fin n) F}
    (hg : g ∈ coordBlockSL F S) : slGraphAut n F g ∈ coordBlockSL F S := by
  rw [mem_coordBlockSL_iff]
  intro i j hij
  rw [slGraphAut_matrix]
  have h := mem_coordBlockSL_iff.mp ((coordBlockSL F S).inv_mem hg) j i (hij.elim Or.inr Or.inl)
  simpa [Matrix.transpose_apply, Matrix.one_apply, eq_comm] using h

private theorem n2_coordBlockSL_map_slGraphAut
    {F : Type} [Field F] {n : ℕ} (S : Finset (Fin n)) :
    (coordBlockSL F S).map (slGraphAut n F).toMonoidHom = coordBlockSL F S := by
  apply le_antisymm
  · rintro g ⟨x,hx,rfl⟩
    exact n2_coordBlockSL_mem_slGraphAut hx
  · intro g hg
    refine Subgroup.mem_map.mpr ⟨slGraphAut n F g, n2_coordBlockSL_mem_slGraphAut hg, ?_⟩
    have hsq : slGraphAut n F * slGraphAut n F = 1 := by
      simpa [pow_two] using slGraphAut_sq n F
    change (slGraphAut n F) ((slGraphAut n F) g) = g
    rw [← MulAut.mul_apply, hsq]
    rfl

theorem sl4_coordSL3_marking_invariant (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = 4) (i₀ : Fin 4)
    (α : MulAut (Matrix.SpecialLinearGroup (Fin 4) F)) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (coordBlockSL F ({i₀}ᶜ : Finset (Fin 4))).map α.toMonoidHom =
        (coordBlockSL F ({i₀}ᶜ : Finset (Fin 4))).map (MulAut.conj g).toMonoidHom := by
  classical
  obtain ⟨A, σ, ε, hε, hα⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_eq_std_of_mulAut_sl (n := 4) (K := F) (by norm_num) α
  obtain ⟨g, hg⟩ := sl4_slConjugation_eq_inner F hF A
  refine ⟨g, ?_⟩
  rw [hα]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · simp only [pow_zero, mul_one]
    change (coordBlockSL F ({i₀}ᶜ : Finset (Fin 4))).map
      ((slConjugation 4 F A).toMonoidHom.comp (slFieldAut (Fin 4) F σ).toMonoidHom) = _
    rw [← Subgroup.map_map, n2_coordBlockSL_map_slFieldAut, hg]
  · simp only [pow_one]
    change (coordBlockSL F ({i₀}ᶜ : Finset (Fin 4))).map
      (((slConjugation 4 F A).toMonoidHom.comp (slFieldAut (Fin 4) F σ).toMonoidHom).comp
        (slGraphAut 4 F).toMonoidHom) = _
    rw [← Subgroup.map_map, ← Subgroup.map_map, n2_coordBlockSL_map_slGraphAut,
      n2_coordBlockSL_map_slFieldAut, hg]

open CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.ComponentClassification.CatalogueBGraphForm

theorem sl4_fieldFree_innerGraph_marking_invariant
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    (α : MulAut (SpecialLinearGroup (Fin 4) F))
    (s : SpecialLinearGroup (Fin 4) F) {δ : ℕ} (hδ : δ ≤ 1) :
    ∃ s' : SpecialLinearGroup (Fin 4) F,
      α * (MulAut.conj s * slGraphAut 4 F ^ δ) * α⁻¹ =
        MulAut.conj s' * slGraphAut 4 F ^ δ := by
  classical
  let S := SpecialLinearGroup (Fin 4) F
  let d : MulAut S := slGraphAut 4 F
  have hn (β : MulAut S) (t : S) :
      β * MulAut.conj t * β⁻¹ = MulAut.conj (β t) := by
    apply DFunLike.ext
    intro x
    change β (t * β.symm x * t⁻¹) = β t * x * (β t)⁻¹
    simp only [map_mul, MulEquiv.map_inv, β.apply_symm_apply]
  obtain ⟨A, σ, ε, _hε, hα⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_eq_std_of_mulAut_sl (by norm_num : 3 ≤ 4) α
  obtain ⟨r, hr⟩ := sl4_slConjugation_eq_inner F hF A
  let f : MulAut S := slFieldAut (Fin 4) F σ
  let b : MulAut S := f * d ^ ε
  have hαb : α = MulAut.conj r * b := by
    rw [hα, hr]
    rfl
  have hfd : Commute f d := by
    show f * d = d * f
    apply DFunLike.ext
    intro x
    exact (slGraphAut_field_commute 4 F σ x).symm
  have hbd : Commute b d := by
    show (f * d ^ ε) * d = d * (f * d ^ ε)
    calc
      (f * d ^ ε) * d = f * (d ^ ε * d) := mul_assoc _ _ _
      _ = f * (d * d ^ ε) := by rw [(Commute.refl d).pow_left ε |>.eq]
      _ = (f * d) * d ^ ε := (mul_assoc _ _ _).symm
      _ = (d * f) * d ^ ε := by rw [hfd.eq]
      _ = d * (f * d ^ ε) := mul_assoc _ _ _
  let u : S := r * d (r⁻¹)
  have hgraph : α * d * α⁻¹ = MulAut.conj u * d := by
    have hb : b * d * b⁻¹ = d := by rw [hbd.eq]; group
    have hd : d * MulAut.conj (r⁻¹) = MulAut.conj (d (r⁻¹)) * d :=
      mul_inv_eq_iff_eq_mul.mp (hn d (r⁻¹))
    calc
      α * d * α⁻¹ = MulAut.conj r * (b * d * b⁻¹) * (MulAut.conj r)⁻¹ := by
        rw [hαb]; group
      _ = MulAut.conj r * d * (MulAut.conj r)⁻¹ := by rw [hb]
      _ = MulAut.conj r * (d * MulAut.conj (r⁻¹)) := by rw [map_inv]; group
      _ = MulAut.conj r * (MulAut.conj (d (r⁻¹)) * d) := by rw [hd]
      _ = MulAut.conj u * d := by dsimp [u]; rw [map_mul]; group
  interval_cases δ
  · refine ⟨α s, ?_⟩
    simpa using hn α s
  · refine ⟨α s * u, ?_⟩
    simp only [pow_one]
    change α * (MulAut.conj s * d) * α⁻¹ = MulAut.conj (α s * u) * d
    calc
      α * (MulAut.conj s * d) * α⁻¹ =
          (α * MulAut.conj s * α⁻¹) * (α * d * α⁻¹) := by group
      _ = MulAut.conj (α s) * (MulAut.conj u * d) := by rw [hn, hgraph]
      _ = MulAut.conj (α s * u) * d := by
        rw [map_mul (MulAut.conj : S →* MulAut S) (α s) u]
        group

theorem sl4_fieldFree_GLGraph_marking_invariant
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    (α : MulAut (SpecialLinearGroup (Fin 4) F))
    (C : GL (Fin 4) F) {δ : ℕ} (hδ : δ ≤ 1) :
    ∃ C' : GL (Fin 4) F,
      α * (slConjugation 4 F C * slGraphAut 4 F ^ δ) * α⁻¹ =
        slConjugation 4 F C' * slGraphAut 4 F ^ δ := by
  obtain ⟨s, hs⟩ := sl4_slConjugation_eq_inner F hF C
  obtain ⟨s', h⟩ := sl4_fieldFree_innerGraph_marking_invariant hF α s hδ
  refine ⟨SpecialLinearGroup.toGL s', ?_⟩
  rw [hs, CFSG.GH74.Generic.S1.slConj_toGL]
  exact h


end CFSG.StandardType


public section

namespace CFSG.StandardType.N2KFieldCoefficient

open Matrix
open CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBGraphForm
open scoped MatrixGroups

noncomputable section

abbrev F4 : Type := GaloisField 2 2
abbrev GL6F4 : Type := Matrix.GeneralLinearGroup (Fin 6) F4
abbrev SL6F4 : Type := Matrix.SpecialLinearGroup (Fin 6) F4

abbrev root01 : (0 : Fin 6) ≠ 1 := by decide
abbrev root10 : (1 : Fin 6) ≠ 0 := by decide

abbrev rootTransvection (t : F4) : SL6F4 :=
  SpecialLinearGroup.transvection root01 t

abbrev slConjugation6 (A : GL6F4) : MulAut SL6F4 :=
  slConjugation 6 F4 A

abbrev slFieldAut6 (σ : F4 ≃+* F4) : MulAut SL6F4 :=
  slFieldAut (Fin 6) F4 σ

abbrev slGraphAut6 : MulAut SL6F4 :=
  slGraphAut 6 F4

@[expose] noncomputable def fieldDetectionBeta (A : GL6F4) (σ : F4 ≃+* F4) (ε : ℕ) :
    MulAut SL6F4 :=
  slConjugation6 A * slFieldAut6 σ * (slGraphAut6) ^ ε

noncomputable def rootDirection (ε : ℕ) : Matrix (Fin 6) (Fin 6) F4 :=
  if ε = 0 then Matrix.single (0 : Fin 6) 1 1 else Matrix.single (1 : Fin 6) 0 1

private lemma fieldAut_transvection (σ : F4 ≃+* F4) {i j : Fin 6} (hij : i ≠ j) (t : F4) :
    ((slFieldAut6 σ (SpecialLinearGroup.transvection hij t) : SL6F4) :
      Matrix (Fin 6) (Fin 6) F4) =
      1 + σ t • Matrix.single i j 1 := by
  change ((slFieldEquiv (Fin 6) σ
    (SpecialLinearGroup.transvection hij t) : SL6F4) : Matrix (Fin 6) (Fin 6) F4) = _
  ext a b
  rw [slFieldEquiv_entry]
  rw [SpecialLinearGroup.transvection_coe]
  by_cases h : a = i ∧ b = j
  · rcases h with ⟨rfl, rfl⟩
    simp [Matrix.smul_apply, Matrix.single, Matrix.one_apply]
  · have h' : ¬ (i = a ∧ j = b) := by
      intro hh
      exact h ⟨hh.1.symm, hh.2.symm⟩
    simp [Matrix.smul_apply, Matrix.single, Matrix.one_apply, h, h']

private lemma graphAut_transvection (t : F4) :
    ((slGraphAut6 (rootTransvection t) : SL6F4) : Matrix (Fin 6) (Fin 6) F4) =
      1 + t • Matrix.single (1 : Fin 6) 0 1 := by
  rw [slGraphAut_matrix]
  have hinv : (rootTransvection t)⁻¹ =
      SpecialLinearGroup.transvection root01 (-t) :=
    SpecialLinearGroup.transvection_inv root01 t
  rw [hinv]
  rw [show (-t : F4) = t by rw [CharTwo.neg_eq]]
  rw [SpecialLinearGroup.transvection_coe]
  rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single]
  ext a b
  simp [Matrix.smul_apply, Matrix.single, Matrix.one_apply]

set_option maxHeartbeats 1000000 in
private lemma conjugation_transvection (A : GL6F4) {i j : Fin 6} (hij : i ≠ j) (t : F4) :
    ((slConjugation6 A (SpecialLinearGroup.transvection hij t) : SL6F4) :
      Matrix (Fin 6) (Fin 6) F4) =
      1 + t • ((A : Matrix (Fin 6) (Fin 6) F4) * Matrix.single i j 1 *
        ((A⁻¹ : GL6F4) : Matrix (Fin 6) (Fin 6) F4)) := by
  rw [slConjugation_matrix]
  rw [SpecialLinearGroup.transvection_coe]
  let E : Matrix (Fin 6) (Fin 6) F4 := Matrix.single i j 1
  have hAA : ((A : Matrix (Fin 6) (Fin 6) F4) * ((A⁻¹ : GL6F4) :
      Matrix (Fin 6) (Fin 6) F4)) = 1 := Units.mul_inv A
  rw [show Matrix.single i j t = t • E by
    change Matrix.single i j t = t • Matrix.single i j 1
    rw [Matrix.smul_single]
    simp]
  calc
    ((A : Matrix (Fin 6) (Fin 6) F4) * (1 + t • E) *
        ((A⁻¹ : GL6F4) : Matrix (Fin 6) (Fin 6) F4)) =
        (((A : Matrix (Fin 6) (Fin 6) F4) * 1 +
          (A : Matrix (Fin 6) (Fin 6) F4) * (t • E)) *
            ((A⁻¹ : GL6F4) : Matrix (Fin 6) (Fin 6) F4)) := by
      rw [Matrix.mul_add]
    _ = (((A : Matrix (Fin 6) (Fin 6) F4) +
          (A : Matrix (Fin 6) (Fin 6) F4) * (t • E)) *
            ((A⁻¹ : GL6F4) : Matrix (Fin 6) (Fin 6) F4)) := by
      rw [Matrix.mul_one]
    _ = ((A : Matrix (Fin 6) (Fin 6) F4) * ((A⁻¹ : GL6F4) :
          Matrix (Fin 6) (Fin 6) F4)) +
          (((A : Matrix (Fin 6) (Fin 6) F4) * (t • E)) *
            ((A⁻¹ : GL6F4) : Matrix (Fin 6) (Fin 6) F4)) := by
      rw [Matrix.add_mul]
    _ = 1 + (((A : Matrix (Fin 6) (Fin 6) F4) * (t • E)) *
          ((A⁻¹ : GL6F4) : Matrix (Fin 6) (Fin 6) F4)) := by
      rw [hAA]
    _ = 1 + ((t • ((A : Matrix (Fin 6) (Fin 6) F4) * E)) *
          ((A⁻¹ : GL6F4) : Matrix (Fin 6) (Fin 6) F4)) := by
      rw [Algebra.mul_smul_comm]
    _ = 1 + (t • (((A : Matrix (Fin 6) (Fin 6) F4) * E) *
          ((A⁻¹ : GL6F4) : Matrix (Fin 6) (Fin 6) F4))) := by
      rw [Algebra.smul_mul_assoc]
    _ = 1 + t • ((A : Matrix (Fin 6) (Fin 6) F4) *
          Matrix.single i j 1 *
            ((A⁻¹ : GL6F4) : Matrix (Fin 6) (Fin 6) F4)) := by
      rw [Matrix.mul_assoc]


private lemma fieldAut_transvection_eq (σ : F4 ≃+* F4) {i j : Fin 6} (hij : i ≠ j) (t : F4) :
    slFieldAut6 σ (SpecialLinearGroup.transvection hij t) =
      SpecialLinearGroup.transvection hij (σ t) := by
  apply Subtype.ext
  rw [fieldAut_transvection, SpecialLinearGroup.transvection_coe]
  rw [Matrix.smul_single]
  simp

private lemma graphAut_transvection_eq (t : F4) :
    slGraphAut6 (rootTransvection t) =
      SpecialLinearGroup.transvection root10 t := by
  apply Subtype.ext
  rw [graphAut_transvection, SpecialLinearGroup.transvection_coe]
  rw [Matrix.smul_single]
  simp

private lemma beta_root_matrix (A : GL6F4) (σ : F4 ≃+* F4) {ε : ℕ} (hε : ε ≤ 1)
    (t : F4) :
    ((fieldDetectionBeta A σ ε (rootTransvection t) : SL6F4) :
      Matrix (Fin 6) (Fin 6) F4) =
      1 + σ t • ((A : Matrix (Fin 6) (Fin 6) F4) * rootDirection ε *
        ((A⁻¹ : GL6F4) : Matrix (Fin 6) (Fin 6) F4)) := by
  interval_cases ε
  · have hbeta : fieldDetectionBeta A σ 0 = slConjugation6 A * slFieldAut6 σ := by
      simp [fieldDetectionBeta]
    rw [hbeta, MulAut.mul_apply]
    rw [fieldAut_transvection_eq σ root01 t]
    rw [conjugation_transvection A root01 (σ t)]
    simp [rootDirection]
  · have hbeta : fieldDetectionBeta A σ 1 =
        slConjugation6 A * slFieldAut6 σ * slGraphAut6 := by
      simp [fieldDetectionBeta]
    rw [hbeta, MulAut.mul_apply, MulAut.mul_apply]
    rw [graphAut_transvection_eq t]
    rw [fieldAut_transvection_eq σ root10 t]
    rw [conjugation_transvection A root10 (σ t)]
    simp [rootDirection]


theorem sigma_eq_refl_of_root_linear
    (A : GL6F4) (σ : F4 ≃+* F4) {ε : ℕ} (hε : ε ≤ 1)
    (hlin : ∀ t : F4,
      ((fieldDetectionBeta A σ ε (rootTransvection t) : SL6F4) :
        Matrix (Fin 6) (Fin 6) F4) =
        1 + t • (((fieldDetectionBeta A σ ε (rootTransvection 1) : SL6F4) :
          Matrix (Fin 6) (Fin 6) F4) - 1)) :
    σ = RingEquiv.refl F4 := by
  let D : Matrix (Fin 6) (Fin 6) F4 :=
    (A : Matrix (Fin 6) (Fin 6) F4) * rootDirection ε *
      ((A⁻¹ : GL6F4) : Matrix (Fin 6) (Fin 6) F4)
  have hformula : ∀ t : F4,
      ((fieldDetectionBeta A σ ε (rootTransvection t) : SL6F4) :
        Matrix (Fin 6) (Fin 6) F4) = 1 + σ t • D := by
    intro t
    simpa [D] using beta_root_matrix A σ hε t
  have hbeta1 : ((fieldDetectionBeta A σ ε (rootTransvection 1) : SL6F4) :
      Matrix (Fin 6) (Fin 6) F4) = 1 + D := by
    simpa using hformula 1
  have htv1 : rootTransvection 1 ≠ (1 : SL6F4) := by
    intro h
    have hentry := congrArg (fun g : SL6F4 => ((g : SL6F4) :
      Matrix (Fin 6) (Fin 6) F4) 0 1) h
    have hleft : ((rootTransvection 1 : SL6F4) :
        Matrix (Fin 6) (Fin 6) F4) 0 1 = 1 := by
      simp [rootTransvection, SpecialLinearGroup.transvection_coe]
    have hright : (((1 : SL6F4) : Matrix (Fin 6) (Fin 6) F4) 0 1) = 0 := by
      simp
    rw [hleft, hright] at hentry
    exact one_ne_zero hentry
  have hbeta1ne : fieldDetectionBeta A σ ε (rootTransvection 1) ≠ 1 := by
    intro h
    have h' : fieldDetectionBeta A σ ε (rootTransvection 1) =
        fieldDetectionBeta A σ ε 1 := by
      simpa using h
    exact htv1 ((fieldDetectionBeta A σ ε).injective h')
  have hDne : D ≠ 0 := by
    intro hD
    apply hbeta1ne
    apply Subtype.ext
    rw [hbeta1, hD, add_zero]
    rfl
  have hD_eq : ∀ t : F4, σ t • D = t • D := by
    intro t
    have h := hlin t
    rw [hformula t] at h
    have hsub : ((1 + D : Matrix (Fin 6) (Fin 6) F4) - 1) = D := by
      abel
    rw [hbeta1, hsub] at h
    exact add_left_cancel h
  have hD_entry : ∃ i j : Fin 6, D i j ≠ 0 := by
    by_contra h
    push Not at h
    apply hDne
    ext i j
    exact h i j
  obtain ⟨i, j, hij⟩ := hD_entry
  have hσt : ∀ t : F4, σ t = t := by
    intro t
    have h := congrFun (congrFun (hD_eq t) i) j
    have h' : σ t * D i j = t * D i j := by
      simpa [Matrix.smul_apply] using h
    exact mul_right_cancel₀ hij h'
  apply RingEquiv.ext
  intro t
  exact hσt t

theorem sigma_eq_refl_of_root_fixed
    (A : GL6F4) (σ : F4 ≃+* F4) {ε : ℕ} (hε : ε ≤ 1)
    (hfix : ∀ t : F4,
      fieldDetectionBeta A σ ε (rootTransvection t) = rootTransvection t) :
    σ = RingEquiv.refl F4 := by
  apply sigma_eq_refl_of_root_linear A σ hε
  intro t
  have ht := congrArg (fun g : SL6F4 => ((g : SL6F4) :
    Matrix (Fin 6) (Fin 6) F4)) (hfix t)
  have h1 := congrArg (fun g : SL6F4 => ((g : SL6F4) :
    Matrix (Fin 6) (Fin 6) F4)) (hfix 1)
  rw [ht, h1]
  rw [rootTransvection, SpecialLinearGroup.transvection_coe]
  rw [rootTransvection, SpecialLinearGroup.transvection_coe]
  have hsub : ((1 + Matrix.single (0 : Fin 6) 1 1 : Matrix (Fin 6) (Fin 6) F4) - 1) =
      Matrix.single (0 : Fin 6) 1 1 := by
    abel
  rw [hsub]
  rw [Matrix.smul_single]
  simp

end

end CFSG.StandardType.N2KFieldCoefficient


public section

namespace CFSG.StandardType.N2KActualAutomorphism

open Matrix
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

noncomputable section

variable {F : Type} [Field F] [Finite F] [CharP F 2]

abbrev SL6F (F : Type) [Field F] : Type := Matrix.SpecialLinearGroup (Fin 6) F
abbrev PSL6F (F : Type) [Field F] : Type := projectiveSL 6 F

private theorem ker_eq_bot_or_center
    (hF : Nat.card F = 4) {Q : Type} [Group Q]
    (ψ : SL6F F →* Q) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center (SL6F F)) :
    ψ.ker = ⊥ ∨ ψ.ker = Subgroup.center (SL6F F) := by
  classical
  have hcardC : Nat.card (Subgroup.center (SL6F F)) = 3 := by
    dsimp [SL6F]
    rw [CFSG.OrderReductions.LinearOrders.card_specialLinear_center F 6 (by norm_num), hF]
    norm_num
  have hcard_dvd : Nat.card ψ.ker ∣ 3 := by
    rw [← hcardC]
    exact Subgroup.card_dvd_of_le hker
  have hcard : Nat.card ψ.ker = 1 ∨ Nat.card ψ.ker = 3 :=
    (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hcard_dvd
  rcases hcard with h1 | h3
  · left
    exact Subgroup.eq_bot_of_card_le ψ.ker (by omega)
  · right
    apply Subgroup.eq_of_le_of_card_ge hker
    rw [hcardC, h3]

private theorem exists_quotient_equiv_projective
    {Q : Type} [Group Q] (ψ : SL6F F →* Q) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = Subgroup.center (SL6F F)) :
    ∃ e : Q ≃* PSL6F F, ∀ g : SL6F F, e (ψ g) = proj 6 F g := by
  classical
  let S := SL6F F
  let P := PSL6F F
  let π : S →* P := proj 6 F
  have hkerπ : ψ.ker = π.ker := by
    dsimp [π, S, P]
    rw [ker_proj, scalars_eq_center]
    exact hker
  let eψ : S ⧸ ψ.ker ≃* Q :=
    QuotientGroup.liftEquiv (N := ψ.ker) hψ rfl
  let eπ : S ⧸ π.ker ≃* P :=
    QuotientGroup.liftEquiv (N := π.ker) (proj_surjective 6 F) rfl
  let c : S ⧸ ψ.ker ≃* S ⧸ π.ker :=
    QuotientGroup.quotientMulEquivOfEq hkerπ
  refine ⟨eψ.symm.trans (c.trans eπ), ?_⟩
  intro g
  have hψg : eψ.symm (ψ g) = QuotientGroup.mk g := by
    rw [← QuotientGroup.liftEquiv_mk (N := ψ.ker) hψ rfl g]
    exact eψ.symm_apply_apply _
  have hc : c (QuotientGroup.mk g) = QuotientGroup.mk g :=
    QuotientGroup.quotientMulEquivOfEq_mk hkerπ g
  have hπg : eπ (QuotientGroup.mk g) = π g :=
    QuotientGroup.liftEquiv_mk (N := π.ker) (proj_surjective 6 F) rfl g
  simp only [MulEquiv.trans_apply]
  rw [hψg, hc, hπg]


private theorem exists_std_lift_of_ker_bot
    {Q : Type} [Group Q] (ψ : SL6F F →* Q) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = ⊥) (αQ : MulAut Q) :
    ∃ (A : GL (Fin 6) F) (σ : F ≃+* F) (ε : ℕ), ε ≤ 1 ∧
      ∀ g : SL6F F,
        αQ (ψ g) = ψ
          (((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 6 F A) *
            (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 6) F σ) *
            (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 6 F) ^ ε) g) := by
  classical
  have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hker
  let e : SL6F F ≃* Q := MulEquiv.ofBijective ψ ⟨hinj, hψ⟩
  let β : MulAut (SL6F F) := MulAut.congr e.symm αQ
  obtain ⟨A, σ, ε, hε, hβ⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_eq_std_of_mulAut_sl
      (n := 6) (K := F) (by norm_num) β
  let std : MulAut (SL6F F) :=
    (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 6 F A) *
      (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 6) F σ) *
      (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 6 F) ^ ε
  refine ⟨A, σ, ε, hε, ?_⟩
  change ∀ g : SL6F F, αQ (ψ g) = ψ (std g)
  intro g
  have hβg : β g = e.symm (αQ (e g)) := by
    simp [β, MulAut.congr_apply]
  have hcongr : e (β g) = αQ (e g) := by
    rw [hβg]
    exact e.apply_symm_apply (αQ (e g))
  calc
    αQ (ψ g) = e (β g) := by
      rw [hcongr]
      rfl
    _ = e (std g) := by rw [hβ]
    _ = ψ (std g) := rfl


private theorem exists_std_lift_of_ker_center
    {Q : Type} [Group Q] (ψ : SL6F F →* Q) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = Subgroup.center (SL6F F)) (αQ : MulAut Q) :
    ∃ (A : GL (Fin 6) F) (σ : F ≃+* F) (ε : ℕ), ε ≤ 1 ∧
      ∀ g : SL6F F,
        αQ (ψ g) = ψ
          (((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 6 F A) *
            (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 6) F σ) *
            (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 6 F) ^ ε) g) := by
  classical
  obtain ⟨e, he⟩ := exists_quotient_equiv_projective ψ hψ hker
  let αP : MulAut (PSL6F F) := MulAut.congr e αQ
  obtain ⟨A, σ, ε, hε, hgen⟩ :=
    (automorphism_generation (K := F) (n := 6) (by norm_num)).2 αP
  let std : MulAut (SL6F F) :=
    (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 6 F A) *
      (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 6) F σ) *
      (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 6 F) ^ ε
  have hdesc : descendAut 6 F std =
      conjAut 6 F A * fieldAut 6 F σ * dualAut 6 F ^ ε := by
    dsimp [std]
    rw [map_mul, map_mul, map_pow]
    rfl
  refine ⟨A, σ, ε, hε, ?_⟩
  change ∀ g : SL6F F, αQ (ψ g) = ψ (std g)
  intro g
  apply e.injective
  have hαP : αP (e (ψ g)) = e (αQ (ψ g)) := by
    simp [αP, MulAut.congr_apply]
  calc
    e (αQ (ψ g)) = αP (e (ψ g)) := hαP.symm
    _ = αP (proj 6 F g) := by rw [he g]
    _ = (conjAut 6 F A * fieldAut 6 F σ * dualAut 6 F ^ ε) (proj 6 F g) := by
      rw [hgen]
    _ = descendAut 6 F std (proj 6 F g) := by rw [hdesc]
    _ = proj 6 F (std g) := descendAut_proj 6 F std g
    _ = e (ψ (std g)) := by rw [he (std g)]


theorem exists_std_lift_of_central_kernel
    (hF : Nat.card F = 4) {Q : Type} [Group Q]
    (ψ : SL6F F →* Q) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center (SL6F F)) (αQ : MulAut Q) :
    ∃ (A : GL (Fin 6) F) (σ : F ≃+* F) (ε : ℕ), ε ≤ 1 ∧
      ∀ g : SL6F F,
        αQ (ψ g) = ψ
          (((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 6 F A) *
            (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 6) F σ) *
            (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 6 F) ^ ε) g) := by
  rcases ker_eq_bot_or_center hF ψ hψ hker with hbot | hcenter
  · exact exists_std_lift_of_ker_bot ψ hψ hbot αQ
  · exact exists_std_lift_of_ker_center ψ hψ hcenter αQ

end

end CFSG.StandardType.N2KActualAutomorphism


public section

namespace CFSG.StandardType.N2KFieldCoefficient
open Matrix CFSG.SeitzReduction.E6Pilot
open CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBGraphForm
open CFSG.SeitzReduction.LinearPilot

noncomputable section

abbrev GL4F4 : Type := Matrix.GeneralLinearGroup (Fin 4) F4
abbrev SL4F4 : Type := Matrix.SpecialLinearGroup (Fin 4) F4

abbrev root01_4 : (0 : Fin 4) ≠ 1 := by decide

@[expose] noncomputable def blockGamma (C : GL4F4) (δ : ℕ) : MulAut SL4F4 :=
  slConjugation 4 F4 C * (slGraphAut 4 F4) ^ δ

private theorem blockFourMat_affine (t : F4) (M : Matrix (Fin 4) (Fin 4) F4) :
    blockFourMat (1 + t • M) = 1 + t • (blockFourMat (1 + M) - 1) := by
  ext i j
  obtain ⟨i', rfl⟩ := e46.surjective i
  obtain ⟨j', rfl⟩ := e46.surjective j
  rw [blockFourMat_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply]
  rw [blockFourMat_apply]
  rcases i' with i' | i' <;> rcases j' with j' | j' <;>
    simp [Matrix.fromBlocks, Matrix.one_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]
  all_goals ring

theorem sigma_eq_refl_of_block_eq
    {Q : Type} [Group Q]
    (psi : SL6F4 →* Q)
    (hpsi_surj : Function.Surjective psi)
    (hpsi_ker : psi.ker ≤ Subgroup.center SL6F4)
    (A : GL6F4)
    (sigma : F4 ≃+* F4)
    (epsilon : ℕ) (hepsilon : epsilon ≤ 1)
    (C : GL4F4)
    (delta : ℕ) (hdelta : delta ≤ 1)
    (h : ∀ g : SL4F4,
      psi ((fieldDetectionBeta A sigma epsilon) (blockFour g)) =
        psi (blockFour ((blockGamma C delta) g))) :
    sigma = RingEquiv.refl F4 := by
  haveI hperf : Group.IsPerfect SL4F4 :=
    CFSG.LinearGroups.special_linear_isPerfect (by omega) (Or.inl (by omega))
  have hcomp : ∀ g : SL4F4,
      psi ((fieldDetectionBeta A sigma epsilon).toMonoidHom.comp blockFour g) =
        psi (blockFour.comp (blockGamma C delta).toMonoidHom g) := by
    intro g
    simpa using h g
  have hlift : (fieldDetectionBeta A sigma epsilon).toMonoidHom.comp blockFour =
      blockFour.comp (blockGamma C delta).toMonoidHom :=
    eq_of_comp_eq_of_ker_le_center hpsi_ker hcomp
  have hlin : ∀ t : F4,
      ((fieldDetectionBeta A sigma epsilon (rootTransvection t) : SL6F4) :
        Matrix (Fin 6) (Fin 6) F4) =
        1 + t • (((fieldDetectionBeta A sigma epsilon (rootTransvection 1) : SL6F4) :
          Matrix (Fin 6) (Fin 6) F4) - 1) := by
    intro t
    have h1 := congrArg (fun f => f (SpecialLinearGroup.transvection root01_4 t)) hlift
    have hleft_at : ∀ s : F4,
        ((fieldDetectionBeta A sigma epsilon).toMonoidHom.comp blockFour)
          (SpecialLinearGroup.transvection root01_4 s) =
          fieldDetectionBeta A sigma epsilon (rootTransvection s) := by
      intro s
      simp only [MonoidHom.comp_apply, rootTransvection]
      rw [blockFour_transvection]
      have ht : SpecialLinearGroup.transvection (c4_ne root01_4) s =
          SpecialLinearGroup.transvection root01 s := by
        apply Subtype.ext
        simp only [SpecialLinearGroup.transvection_coe]
        rfl
      rw [ht]
      rfl
    have hleft := hleft_at t
    rw [hleft] at h1
    simp only [MonoidHom.comp_apply] at h1
    interval_cases delta
    ·
      have hgamma_at : ∀ s : F4,
          (blockGamma C 0) (SpecialLinearGroup.transvection root01_4 s) =
          slConjugation 4 F4 C (SpecialLinearGroup.transvection root01_4 s) := by
        intro s
        simp [blockGamma]
      have hgamma := hgamma_at t
      change (fieldDetectionBeta A sigma epsilon) (rootTransvection t) =
        blockFour ((blockGamma C 0) (SpecialLinearGroup.transvection root01_4 t)) at h1
      rw [hgamma] at h1
      have hM_all : ∀ s : F4,
          ((slConjugation 4 F4 C (SpecialLinearGroup.transvection root01_4 s) : SL4F4) :
            Matrix (Fin 4) (Fin 4) F4) =
            1 + s • ((C : Matrix (Fin 4) (Fin 4) F4) * Matrix.single (0 : Fin 4) 1 1 *
              ((C⁻¹ : GL4F4) : Matrix (Fin 4) (Fin 4) F4)) := by
        intro s
        rw [slConjugation_matrix]
        rw [SpecialLinearGroup.transvection_coe]
        rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel,
          Units.val_one]
        rw [show single (0 : Fin 4) 1 s =
          s • (single (0 : Fin 4) 1 1 : Matrix (Fin 4) (Fin 4) F4) by
            rw [Matrix.smul_single, smul_eq_mul, mul_one]]
        rw [Matrix.mul_smul, Matrix.smul_mul]
      have hM := hM_all t
      have hM1 := hM_all 1
      have h1mat := congrArg (fun g : SL6F4 => ((g : SL6F4) :
        Matrix (Fin 6) (Fin 6) F4)) h1
      rw [coe_blockFour] at h1mat
      rw [hM] at h1mat
      rw [blockFourMat_affine t] at h1mat
      have h1one := congrArg (fun f => f (SpecialLinearGroup.transvection root01_4 1)) hlift
      rw [hleft_at 1] at h1one
      simp only [MonoidHom.comp_apply] at h1one
      change (fieldDetectionBeta A sigma epsilon) (rootTransvection 1) =
        blockFour ((blockGamma C 0) (SpecialLinearGroup.transvection root01_4 1)) at h1one
      rw [hgamma_at 1] at h1one
      have h1one_mat := congrArg (fun g : SL6F4 => ((g : SL6F4) :
        Matrix (Fin 6) (Fin 6) F4)) h1one
      rw [coe_blockFour] at h1one_mat
      rw [hM1] at h1one_mat
      simp only [one_smul] at h1one_mat
      rw [← h1one_mat] at h1mat
      exact h1mat
    ·
      have hgamma_at : ∀ s : F4,
          (blockGamma C 1) (SpecialLinearGroup.transvection root01_4 s) =
          slConjugation 4 F4 C (slGraphAut 4 F4 (SpecialLinearGroup.transvection root01_4 s)) := by
        intro s
        simp [blockGamma]
      have hgamma := hgamma_at t
      change (fieldDetectionBeta A sigma epsilon) (rootTransvection t) =
        blockFour ((blockGamma C 1) (SpecialLinearGroup.transvection root01_4 t)) at h1
      rw [hgamma] at h1
      have hM_all : ∀ s : F4,
          ((slConjugation 4 F4 C (slGraphAut 4 F4 (SpecialLinearGroup.transvection root01_4 s)) :
            SL4F4) : Matrix (Fin 4) (Fin 4) F4) =
            1 + s • ((C : Matrix (Fin 4) (Fin 4) F4) * Matrix.single (1 : Fin 4) 0 1 *
              ((C⁻¹ : GL4F4) : Matrix (Fin 4) (Fin 4) F4)) := by
        intro s
        rw [slConjugation_matrix]
        rw [slGraphAut_matrix]
        have hinv : (SpecialLinearGroup.transvection root01_4 s)⁻¹ =
            SpecialLinearGroup.transvection root01_4 (-s) :=
          SpecialLinearGroup.transvection_inv root01_4 s
        rw [hinv]
        rw [show (-s : F4) = s by rw [CharTwo.neg_eq]]
        rw [SpecialLinearGroup.transvection_coe]
        rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single]
        rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel,
          Units.val_one]
        rw [show single (1 : Fin 4) 0 s =
          s • (single (1 : Fin 4) 0 1 : Matrix (Fin 4) (Fin 4) F4) by
            rw [Matrix.smul_single, smul_eq_mul, mul_one]]
        rw [Matrix.mul_smul, Matrix.smul_mul]
      have hM := hM_all t
      have hM1 := hM_all 1
      have h1mat := congrArg (fun g : SL6F4 => ((g : SL6F4) :
        Matrix (Fin 6) (Fin 6) F4)) h1
      rw [coe_blockFour] at h1mat
      rw [hM] at h1mat
      rw [blockFourMat_affine t] at h1mat
      have h1one := congrArg (fun f => f (SpecialLinearGroup.transvection root01_4 1)) hlift
      rw [hleft_at 1] at h1one
      simp only [MonoidHom.comp_apply] at h1one
      change (fieldDetectionBeta A sigma epsilon) (rootTransvection 1) =
        blockFour ((blockGamma C 1) (SpecialLinearGroup.transvection root01_4 1)) at h1one
      rw [hgamma_at 1] at h1one
      have h1one_mat := congrArg (fun g : SL6F4 => ((g : SL6F4) :
        Matrix (Fin 6) (Fin 6) F4)) h1one
      rw [coe_blockFour] at h1one_mat
      rw [hM1] at h1one_mat
      simp only [one_smul] at h1one_mat
      rw [← h1one_mat] at h1mat
      exact h1mat
  exact sigma_eq_refl_of_root_linear A sigma hepsilon hlin


end

end CFSG.StandardType.N2KFieldCoefficient


public section

namespace CFSG.StandardType

noncomputable section

theorem exists_wholeRootChart_of_normalizer
    {G N : Type} [Group G] [Group N]
    {J H : Subgroup G} (hJH : J ≤ H)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    (eJ : J ≃* Matrix.SpecialLinearGroup (Fin 4) F)
    (psi : N →* G) (hpsi : psi.range = H)
    (Q : Subgroup N)
    (hQ : Q.map psi =
      (rootR F).map (J.subtype.comp eJ.symm.toMonoidHom))
    (n : G) (hn : n ∈ Subgroup.normalizer (J : Set G)) :
    ∃ j : J,
      ((MulAut.conj (n * (j : G))).toMonoidHom.comp psi).range =
        H.map (MulAut.conj n).toMonoidHom ∧
      ((MulAut.conj (n * (j : G))).toMonoidHom.comp psi).ker = psi.ker ∧
      Q.map ((MulAut.conj (n * (j : G))).toMonoidHom.comp psi) =
        (rootR F).map (J.subtype.comp eJ.symm.toMonoidHom) := by
  classical
  let cJ : MulAut ↥J := (J.normalizerMonoidHom ⟨n, hn⟩)⁻¹
  let α : MulAut (Matrix.SpecialLinearGroup (Fin 4) F) :=
    (eJ.symm.trans cJ).trans eJ
  obtain ⟨g, hg⟩ := rootR_marking_invariant F hF α
  let j : ↥J := eJ.symm g
  have hα_symm : eJ.symm.toMonoidHom.comp α.toMonoidHom =
      cJ.toMonoidHom.comp eJ.symm.toMonoidHom := by
    ext x
    simp [α, cJ]
  have hrootJ :
      (rootR F).map (cJ.toMonoidHom.comp eJ.symm.toMonoidHom) =
        (rootR F).map (eJ.symm.toMonoidHom.comp (MulAut.conj g).toMonoidHom) := by
    have h := congrArg
      (fun S : Subgroup (Matrix.SpecialLinearGroup (Fin 4) F) =>
        S.map eJ.symm.toMonoidHom) hg
    rw [Subgroup.map_map] at h
    rw [hα_symm] at h
    simp only [Subgroup.map_map] at h
    exact h
  have hrootG := congrArg (fun S : Subgroup ↥J => S.map J.subtype) hrootJ
  rw [Subgroup.map_map] at hrootG
  simp only [Subgroup.map_map] at hrootG
  have hnorm_apply (y : ↥J) :
      ((J.normalizerMonoidHom ⟨n, hn⟩ y : ↥J) : G) =
        n * (y : G) * n⁻¹ := by
    rfl
  have hcJ_apply (x : ↥J) : (cJ x : G) = n⁻¹ * (x : G) * n := by
    have hc : J.normalizerMonoidHom ⟨n, hn⟩ (cJ x) = x := by
      exact MulEquiv.apply_symm_apply (J.normalizerMonoidHom ⟨n, hn⟩) x
    have h := hnorm_apply (cJ x)
    rw [hc] at h
    calc
      (cJ x : G) = n⁻¹ * (n * (cJ x : G) * n⁻¹) * n := by group
      _ = n⁻¹ * (x : G) * n := by rw [h]
  have hcomp_n :
      (MulAut.conj (n⁻¹)).toMonoidHom.comp
          (J.subtype.comp eJ.symm.toMonoidHom) =
        J.subtype.comp (cJ.toMonoidHom.comp eJ.symm.toMonoidHom) := by
    ext x
    simpa using (hcJ_apply (eJ.symm x)).symm
  have hcomp_j :
      (MulAut.conj (j : G)).toMonoidHom.comp
          (J.subtype.comp eJ.symm.toMonoidHom) =
        J.subtype.comp (eJ.symm.toMonoidHom.comp
          (MulAut.conj g).toMonoidHom) := by
    ext x
    simp [j, MulAut.conj_apply]
  have hR_conj_n :
      ((rootR F).map (J.subtype.comp eJ.symm.toMonoidHom)).map
          (MulAut.conj (n⁻¹)).toMonoidHom =
        (rootR F).map (J.subtype.comp
          (cJ.toMonoidHom.comp eJ.symm.toMonoidHom)) := by
    rw [Subgroup.map_map, hcomp_n]
  have hR_conj_j :
      ((rootR F).map (J.subtype.comp eJ.symm.toMonoidHom)).map
          (MulAut.conj (j : G)).toMonoidHom =
        (rootR F).map (J.subtype.comp
          (eJ.symm.toMonoidHom.comp (MulAut.conj g).toMonoidHom)) := by
    rw [Subgroup.map_map, hcomp_j]
  have hRJ :
      ((rootR F).map (J.subtype.comp eJ.symm.toMonoidHom)).map
          (MulAut.conj (n⁻¹)).toMonoidHom =
        ((rootR F).map (J.subtype.comp eJ.symm.toMonoidHom)).map
          (MulAut.conj (j : G)).toMonoidHom := by
    rw [hR_conj_n, hR_conj_j]
    exact hrootG
  have hcomp_fix :
      (MulAut.conj n).toMonoidHom.comp
          (MulAut.conj (j : G)).toMonoidHom =
        (MulAut.conj (n * (j : G))).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hRfix :
      ((rootR F).map (J.subtype.comp eJ.symm.toMonoidHom)).map
          (MulAut.conj (n * (j : G))).toMonoidHom =
        (rootR F).map (J.subtype.comp eJ.symm.toMonoidHom) := by
    have hconj_comp :
        (MulAut.conj n).toMonoidHom.comp
            (MulAut.conj (n⁻¹)).toMonoidHom = MonoidHom.id G := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    have h1 :
        (((rootR F).map (J.subtype.comp eJ.symm.toMonoidHom)).map
            (MulAut.conj (n⁻¹)).toMonoidHom).map
          (MulAut.conj n).toMonoidHom =
        (rootR F).map (J.subtype.comp eJ.symm.toMonoidHom) := by
      rw [Subgroup.map_map, hconj_comp, Subgroup.map_id]
    rw [hRJ] at h1
    rw [Subgroup.map_map] at h1
    rw [hcomp_fix] at h1
    exact h1
  have hHj : H.map (MulAut.conj (j : G)).toMonoidHom = H := by
    have hjH : (j : G) ∈ H := hJH j.2
    have hHnorm : H ≤ Subgroup.normalizer (H : Set G) := by
      rw [Subgroup.le_set_normalizer_iff]
      intro x hx y hy
      exact H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)
    exact (Subgroup.mem_normalizer_iff_map_conj_eq).mp (hHnorm hjH)
  have hHconj :
      H.map (MulAut.conj (n * (j : G))).toMonoidHom =
        H.map (MulAut.conj n).toMonoidHom := by
    calc
      H.map (MulAut.conj (n * (j : G))).toMonoidHom
          = H.map ((MulAut.conj n).toMonoidHom.comp
              (MulAut.conj (j : G)).toMonoidHom) := by
              congr 1
              ext x
              simp [MulAut.conj_apply, mul_assoc]
      _ = (H.map (MulAut.conj (j : G)).toMonoidHom).map
            (MulAut.conj n).toMonoidHom := by
              rw [Subgroup.map_map]
      _ = H.map (MulAut.conj n).toMonoidHom := by rw [hHj]
  have hker :
      ((MulAut.conj (n * (j : G))).toMonoidHom.comp psi).ker = psi.ker :=
    MonoidHom.ker_comp_of_injective psi
      (MulAut.conj (n * (j : G))).toMonoidHom
      (MulAut.conj (n * (j : G))).injective
  have hQ' :
      Q.map ((MulAut.conj (n * (j : G))).toMonoidHom.comp psi) =
        (rootR F).map (J.subtype.comp eJ.symm.toMonoidHom) := by
    rw [← Subgroup.map_map, hQ, hRfix]
  have hrange :
      ((MulAut.conj (n * (j : G))).toMonoidHom.comp psi).range =
        H.map (MulAut.conj n).toMonoidHom := by
    rw [MonoidHom.range_comp, hpsi, hHconj]
  exact ⟨j, hrange, hker, hQ'⟩


end

end CFSG.StandardType
