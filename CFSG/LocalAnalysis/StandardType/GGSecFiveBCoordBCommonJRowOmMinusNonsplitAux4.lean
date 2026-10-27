module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowOmMinusNonsplitAux1
import CFSG.LocalAnalysis.StandardType.GGTBJOmModelMap
import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestOddLayer
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourPlusFrame
import CFSG.GroupTheory.IsComponentOfMap
import CFSG.RankThree.PartOne.KC.OrthogonalBlockDet
import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
import CFSG.HardMathSupport.Dickson.Bal207.OrthD4Semilin
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallL4Klein
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.ClassicalGroups.SpecialLinear.ComponentCartanRankDivisible
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJCoord
import CFSG.LocalAnalysis.StandardType.GGTBJOmComp
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenFrame
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenCoherent
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenTorus
import CFSG.LocalAnalysis.StandardType.GGRealKGOmegaFrame
import CFSG.LocalAnalysis.StandardType.GGHdRo7DFrameOmega
import CFSG.ClassicalGroups.Orthogonal.MinusPlaneFrames
import CFSG.ClassicalInvolution.RouteD.TWYType
import CFSG.RankThree.PartOne.S11d.OrthModels
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Label
import CFSG.LocalAnalysis.StandardType.GGTCJLabel
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOKlein
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOrthOmega
import CFSG.CGT.PushingUpLit.CGT6.SixFourCoreSL
import CFSG.CGT.PushingUpLit.Glue.NineContentGlue
import CFSG.CGT.PushingUpLit.NineContent
import CFSG.CGT.Timmesfeld75.Derivations
import CFSG.CGT.Timmesfeld75.Targets
import CFSG.ClassicalGroups.SpecialLinear.DiagonalTorusRank
import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.RankCube
import CFSG.HardMathSupport.Dickson.Bal207.OrthD4Loc
import CFSG.HardMathSupport.Dickson.Bal207.Restate
import CFSG.HardMathSupport.Solomon.Coordinator.InndiagLink
import CFSG.LieType.SpecialLinear.BinaryDescent.Basic
import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Bounded
import CFSG.LocalAnalysis.SectionRank.QTK.EvenOrth
import CFSG.LocalAnalysis.SectionRank.QTK.Exc
import CFSG.LocalAnalysis.SectionRank.QTK.OddOrth
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule
import CFSG.LocalAnalysis.UniquenessCase.UC22S20b
import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
import CFSG.RankThree.OddKernel.CompleteRankComparison
import CFSG.RankThree.PartOne.KF.ClsPSL
import CFSG.RankThree.PartOne.KF.SymCtxMatrix
import CFSG.RankThree.PartOne.KF.ToralQuot
import CFSG.RankThree.PartOne.S11c.Sec66PSL

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.GroupTheory.WeirSylow
open Polynomial
open CFSG.RankThree.PartOne.KCOrthogonal

namespace CommonJOmMinusNonsplit

open CFSG.RankThree.Classical2 (orthDerived)

private theorem signedNormalizer_frameTorus_rMinus
    {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} {p k : ℕ} {b c : K}
    {U : Fin k → Submodule K V} {ef : Fin k → ↥(orthDerived Q)}
    {E : Subgroup ↥(orthDerived Q)} {u : Fin k → V} {cc t : K}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1)
    (hC : CFSG.StandardType.OmNsRootGen.IsCoherentFrame Q p U ef E u cc t) (hk : 0 < k)
    (hsc : ∀ g : ↥(orthDerived Q), (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    {τ : (Fin k → Multiplicative (ZMod p)) →* ↥(orthDerived Q)}
    (hτinj : Function.Injective τ) (hτE : τ.range = E)
    (hτ : ∀ i, τ (Pi.mulSingle i (Multiplicative.ofAdd 1)) = ef i)
    (e : OrthRest.RMinus K k b c ≃* ↥(orthDerived Q)) :
    GGOmMinusNonsplitSignedNormalizer (e.symm.toMonoidHom.comp τ) := by
  intro g hg
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun x : V ≃ₗ[K] V => (x : V → V))
    fun x y hxy => LinearEquiv.ext (congrFun hxy)
  haveI : Finite ↥E := Subtype.finite
  have hgE : ∀ x ∈ E, e g * x * (e g)⁻¹ ∈ E := by
    intro x hx
    rw [← hτE] at hx ⊢
    obtain ⟨a, rfl⟩ := hx
    have hga : e.symm (τ a) ∈ (e.symm.toMonoidHom.comp τ).range := ⟨a, rfl⟩
    have h1 := hg (e.symm (τ a)) hga
    have h2 : e (g * e.symm (τ a) * g⁻¹) = e g * τ a * (e g)⁻¹ := by
      rw [map_mul, map_mul, map_inv, e.apply_symm_apply]
    obtain ⟨f, hf⟩ := h1
    refine ⟨f, ?_⟩
    have hf' : e (e.symm (τ f)) = e (g * e.symm (τ a) * g⁻¹) := by
      simpa using congrArg e hf
    rw [← e.apply_symm_apply (τ f), hf', h2]
  obtain ⟨w, hgw⟩ := CFSG.StandardType.HdRo7D.hdRo7DFrOAux_exists_indAut hgE hτinj hτE
  have hws : SpCoord.IsSignedPerm ⇑w :=
    RealKGOmega.isSignedPerm_of_normalizer hQ hp hp2 hpq hT hC hk hsc hτinj hτE hτ hgw
  refine ⟨w, hws, ?_⟩
  intro f
  apply e.injective
  simpa [MonoidHom.comp_apply] using hgw f

private theorem ggHasLabel_fixedBlock {K : Type} [Field K] [Finite K] [CharP K 2]
    {m f : ℕ} (hK : Nat.card K = 2 ^ f) (hm : 3 ≤ m) (hf1 : 1 ≤ f)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {R : QuadraticForm K V} (eiso : R.IsometryEquiv (CFSG.LieType.Universal.Spin.quadPlus m K))
    {J : Type} [Group J] (hJq : CFSG.IsQuasisimple J)
    (eQ : (J ⧸ Subgroup.center J) ≃* ↥(orthDerived R)) :
    GGHasLabel ⟨.D, m, f⟩ (J ⧸ Subgroup.center J) := by
  by_cases hm3 : m = 3
  · subst m
    let eOrth : ↥(orthDerived (CFSG.LieType.Universal.Spin.quadPlus 3 K)) ≃*
        ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus 3 K)) :=
      (CFSG.RankThree.PartOne.statedOmegaOrthEquiv
        (CFSG.LieType.Universal.Spin.coe_quadPlus (n := 3) (K := K))).symm
    let eOmega : (J ⧸ Subgroup.center J) ≃*
        ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus 3 K)) :=
      eQ.trans ((CFSG.RankThree.PartOne.orthDerivedEquiv eiso).trans eOrth)
    let eSL : (J ⧸ Subgroup.center J) ≃* Matrix.SpecialLinearGroup (Fin 4) K :=
      eOmega.trans
        (CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.kleinOmegaEquiv K).symm
    have hcenterSL : Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) K) = ⊥ :=
      CFSG.ClassicalGroups.SpecialLinear.center_specialLinear_four_eq_bot K
    let ePSL : (J ⧸ Subgroup.center J) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 4) K :=
      eSL.trans ((QuotientGroup.quotientMulEquivOfEq hcenterSL).trans
        QuotientGroup.quotientBot).symm
    have hmodel3 : CFSG.Open.StatedClassicalModel (J ⧸ Subgroup.center J) .PSL 4 2 f := by
      refine ⟨⟨Nat.prime_two, hf1, by norm_num, by simp, by simp⟩, K, inferInstance,
        inferInstance, hK, ?_⟩
      exact ⟨ePSL.trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 4 K)⟩
    have hHas3 := CFSG.LocalAnalysis.GLTheoremA.Y10F.hasLabel_of_statedClassicalModel_PSL4_D
      hJq hmodel3
    exact CFSG.StandardType.TCJ.tcj_ggHasLabel_of_hasLabel hHas3
  · have hm4 : 4 ≤ m := by omega
    have hmodel : CFSG.Blueprint.LieModel (J ⧸ Subgroup.center J) .POmegaPlus m 2 f :=
      CFSG.RankThree.PartOne.lieModel_of_orthDerived_plus hm4 hf1 hK eiso eQ
    have hSC := hmodel.statedClassicalModel_of_ne_zero (by omega)
    have hHas := CFSG.LocalAnalysis.GLTheoremA.Y10F.hasLabel_of_statedClassicalModel_POmegaPlus
      hJq hSC
    exact CFSG.StandardType.TCJ.tcj_ggHasLabel_of_hasLabel hHas

private theorem ggHasLabel_of_plus_fixedBlock {K : Type} [Field K] [Finite K] [CharP K 2]
    {p m f : ℕ} (hK : Nat.card K = 2 ^ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq' : p ∣ Nat.card K + 1) (hm : 3 ≤ m) (hf1 : 1 ≤ f)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hVminus : ¬ IsPlusType Q)
    {U : Fin m → Submodule K V} {ef' : Fin m → ↥(orthDerived Q)}
    {E : Subgroup ↥(orthDerived Q)} {u : Fin m → V} {cc t : K}
    (hC : CFSG.StandardType.OmNsRootGen.IsCoherentFrame Q p U ef' E u cc t)
    {x : ↥(orthDerived Q)}
    (hxO : CFSG.RankThree.PartOne.KCOrthogonal.OddOrderIsometry Q p (x : V ≃ₗ[K] V))
    (i : Fin m) (z : ZMod p) (hz : z ≠ 0) (hx_eq : x = (ef' i) ^ z.val)
    (hx_fix : CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (x : V ≃ₗ[K] V) =
      CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.polarPerp Q (U i))
    (hfixdim : Module.finrank K (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace
      (x : V ≃ₗ[K] V)) = 2 * m)
    {b c : K} (e : OrthRest.RMinus K m b c ≃* ↥(orthDerived Q))
    {J : Subgroup (OrthRest.RMinus K m b c)}
    (hJ' : IsComponentOf (J.map e.toMonoidHom)
      (Subgroup.centralizer ({x} : Set ↥(orthDerived Q))))
    (hJq : CFSG.IsQuasisimple ↥J) :
    GGHasLabel ⟨.D, m, f⟩ (↥J ⧸ Subgroup.center ↥J) := by
  let J' : Subgroup ↥(orthDerived Q) := J.map e.toMonoidHom
  have hx_eq' : (x : V ≃ₗ[K] V) = ((ef' i : V ≃ₗ[K] V) ^ z.val) := by
    rw [hx_eq]
    simp only [Subgroup.coe_pow]
  have hXnot : ¬ IsPlusType (Q.comp (U i).subtype) := hC.toIsPlaneFrame.not_isPlusType i
  have hc : IsCompl (U i) (CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.polarPerp Q (U i)) :=
    CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.isCompl_polarPerp
      (hC.toIsPlaneFrame.nondeg i)
  have hXnd : CFSG.ClassicalGroups.Orthogonal.PolarNondegOn Q (U i) := by
    intro u hu hu0
    have hu' : (⟨u, hu⟩ : ↥(U i)) = 0 :=
      (hC.toIsPlaneFrame.nondeg i).1 ⟨u, hu⟩ fun v => by
        simpa [CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.polar_comp_subtype_cent,
          QuadraticMap.polarBilin_apply_apply] using hu0 v v.2
    exact congrArg Subtype.val hu'
  have hWnd : CFSG.ClassicalGroups.Orthogonal.PolarNondegOn Q
      (CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.polarPerp Q (U i)) := by
    intro u hu hu0
    refine CFSG.ClassicalGroups.Orthogonal.eq_zero_of_polar_eq_zero hQ fun v => ?_
    have hv : v ∈ U i ⊔ CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.polarPerp Q (U i) := by
      rw [hc.sup_eq_top]; trivial
    obtain ⟨a, ha, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
    rw [QuadraticMap.polar_add_right, QuadraticMap.polar_comm (⇑Q) u a,
      CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.mem_polarPerp_iff.1 hu a ha, hu0 w hw, add_zero]
  have hplus : IsPlusType (Q.comp
      (CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.polarPerp Q (U i)).subtype) := by
    have hiff := CFSG.ClassicalInvolution.RouteD.TWY.isPlusType_iff_of_isCompl hc
      (fun a ha b hb => CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.mem_polarPerp_iff.1 hb a ha)
      hXnd hWnd (a := 1) (b := m) (by omega) (by omega)
      (hXd := by rw [hC.toIsPlaneFrame.finrank_eq i])
      (hWd := by rw [← hx_fix]; exact hfixdim)
    by_contra hWnot
    apply hVminus
    rw [hiff]
    exact ⟨fun hX => absurd hX hXnot, fun hW => absurd hW hWnot⟩
  have hplusFix : IsPlusType (Q.comp
      (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace
        (x : V ≃ₗ[K] V)).subtype) := by
    rw [show CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace
        (x : V ≃ₗ[K] V) =
        CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.polarPerp Q (U i) from hx_fix]
    exact hplus
  have hcomm_le : CFSG.RankThree.PartOne.LIT.commSpace
      (x : V ≃ₗ[K] V) ≤ U i := by
    let g : V ≃ₗ[K] V :=
      ((ef' i : ↥(orthDerived Q)) : V ≃ₗ[K]
        V)
    have hxg : (x : V ≃ₗ[K]
        V) = g ^ z.val := by
      simpa [g] using hx_eq'
    intro v hv
    rw [CFSG.RankThree.PartOne.LIT.mem_commSpace] at hv
    obtain ⟨w, rfl⟩ := hv
    have hspan : w ∈ U i ⊔ CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.polarPerp Q (U i) := by
      rw [hc.sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hspan
    have hxmem : (x : V ≃ₗ[K]
        V) ∈ Subgroup.zpowers g := by
      rw [hxg]
      exact Subgroup.mem_zpowers_iff.mpr ⟨z.val, rfl⟩
    have hfix_b : (x : V ≃ₗ[K]
        V) b = b := by
      have hstab : g ∈ MulAction.stabilizer
          (V ≃ₗ[K] V) b :=
        (MulAction.mem_stabilizer_iff).2 (by
          simpa [g] using hC.toIsPlaneFrame.apply_of_perp i b hb)
      have hb' := (Subgroup.zpowers_le (H := MulAction.stabilizer
        (V ≃ₗ[K] V) b)).2 hstab hxmem
      exact (MulAction.mem_stabilizer_iff).1 hb'
    have hpow_mem : ∀ n : ℕ, (g ^ n) a ∈ U i := by
      intro n
      induction n with
      | zero => simpa using ha
      | succ n ih =>
          rw [pow_succ', LinearEquiv.mul_apply]
          exact hC.toIsPlaneFrame.maps_to i _ ih
    have hx_a : (x : V ≃ₗ[K]
        V) a ∈ U i := by
      rw [hxg]
      exact hpow_mem z.val
    have hx_ab : (x : V ≃ₗ[K]
        V) (a + b) =
        (x : V ≃ₗ[K]
        V) a + b := by
      rw [map_add, hfix_b]
    rw [hx_ab]
    have hsub := Submodule.sub_mem (U i) hx_a ha
    have hEq : (x : V ≃ₗ[K] V) a + b -
        (a + b) = (x : V ≃ₗ[K] V) a - a := by
      abel
    rwa [hEq]
  have hmult_one : ∀ h : K[X], h ∈ CFSG.RankThree.PartOne.KCPrimary.primaryFactors
      (x : V ≃ₗ[K] V).toLinearMap →
      h ≠ Polynomial.X - 1 →
      CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity
        (x : V ≃ₗ[K] V).toLinearMap h = 1 := by
    intro h hh hhX
    have hle := le_trans
      (CFSG.StandardType.OrthRestOdd.primaryComponent_le_commSpace hxO hh hhX) hcomm_le
    haveI : Fact (Irreducible h) :=
      ⟨CFSG.RankThree.PartOne.KCPrimary.irreducible_of_mem_primaryFactors hh⟩
    have hdeg := CFSG.RankThree.PartOne.K159.natDegree_eq_two_of_dvd_card_add_one
      hxO hp hp2 hpq' hh hhX
    have hsq : Squarefree (minpoly K
        (x : V ≃ₗ[K] V).toLinearMap) :=
      hxO.squarefree_minpoly
    have hne : CFSG.RankThree.PartOne.KCPrimary.primaryComponent
        (x : V ≃ₗ[K] V).toLinearMap h ≠ ⊥ :=
      CFSG.RankThree.PartOne.KCPrimary.primaryComponent_ne_bot hsq hh
    haveI : Nontrivial (CFSG.RankThree.PartOne.KCPrimary.primaryComponent
        (x : V ≃ₗ[K] V).toLinearMap h) :=
      Submodule.nontrivial_iff_ne_bot.mpr hne
    have hpos : 0 < Module.finrank K (CFSG.RankThree.PartOne.KCPrimary.primaryComponent
        (x : V ≃ₗ[K] V).toLinearMap h) :=
      Module.finrank_pos
    have hfin := CFSG.RankThree.PartOne.KCPrimary.finrank_primaryComponent
      (x := (x : V ≃ₗ[K] V).toLinearMap)
      (a := h)
    rw [hdeg] at hfin
    have hle2 : Module.finrank K (CFSG.RankThree.PartOne.KCPrimary.primaryComponent
        (x : V ≃ₗ[K] V).toLinearMap h) ≤ 2 := by
      simpa [hC.toIsPlaneFrame.finrank_eq i] using Submodule.finrank_mono hle
    change Module.finrank (AdjoinRoot h) (CFSG.RankThree.PartOne.KCPrimary.primaryComponent
      (x : V ≃ₗ[K] V).toLinearMap h) = 1
    omega
  have hRnd : (QuadraticMap.polarBilin (Q.comp
      (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace
        (x : V ≃ₗ[K] V)).subtype)).Nondegenerate :=
    hxO.polarBilin_fixed_nondegenerate
  have hdimfix : Module.finrank K (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace
      (x : V ≃ₗ[K] V)) = 2 * m := hfixdim
  obtain ⟨eiso⟩ | ⟨bb, cc, hirr', eiso⟩ :=
    CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus
      (Q.comp (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace
        (x : V ≃ₗ[K] V)).subtype) hRnd
      (n := m) (by omega) hdimfix
  · obtain ⟨eiso⟩ := eiso
    obtain ⟨h, hh, hhX, hJspec⟩ | ⟨F, hFq, hFle, hFnorm, hFdim, hJfix⟩ :=
      OrthTorus.component_cases hQ hp hp2 hxO hJ'
    · exfalso
      haveI : Fact (Irreducible h) :=
        ⟨CFSG.RankThree.PartOne.KCPrimary.irreducible_of_mem_primaryFactors hh⟩
      have hbot : CFSG.RankThree.PartOne.KCOrthogonal.specialBlock Q (x : V ≃ₗ[K]
          V) h = ⊥ :=
        hxO.specialBlock_eq_bot_of_finrank_eq_one hh (hmult_one h hh hhX)
      have hJbot : J.map e.toMonoidHom = ⊥ := by
        rw [hJspec, hbot]
        simp
      rw [hJbot] at hJ'
      haveI : Subsingleton ↥(⊥ : Subgroup ↥(orthDerived Q)) := by
        constructor
        intro a b
        exact Subtype.ext ((Subgroup.mem_bot.mp a.2).trans (Subgroup.mem_bot.mp b.2).symm)
      have hsubq : Subsingleton (↥(⊥ : Subgroup ↥(orthDerived Q)) ⧸
          Subgroup.center ↥(⊥ : Subgroup ↥(orthDerived Q))) := by
        refine ⟨fun a b => ?_⟩
        obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ a
        obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective _ b
        congr 1
        exact Subsingleton.elim a b

      obtain ⟨a, b, hab⟩ := hJ'.2.2.2.toNontrivial.exists_pair_ne
      exact hab (Subsingleton.elim a b)
    · have hFfull : F = CFSG.RankThree.PartOne.KCOrthogonal.supportedFixedDerived Q (x : V ≃ₗ[K]
          V) := by
        rcases hFdim with h4 | heq
        · omega
        · exact heq
      have hJeq : J.map e.toMonoidHom =
          (CFSG.RankThree.PartOne.KCOrthogonal.supportedFixedDerived Q (x : V ≃ₗ[K]
          V)).subgroupOf (orthDerived Q) := by
        rw [hJfix, hFfull]
      let R : QuadraticForm K ↥(CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace
          (x : V ≃ₗ[K] V)) :=
        Q.comp (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace
          (x : V ≃ₗ[K] V)).subtype
      let eJ0 : ↥J ≃* ↥J' := Subgroup.equivMapOfInjective J e.toMonoidHom e.injective
      let eJ' : ↥J' ≃* ↥(CFSG.RankThree.PartOne.KCOrthogonal.supportedFixedDerived Q
          (x : V ≃ₗ[K] V)) := by
        change ↥(J.map e.toMonoidHom) ≃*
          ↥(CFSG.RankThree.PartOne.KCOrthogonal.supportedFixedDerived Q (x : V ≃ₗ[K] V))
        rw [hJeq]
        exact Subgroup.subgroupOfEquivOfLe hxO.supportedFixedDerived_le_orthDerived
      let eFix : ↥(CFSG.RankThree.PartOne.KCOrthogonal.supportedFixedDerived Q
          (x : V ≃ₗ[K] V)) ≃* ↥(orthDerived R) :=
        CFSG.HardMathSupport.Dickson.Bal207.OrthFix.fixRestr hxO
      let eFull : ↥J ≃* ↥(orthDerived R) := eJ0.trans (eJ'.trans eFix)
      haveI : Nontrivial ↥(CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace
          (x : V ≃ₗ[K] V)) :=
        Module.nontrivial_of_finrank_pos (by rw [hfixdim]; omega)
      have hcenterR : Subgroup.center ↥(orthDerived R) = ⊥ := by
        refine CFSG.RankThree.PartOne.center_orthDerived_eq_bot hRnd ?_
        obtain ⟨T, hT, hQ0⟩ :=
          CFSG.ComponentClassification.RankTwoClassical.exists_totallySingular_quadPlus
            (n := m) (by omega) K
        refine ⟨T.map eiso.symm.toLinearEquiv.toLinearMap, ?_, ?_⟩
        · rw [LinearEquiv.finrank_map_eq]
          exact hT
        · rintro v hv
          obtain ⟨w, hw, rfl⟩ := hv
          exact (eiso.symm.map_app w).trans (hQ0 w hw)
      have hcenterJ : Subgroup.center ↥J = ⊥ := by
        rw [eq_bot_iff]
        intro z hz
        have hz' : eFull z ∈ Subgroup.center ↥(orthDerived R) := by
          rw [← Subgroup.map_center_eq eFull]
          exact Subgroup.mem_map_of_mem _ hz
        rw [hcenterR] at hz'
        exact Subgroup.mem_bot.mpr (eFull.injective (by simpa using Subgroup.mem_bot.mp hz'))
      let eQ : (↥J ⧸ Subgroup.center ↥J) ≃* ↥(orthDerived R) :=
        (QuotientGroup.quotientMulEquivOfEq hcenterJ).trans
          (QuotientGroup.quotientBot.trans eFull)
      exact ggHasLabel_fixedBlock (K := K) (m := m) (f := f) hK hm hf1
        (V := ↥(CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace
          (x : V ≃ₗ[K] V)))
        (R := R) eiso (J := ↥J) hJq eQ
  · exfalso
    obtain ⟨eiso⟩ := eiso
    exact (CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus (n := m) (by omega) hirr')
      ((CFSG.GroupTheory.WeirSylow.isPlusType_congr eiso).mp hplusFix)

private theorem exists_coherentFrame_sparse {K : Type} [Field K] [Finite K] [CharP K 2]
    {p m f : ℕ} (hK : Nat.card K = 2 ^ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq' : p ∣ Nat.card K + 1) (hm : 3 ≤ m) (hmo : Odd m) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {τ : (Fin m → Multiplicative (ZMod p)) →* OrthRest.RMinus K m b c}
    (hτ : Function.Injective τ) (hsign : GGOmMinusNonsplitSignedNormalizer τ)
    (hsgn : ∀ i : Fin m, ∃ w : OrthRest.RMinus K m b c,
      ∀ f, w * τ f * w⁻¹ = τ (SpCoord.sgnAut i f))
    (hperm : ∀ σ : Equiv.Perm (Fin m), ∃ w : OrthRest.RMinus K m b c,
      ∀ f, w * τ f * w⁻¹ = τ (SpCoord.permAut σ f))
    {g : Fin m → Multiplicative (ZMod p)} (hS : GGCoordSparse g) (hg : g ≠ 1)
    {Q : QuadraticForm K (LargeEvenMinusIdx m → K)}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (e : OrthRest.RMinus K m b c ≃* ↥(orthDerived Q))
    {E : Subgroup ↥(orthDerived Q)} (hE_eq : E = τ.range.map e.toMonoidHom)
    (hE_ea : IsElemAbelian p E) (hE_card : Nat.card E = p ^ m)
    (hscE : ∀ g : ↥(orthDerived Q), (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E)
    (hT : ∃ T : Submodule K (LargeEvenMinusIdx m → K),
      Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    (hdim : Module.finrank K (LargeEvenMinusIdx m → K) = 2 * (m + 1)) :
    ∃ (U : Fin m → Submodule K (LargeEvenMinusIdx m → K))
      (ef' : Fin m → ↥(orthDerived Q)) (u : Fin m → LargeEvenMinusIdx m → K)
      (cc t : K), CFSG.StandardType.OmNsRootGen.IsCoherentFrame Q p U ef' E u cc t ∧
      ∃ (i : Fin m) (z : ZMod p), z ≠ 0 ∧ e (τ g) = (ef' i) ^ z.val := by
  let x : ↥(orthDerived Q) := e (τ g)
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨k, U, ef, hF, hcase⟩ :=
    CFSG.StandardType.OmNsRootGen.exists_planeFrame_of_selfCentralizing hQ hp hp2 hpq'
      (ℓ := m + 1) hdim (by omega) (E := E) hE_ea hscE
  obtain ⟨τf0, hτf0inj, hτf0range, -, -⟩ :=
    CFSG.StandardType.OmNsRootGen.exists_frameTorus hF hp
  have hk_eq_m : k = m := by
    have h1 : Nat.card (Fin k → Multiplicative (ZMod p)) = Nat.card E := by
      rw [← hτf0range]
      exact Nat.card_congr (MonoidHom.ofInjective hτf0inj).toEquiv
    have h1' : Nat.card (Fin k → Multiplicative (ZMod p)) = p ^ m := by
      rw [h1, hE_card]
    have h2 : Nat.card (Fin k → Multiplicative (ZMod p)) = p ^ k := by
      rw [Nat.card_fun, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, Nat.card_fin]
    exact Nat.pow_right_injective hp.two_le (h2.symm.trans h1')
  subst k
  rcases hcase with ⟨h1, -⟩ | ⟨h1, v₀, v₁, hv₀, hv₁, hQv₀, hQv₁, hvv⟩
  · omega
  obtain ⟨ef', u, cc, t, hC, -⟩ :=
    CFSG.StandardType.OmNsRootGen.exists_coherentFrame hF hp hp2 hpq' (by omega)
  obtain ⟨τf, hτfinj, hτfrange, hτfgen, -⟩ :=
    CFSG.StandardType.OmNsRootGen.exists_frameTorus hC.toIsPlaneFrame hp
  have hsign₀ : GGOmMinusNonsplitSignedNormalizer (e.symm.toMonoidHom.comp τf) :=
    signedNormalizer_frameTorus_rMinus hQ hp hp2 hpq' hC (by omega) hscE hT
      hτfinj hτfrange hτfgen e
  let τ₀ : (Fin m → Multiplicative (ZMod p)) →* OrthRest.RMinus K m b c :=
    e.symm.toMonoidHom.comp τf
  have hτ₀inj : Function.Injective τ₀ := by
    exact e.symm.injective.comp hτfinj
  have hrange : τ.range = τ₀.range := by
    ext y
    constructor
    · intro hy
      have hey : e y ∈ E := by
        rw [hE_eq]
        exact Subgroup.mem_map_of_mem e.toMonoidHom hy
      rw [← hτfrange] at hey
      obtain ⟨a, ha⟩ := hey
      refine ⟨a, ?_⟩
      apply e.injective
      change e (e.symm (τf a)) = e y
      rw [e.apply_symm_apply, ha]
    · intro hy
      obtain ⟨a, ha⟩ := hy
      have hey : e y ∈ E := by
        rw [← hτfrange]
        refine ⟨a, ?_⟩
        rw [← ha]
        simp [τ₀]
      rw [hE_eq] at hey
      obtain ⟨x, hx, hxy⟩ := hey
      exact (e.injective hxy) ▸ hx
  obtain ⟨φ, hφ, hφnorm⟩ :=
    ggCommonJRowOmMinusNonsplit_compareTorus hτ hτ₀inj hrange hsgn hperm hsign₀
  have hf_sparse : GGCoordSparse (φ g) :=
    ((CommonJ.ggCoord_iff_of_normalizes hp hp2 hm hφnorm g).2).mpr hS
  have hf_ne : φ g ≠ 1 := by
    simpa using φ.injective.ne hg
  obtain ⟨i, hi⟩ := hf_sparse
  have hfi : φ g i ≠ 1 := by
    intro h1
    apply hf_ne
    funext j
    by_cases hji : j = i
    · subst hji; simpa using h1
    · simpa using hi j hji
  let z : ZMod p := Multiplicative.toAdd (φ g i)
  have hz : z ≠ 0 := by
    intro h0
    apply hfi
    rw [show φ g i = Multiplicative.ofAdd z from (ofAdd_toAdd _).symm, h0, ofAdd_zero]
  have hf_eq : φ g = Pi.mulSingle i (Multiplicative.ofAdd z) := by
    funext j
    by_cases hji : j = i
    · subst hji; simp [z]
    · rw [hi j hji, Pi.mulSingle_eq_of_ne hji]
  have hx_eq : x = (ef' i) ^ z.val := by
    calc x = e (τ g) := rfl
      _ = e (τ₀ (φ g)) := by rw [hφ g]
      _ = τf (φ g) := by
        change e (e.symm (τf (φ g))) = τf (φ g)
        exact e.apply_symm_apply _
      _ = τf (Pi.mulSingle i (Multiplicative.ofAdd z)) := by rw [hf_eq]
      _ = (τf (Pi.mulSingle i (Multiplicative.ofAdd 1))) ^ z.val := by
        rw [SpCoord.mulSingle_ofAdd_eq_pow, map_pow]
      _ = (ef' i) ^ z.val := by rw [hτfgen i]
  exact ⟨U, ef', u, cc, t, hC, i, z, hz, by simpa [x] using hx_eq⟩


private theorem fixedSpace_facts {K : Type} [Field K] [Finite K] [CharP K 2] {p m : ℕ}
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hp : p.Prime) (hp2 : p ≠ 2)
    {U : Fin m → Submodule K V} {ef' : Fin m → ↥(orthDerived Q)}
    {E : Subgroup ↥(orthDerived Q)} {u : Fin m → V} {cc t : K}
    (hC : CFSG.StandardType.OmNsRootGen.IsCoherentFrame Q p U ef' E u cc t)
    {x : ↥(orthDerived Q)} {i : Fin m} {z : ZMod p} (hz : z ≠ 0)
    (hx_eq : x = (ef' i) ^ z.val)
    (hdim : Module.finrank K V = 2 * (m + 1)) :
    ∃ (hxO : CFSG.RankThree.PartOne.KCOrthogonal.OddOrderIsometry Q p (x : V ≃ₗ[K] V)),
      CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (x : V ≃ₗ[K] V) =
        CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.polarPerp Q (U i) ∧
      Module.finrank K (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (x : V ≃ₗ[K] V)) =
        2 * m := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hpow_ef : (ef' i) ^ p = 1 := hC.isElemAbelian.2 (ef' i) (hC.toIsPlaneFrame.mem i)
  have hxpow : x ^ p = 1 := by
    rw [hx_eq]
    rw [← pow_mul, mul_comm, pow_mul, hpow_ef, one_pow]
  have hxO : CFSG.RankThree.PartOne.KCOrthogonal.OddOrderIsometry Q p
      (x : V ≃ₗ[K] V) :=
    CFSG.StandardType.OmPlusFrame.oddOrderIsometry_of_orthDerived hQ hp hp2 (t := x) hxpow
  have hx_eq' : ((x : ↥(orthDerived Q)) : V ≃ₗ[K]
      V) =
      (((ef' i : ↥(orthDerived Q)) : V ≃ₗ[K]
      V) ^ z.val) := by
    rw [hx_eq]
    simp only [Subgroup.coe_pow]
  have hx_fix : CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (x : V ≃ₗ[K] V) =
      CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.polarPerp Q (U i) := by
    change CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace ((x : ↥(orthDerived Q)) :
      V ≃ₗ[K] V) =
      CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.polarPerp Q (U i)
    rw [hx_eq']
    have hord : orderOf (((ef' i : ↥(orthDerived Q)) : V ≃ₗ[K]
        V)) = p := by simpa using hC.orderOf_eq i
    have hne1 : (((ef' i : ↥(orthDerived Q)) : V ≃ₗ[K]
        V) ^ z.val) ≠ 1 := by
      intro h1
      have hdvd0 : orderOf (((ef' i : ↥(orthDerived Q)) : V ≃ₗ[K]
          V)) ∣ z.val := orderOf_dvd_of_pow_eq_one h1
      have hdvd : p ∣ z.val := hord ▸ hdvd0
      have hlt : z.val < p := ZMod.val_lt z
      have hz0 : z.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
      have hz0' : (z.val : ZMod p) = 0 := by simp [hz0]
      exact hz ((ZMod.natCast_zmod_val z).symm.trans hz0')
    exact (CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.fixedSpace_eq_of_mem_zpowers hp hord
      (Subgroup.mem_zpowers_iff.mpr ⟨z.val, rfl⟩) hne1).trans
      (hC.toIsPlaneFrame.fixedSpace_eq_polarPerp i)
  have hfixdim : Module.finrank K (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace
      (x : V ≃ₗ[K] V)) = 2 * m := by
    rw [hx_fix, CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.finrank_polarPerp hQ, hdim,
      hC.toIsPlaneFrame.finrank_eq i]
    omega
  exact ⟨hxO, hx_fix, hfixdim⟩


theorem ggCommonJRowOmMinusNonsplit_sparse {K : Type} [Field K] [Finite K] {p m f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f + 1)
    (hm : 3 ≤ m) (hmo : Odd m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {τ : (Fin m → Multiplicative (ZMod p)) →* OrthRest.RMinus K m b c}
    (hτ : Function.Injective τ) (hsign : GGOmMinusNonsplitSignedNormalizer τ)
    (hsgn : ∀ i : Fin m, ∃ w : OrthRest.RMinus K m b c, ∀ f, w * τ f * w⁻¹ = τ (SpCoord.sgnAut i f))
    (hperm : ∀ σ : Equiv.Perm (Fin m), ∃ w : OrthRest.RMinus K m b c,
      ∀ f, w * τ f * w⁻¹ = τ (SpCoord.permAut σ f))
    {g : Fin m → Multiplicative (ZMod p)} (hS : GGCoordSparse g) (hg : g ≠ 1)
    (J : Subgroup (OrthRest.RMinus K m b c))
    (hJ : IsComponentOf J (Subgroup.centralizer ({τ g} : Set (OrthRest.RMinus K m b c))))
    (hcard : Nat.card ↥(τ.range ⊓ Subgroup.centralizer (J : Set (OrthRest.RMinus K m b c))) = p) :
    GGHasLabel ⟨.D, m, f⟩ (↥J ⧸ Subgroup.center ↥J) := by
  classical
  haveI : CharP K 2 := by
    haveI := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  haveI : Fintype K := Fintype.ofFinite K
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hpq' : p ∣ Nat.card K + 1 := by rw [hK]; exact hpq
  have hf1 : 1 ≤ f := by
    by_contra h
    have hf0 : f = 0 := by omega
    subst f
    rw [pow_zero] at hK
    have h2 : 1 < Nat.card K := by
      haveI : Nontrivial K := inferInstance
      simpa [Nat.card_eq_fintype_card] using Fintype.one_lt_card
    omega
  let Q : QuadraticForm K (LargeEvenMinusIdx m → K) := TableBOrth.qMinusForm K m b c
  have hQ : (QuadraticMap.polarBilin Q).Nondegenerate :=
    TableBOrth.nondegenerate_qMinusForm m hirr
  have hVminus : ¬ IsPlusType Q := by
    intro h
    exact CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus (n := m + 1) (by omega) hirr
      ((CFSG.GroupTheory.WeirSylow.isPlusType_congr
        (TableBOrth.qMinusIsometry m b c)).mp h)
  let e : OrthRest.RMinus K m b c ≃* ↥(orthDerived Q) := OrthTorus.rMinusEquiv K m b c
  let T : Subgroup (OrthRest.RMinus K m b c) := τ.range
  let E : Subgroup ↥(orthDerived Q) := T.map e.toMonoidHom
  let x : ↥(orthDerived Q) := e (τ g)
  let J' : Subgroup ↥(orthDerived Q) := J.map e.toMonoidHom
  have hT_ea : IsElemAbelian p T := by
    change IsElemAbelian p τ.range
    have hexp : ∀ a : Fin m → Multiplicative (ZMod p), a ^ p = 1 := by
      intro a
      funext i
      apply Multiplicative.toAdd.injective
      simp only [Pi.pow_apply, toAdd_pow, Pi.one_apply, toAdd_one,
        nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    exact CFSG.StandardType.isElemAbelian_range (p := p)
      (fun a b : Fin m → Multiplicative (ZMod p) => mul_comm a b) hexp τ
  have hT_card : Nat.card T = p ^ m := by
    change Nat.card τ.range = p ^ m
    rw [← Nat.card_congr (MonoidHom.ofInjective hτ).toEquiv, Nat.card_fun,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, Nat.card_fin]
  have hscT := ggCommonJRowOmMinusNonsplit_sc hK hp hp2 hpq hm hmo hirr hT_ea hT_card
  have hE_ea : IsElemAbelian p E := by
    change IsElemAbelian p (T.map e.toMonoidHom)
    exact hT_ea.map e.toMonoidHom
  have hE_card : Nat.card E = p ^ m :=
    (CFSG.StandardType.natCard_map_mulEquiv e T).trans hT_card
  have hscE := CFSG.StandardType.selfCent_map_mulEquiv e hscT
  have hdim : Module.finrank K (LargeEvenMinusIdx m → K) = 2 * (m + 1) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin]
    ring
  have hT : ∃ T : Submodule K (LargeEvenMinusIdx m → K),
      Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0 :=
    (by simpa [Q] using (OrthTorus.charSum_qMinusForm m hirr).2 hm)
  obtain ⟨U, ef', u, cc, t, hC, i, z, hz, hx_eq_e⟩ :=
    exists_coherentFrame_sparse hK hp hp2 hpq' hm hmo hirr hτ hsign hsgn hperm hS hg
      hQ e (by rfl : E = τ.range.map e.toMonoidHom) hE_ea hE_card hscE hT hdim
  have hx_eq : x = (ef' i) ^ z.val := by simpa [x] using hx_eq_e
  obtain ⟨hxO, hx_fix, hfixdim⟩ :=
    fixedSpace_facts hQ hp hp2 hC hz hx_eq hdim
  have hJ' : IsComponentOf J' (Subgroup.centralizer ({x} : Set ↥(orthDerived Q))) := by
    have h := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective hJ
      e.toMonoidHom e.injective
    rw [CFSG.LocalAnalysis.ComponentInitial.map_centralizer_singleton_mulEquiv e (τ g)] at h
    change IsComponentOf J' (Subgroup.centralizer ({x} : Set ↥(orthDerived Q)))
    exact h
  have hJq : CFSG.IsQuasisimple ↥J :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥J).mp hJ.2.2
  exact ggHasLabel_of_plus_fixedBlock (K := K) (p := p) (m := m) (f := f)
    hK hp hp2 hpq' hm hf1 hQ hVminus hC hxO i z hz hx_eq hx_fix hfixdim e hJ' hJq
    (J := J)

