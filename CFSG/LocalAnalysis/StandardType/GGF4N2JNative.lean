module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434ClOrthCases
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestOddLayer
public import CFSG.RankThree.PartOne.K159.RowFourFixed
public import CFSG.RankThree.Classical.SteinbergBJUnitaryTwoBlock
public import CFSG.RankThree.CentralLiftU.UnitaryThreeLift
public import CFSG.LieType.Universal.Unitary.Comparison

public import CFSG.RankThree.GF2n.Stroth80.GriessOrthSmall
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Faithful
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma41
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Abstract
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434ClSetup
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.PlaneStruct
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.PointConfig
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionCyclic
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionShadow
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityKFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityReduction
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.RankThree.PartOne.CTP.StrongPClassification
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S15K.FixedWitt
public import CFSG.RankThree.PartOne.S15K.LayerModel
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.YGroups.Y322Central
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
public import Certificates.Certificate2154
public import Certificates.Certificate2157
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

namespace CFSG.StandardType.N2Orthogonal

open Polynomial Module QuadraticMap
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
  CFSG.GroupTheory.WeirSylow
  CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434.Cl

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

theorem primaryMultiplicity_le_three_of_minus_eight
    (hK : Nat.card K = 4) (hx : OddOrderIsometry Q 5 x)
    (hdim : finrank K V = 8) (hminus : ¬ IsPlusType Q) (hx1 : x ≠ 1)
    {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap) (hne : h ≠ X - 1) :
    primaryMultiplicity x.toLinearMap h ≤ 3 := by
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hself := selfDual_of_dvd_card_add_one hx (by norm_num [hK]) hh hne
  have hdeg := natDegree_eq_two_of_selfDual hx hK hh hne hself
  have hfix : 2 ≤ finrank K (fixedSpace x) := by
    rcases CFSG.RankThree.PartOne.K159.fixed_type hx Nat.prime_five (by decide)
      (by norm_num [hK]) hdim hminus hx1 with h2 | ⟨h4, -⟩ | ⟨h6, -⟩ <;> omega
  have hsum := Submodule.finrank_add_eq_of_isCompl
    (CFSG.RankThree.PartOne.LIT.isCompl_fixedSpace_commSpace hx.cast_ne_zero hx.pow_eq_one)
  rw [← CFSG.StandardType.OrthRestOdd.fixedSpace_eq_lit x, hdim] at hsum
  have hle := Submodule.finrank_mono
    (CFSG.StandardType.OrthRestOdd.primaryComponent_le_commSpace hx hh hne)
  rw [finrank_primaryComponent, hdeg] at hle
  change 2 * primaryMultiplicity x.toLinearMap h ≤
    finrank K (CFSG.RankThree.PartOne.LIT.commSpace x) at hle
  omega

theorem componentImage_sl2_of_multiplicity_two [Nontrivial V]
    (hQ : (polarBilin Q).Nondegenerate) (hK : Nat.card K = 4)
    (hx : OddOrderIsometry Q 5 x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne : h ≠ X - 1)
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q x h))
    (hm : primaryMultiplicity x.toLinearMap h = 2) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (↥(componentImage Q x h) ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  classical
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hself := selfDual_of_dvd_card_add_one hx (by norm_num [hK]) hh hne
  have hdeg := natDegree_eq_two_of_selfDual hx hK hh hne hself
  obtain ⟨d, ℓ, f, hU, B, hd, hcard, hchar, -, hsymm, hleft, ⟨e⟩⟩ :=
    selfDual_unitary_data hx hh hne hself
  have hd1 : d = 1 := by omega
  subst hd1
  have hℓ : ℓ = 2 := hchar.symm.trans (ringChar.eq K 2)
  subst hℓ
  have hf : f = 2 := Nat.pow_right_injective le_rfl (hcard.symm.trans hK)
  subst hf
  haveI := hU.finite
  obtain ⟨e₂⟩ := CFSG.RankThree.Classical.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2
    hU hsymm hleft hm
  have hFΩ : specialBlock Q x h ≤ orthDerived Q :=
    specialBlock_le_orthDerived_of_perfect hq.1
      ((specialBlock_le_isometryCentralizer h).trans
        (fun _ hg => (Subgroup.mem_inf.mp hg).1))
  let ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))
  have hρ : Function.Injective ρ := by
    apply (MonoidHom.ker_eq_bot_iff ρ).mp
    rw [QuotientGroup.ker_mk']
    exact CFSG.StandardType.OrthRestOdd.scalars_subgroupOf_orthDerived_eq_bot Q hQ
  let eImage : ↥(componentImage Q x h) ≃* ↥(specialBlock Q x h) :=
    ((specialBlock Q x h).subgroupOf (orthDerived Q)).equivMapOfInjective ρ hρ |>.symm |>.trans
      (Subgroup.subgroupOfEquivOfLe hFΩ)
  refine ⟨hU.fixedField, inferInstance, inferInstance, ?_, ⟨eImage.trans (e.trans e₂)⟩⟩
  simpa using hU.card_fixedField

theorem fixedComponentImage_sl2_of_fixed_four [Nontrivial V]
    (hQ : (polarBilin Q).Nondegenerate) (hK : Nat.card K = 4)
    (hx : OddOrderIsometry Q 5 x) (hdim : finrank K (fixedSpace x) = 4)
    (hminus : ¬ IsPlusType (Q.comp (fixedSpace x).subtype)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 16 ∧
      Nonempty (↥(fixedComponentImage Q x) ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  have hts : ∀ U : Submodule K (fixedSpace x), finrank K U = 2 →
      ∃ u ∈ U, (Q.comp (fixedSpace x).subtype) u ≠ 0 := by
    intro U hU
    by_contra hn
    push Not at hn
    exact hminus ⟨U, by omega, hn⟩
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := CFSG.RankThree.PartOne.K159.exists_orthDerived_four_sl2
    (Q.comp (fixedSpace x).subtype) hx.polarBilin_fixed_nondegenerate hdim hts
  refine ⟨F, inferInstance, inferInstance, ?_,
    ⟨(CFSG.RankThree.PartOne.fixedComponentImageEquiv hQ hx).trans e⟩⟩
  norm_num [hK] at hF ⊢
  exact hF

theorem component_cases_of_not_sl2
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hK : Nat.card K = 4) (hdim : finrank K V = 8) (hminus : ¬ IsPlusType Q)
    (a : ProjOrthDerived Q) (ha : a ^ 5 = 1) (ha1 : a ≠ 1)
    (J : Subgroup (ProjOrthDerived Q))
    (hJ : CFSG.Open.IsComponentOf J (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))))
    (hno4 : ∀ (F : Type) [Field F] [Finite F], Nat.card F = 4 →
      IsEmpty (↥J ⧸ Subgroup.center ↥J ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))
    (hno16 : ∀ (F : Type) [Field F] [Finite F], Nat.card F = 16 →
      IsEmpty (↥J ⧸ Subgroup.center ↥J ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) :
    ∃ (x : ↥(orthDerived Q)) (hx : OddOrderIsometry Q 5 (x : V ≃ₗ[K] V)),
      QuotientGroup.mk x = a ∧
      ((∃ h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap, h ≠ X - 1 ∧
          primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h = 3 ∧
          CFSG.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[K] V) h) ∧
          J = componentImage Q (x : V ≃ₗ[K] V) h) ∨
        (finrank K (fixedSpace (x : V ≃ₗ[K] V)) = 6 ∧
          IsPlusType (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype) ∧
          J = fixedComponentImage Q (x : V ≃ₗ[K] V))) := by
  classical
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨x, Rep, hx, Cset, hxa, hRep, hcomp, htype⟩ :=
    exists_components_named Nat.prime_five (by decide) hQ hT
      (by rw [ringChar.eq K 2]; decide) a ha ha1
  have hx1 : (x : V ≃ₗ[K] V) ≠ 1 := by
    intro h
    apply ha1
    rw [← hxa, show x = 1 from Subtype.ext h, QuotientGroup.mk_one]
  refine ⟨x, hx, hxa, ?_⟩
  have hft := CFSG.RankThree.PartOne.K159.fixed_type hx Nat.prime_five (by decide)
    (by norm_num [hK]) hdim hminus hx1
  rcases hcomp J hJ with ⟨h, hh, hne, hq, rfl⟩ | hJC
  · have hh' := hRep.1 hh
    haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh'⟩
    have hge := two_le_multiplicity_of_quasisimple hx hh' hq
    have hle := primaryMultiplicity_le_three_of_minus_eight hK hx hdim hminus hx1 hh' hne
    rcases (show primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h = 2 ∨
      primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h = 3 by omega) with hm | hm
    · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := componentImage_sl2_of_multiplicity_two hQ hK hx hh' hne hq hm
      let eQ := QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
      exact False.elim ((hno4 F hF).false eQ)
    · exact Or.inl ⟨h, hh', hne, hm, hq, rfl⟩
  · rcases htype with ⟨-, rfl⟩ | ⟨hlist, -, -, rfl⟩ | ⟨-, e, h4, hsplit, -, -, rfl⟩
    · exact absurd hJC (Set.notMem_empty J)
    · rw [Set.mem_singleton_iff] at hJC
      subst hJC
      rcases hft with h2 | ⟨h4, hm⟩ | ⟨h6, hp⟩
      · have hge := hlist.1
        omega
      · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := fixedComponentImage_sl2_of_fixed_four hQ hK hx h4 hm
        let eQ := QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
        exact False.elim ((hno16 F hF).false eQ)
      · exact Or.inr ⟨h6, hp, rfl⟩
    · rcases hft with h2 | ⟨h4', hm⟩ | ⟨h6, -⟩
      · omega
      · have hp : IsPlusType (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype) := by
          obtain ⟨S, hS, hzero⟩ := hsplit
          exact ⟨S, by omega, hzero⟩
        exact False.elim (hm hp)
      · omega

open CFSG.RankThree.PartOne CFSG.Assembly in
theorem largeEvenLayer_eq_of_component_position
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hK : Nat.card K = 4) (hdim : finrank K V = 8) (hminus : ¬ IsPlusType Q)
    (u : ↥(orthDerived Q)) (hx : OddOrderIsometry Q 5 (u : V ≃ₗ[K] V))
    (hu1 : (u : V ≃ₗ[K] V) ≠ 1) (J : Subgroup (ProjOrthDerived Q))
    (hJ : CFSG.Open.IsComponentOf J
      (Subgroup.centralizer ({piOrth Q u} : Set (ProjOrthDerived Q))))
    (hpos : (∃ h ∈ primaryFactors (u : V ≃ₗ[K] V).toLinearMap, h ≠ X - 1 ∧
        primaryMultiplicity (u : V ≃ₗ[K] V).toLinearMap h = 3 ∧
        CFSG.IsQuasisimple ↥(specialBlock Q (u : V ≃ₗ[K] V) h) ∧
        J = componentImage Q (u : V ≃ₗ[K] V) h) ∨
      (finrank K (fixedSpace (u : V ≃ₗ[K] V)) = 6 ∧
        IsPlusType (Q.comp (fixedSpace (u : V ≃ₗ[K] V)).subtype) ∧
        J = fixedComponentImage Q (u : V ≃ₗ[K] V))) :
    LargeEvenLayer (Subgroup.centralizer ({piOrth Q u} : Set (ProjOrthDerived Q))) = J := by
  classical
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have ha5 : (piOrth Q u) ^ 5 = 1 := by
    rw [← map_pow]
    have hup : u ^ 5 = 1 := Subtype.ext hx.pow_eq_one
    rw [hup, map_one]
  have ha1 : piOrth Q u ≠ 1 := by
    intro h
    have h1 : u = 1 := (piOrth_injective hQ) (h.trans (map_one (piOrth Q)).symm)
    exact hu1 (congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[K] V)) h1)
  obtain ⟨u', Rep, hx', Cset, hxa, hRep, hcomp, htype⟩ :=
    exists_components_named Nat.prime_five (by decide) hQ hT
      (by rw [ringChar.eq K 2]; decide) (piOrth Q u) ha5 ha1
  have huu : u' = u := (piOrth_injective hQ) hxa
  subst u'
  have hsum := Submodule.finrank_add_eq_of_isCompl
    (CFSG.RankThree.PartOne.LIT.isCompl_fixedSpace_commSpace hx.cast_ne_zero hx.pow_eq_one)
  rw [← CFSG.StandardType.OrthRestOdd.fixedSpace_eq_lit (u : V ≃ₗ[K] V), hdim] at hsum
  have hdegree {g : K[X]} (hg : g ∈ primaryFactors (u : V ≃ₗ[K] V).toLinearMap) (hg1 : g ≠ X - 1) :
      g.natDegree = 2 := by
    have : Fact (Irreducible g) := ⟨irreducible_of_mem_primaryFactors hg⟩
    exact natDegree_eq_two_of_selfDual hx hK hg hg1
      (selfDual_of_dvd_card_add_one hx (by norm_num [hK]) hg hg1)
  have hsize {g : K[X]} (hg : g ∈ primaryFactors (u : V ≃ₗ[K] V).toLinearMap) (hg1 : g ≠ X - 1) :
      2 * primaryMultiplicity (u : V ≃ₗ[K] V).toLinearMap g ≤
        finrank K (CFSG.RankThree.PartOne.LIT.commSpace (u : V ≃ₗ[K] V)) := by
    have : Fact (Irreducible g) := ⟨irreducible_of_mem_primaryFactors hg⟩
    have h := Submodule.finrank_mono (OrthRestOdd.primaryComponent_le_commSpace hx hg hg1)
    rw [finrank_primaryComponent, hdegree hg hg1] at h
    exact h
  have heq : ∀ E : Subgroup (ProjOrthDerived Q), CFSG.Open.IsComponentOf E
      (Subgroup.centralizer ({piOrth Q u} : Set (ProjOrthDerived Q))) → E = J := by
    intro E hE
    rcases hpos with ⟨h, hh, hne, hm, hq, hJ⟩ | ⟨hfix, hplus, hJ⟩
    · have hfix2 : finrank K (fixedSpace (u : V ≃ₗ[K] V)) = 2 := by
        have hmin : 2 ≤ finrank K (fixedSpace (u : V ≃ₗ[K] V)) := by
          rcases K159.fixed_type hx Nat.prime_five (by decide)
            (by norm_num [hK]) hdim hminus hu1 with h2 | ⟨h4, -⟩ | ⟨h6, -⟩ <;> omega
        have hle := hsize hh hne
        rw [hm] at hle
        omega
      have hfull : primaryComponent (u : V ≃ₗ[K] V).toLinearMap h =
          CFSG.RankThree.PartOne.LIT.commSpace (u : V ≃ₗ[K] V) := by
        have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
        apply Submodule.eq_of_le_of_finrank_eq
          (OrthRestOdd.primaryComponent_le_commSpace hx hh hne)
        rw [finrank_primaryComponent, hdegree hh hne]
        change 2 * primaryMultiplicity (u : V ≃ₗ[K] V).toLinearMap h =
          finrank K (CFSG.RankThree.PartOne.LIT.commSpace (u : V ≃ₗ[K] V))
        rw [hm]
        omega
      rcases hcomp E hE with ⟨g, hg, hg1, hgq, hEg⟩ | hEC
      · have hg' := hRep.1 hg
        have : Fact (Irreducible g) := ⟨irreducible_of_mem_primaryFactors hg'⟩
        have hge := two_le_multiplicity_of_quasisimple hx hg' hgq
        have hgh : g = h := by
          by_contra hgh
          have hdisj := disjoint_primaryComponent_of_ne hx hg' hh hgh
          have hsub := OrthRestOdd.primaryComponent_le_commSpace hx hg' hg1
          rw [← hfull] at hsub
          have hb : primaryComponent (u : V ≃ₗ[K] V).toLinearMap g = ⊥ :=
            le_antisymm (fun _ hv => (disjoint_iff_inf_le.mp hdisj) ⟨hv, hsub hv⟩) bot_le
          have hz := Submodule.finrank_eq_zero.mpr hb
          rw [finrank_primaryComponent, hdegree hg' hg1] at hz
          change 2 * primaryMultiplicity (u : V ≃ₗ[K] V).toLinearMap g = 0 at hz
          omega
        rw [hgh] at hEg
        exact hEg.trans hJ.symm
      · rcases htype with ⟨-, hc⟩ | ⟨hlist, -⟩ | ⟨hlist, -⟩
        · rw [hc] at hEC
          exact False.elim (Set.notMem_empty E hEC)
        · have hge := hlist.1
          omega
        · have hge := hlist.1
          omega
    · have hcomm2 : finrank K (CFSG.RankThree.PartOne.LIT.commSpace (u : V ≃ₗ[K] V)) = 2 := by omega
      rcases hcomp E hE with ⟨g, hg, hg1, hgq, hEg⟩ | hEC
      · have hg' := hRep.1 hg
        have : Fact (Irreducible g) := ⟨irreducible_of_mem_primaryFactors hg'⟩
        have hge := two_le_multiplicity_of_quasisimple hx hg' hgq
        have hle := hsize hg' hg1
        omega
      · rcases htype with ⟨-, hc⟩ | ⟨-, -, -, hc⟩ | ⟨-, e, hfour, -⟩
        · rw [hc] at hEC
          exact False.elim (Set.notMem_empty E hEC)
        · rw [hc, Set.mem_singleton_iff] at hEC
          exact hEC.trans hJ.symm
        · omega
  apply le_antisymm
  · exact sSup_le fun E hE => le_of_eq (heq E (isComponentOf_iff_open.mp hE))
  · exact le_sSup (isComponentOf_iff_open.mpr hJ)


open CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank

theorem componentImage_statedSU_of_multiplicity_three [Nontrivial V]
    (hQ : (polarBilin Q).Nondegenerate) (hK : Nat.card K = 4)
    (hx : OddOrderIsometry Q 5 x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne : h ≠ X - 1)
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q x h))
    (hm : primaryMultiplicity x.toLinearMap h = 3) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 16 ∧
      Nonempty (↥(componentImage Q x h) ≃* ↥(StatedSU 3 4 F)) := by
  classical
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hself := selfDual_of_dvd_card_add_one hx (by norm_num [hK]) hh hne
  have hdeg := natDegree_eq_two_of_selfDual hx hK hh hne hself
  obtain ⟨d, ℓ, f, hU, B, hd, hcard, hchar, -, hsymm, hleft, ⟨e⟩⟩ :=
    selfDual_unitary_data hx hh hne hself
  have hd1 : d = 1 := by omega
  subst hd1
  have hℓ : ℓ = 2 := hchar.symm.trans (ringChar.eq K 2)
  subst hℓ
  have hf : f = 2 := Nat.pow_right_injective le_rfl (hcard.symm.trans hK)
  subst hf
  haveI := hU.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hU.charP
  have hF : Nat.card (AdjoinRoot h) = (2 ^ 2) ^ 2 := by simpa using hU.card
  obtain ⟨e₀, he₀⟩ := hU.exists_orthonormal_basis hsymm hleft
  let e₁ := e₀.reindex (finCongr hm)
  have he₁ : ∀ i j : Fin 3, B (e₁ i) (e₁ j) = if i = j then 1 else 0 := by
    intro i j
    simp only [e₁, Module.Basis.reindex_apply, he₀, EmbeddingLike.apply_eq_iff_eq]
  obtain ⟨e₂⟩ := CFSG.RankThree.CentralLiftU.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SUid
    hU e₁ he₁
  have hS : SUid hU.barEquiv 3 = StatedSU 3 4 (AdjoinRoot h) := by
    rw [CFSG.RankThree.CentralLiftU.barEquiv_eq_unitaryInvolution hU,
      SUid_eq_statedSU hF]
    rfl
  have hFΩ : specialBlock Q x h ≤ orthDerived Q :=
    specialBlock_le_orthDerived_of_perfect hq.1
      ((specialBlock_le_isometryCentralizer h).trans
        (fun _ hg => (Subgroup.mem_inf.mp hg).1))
  let eImage : ↥(componentImage Q x h) ≃* ↥(specialBlock Q x h) :=
    (((specialBlock Q x h).subgroupOf (orthDerived Q)).equivMapOfInjective
      (CFSG.RankThree.PartOne.piOrth Q) (CFSG.RankThree.PartOne.piOrth_injective hQ)).symm.trans
      (Subgroup.subgroupOfEquivOfLe hFΩ)
  exact ⟨AdjoinRoot h, inferInstance, inferInstance, inferInstance, by norm_num at hF ⊢; exact hF,
    ⟨eImage.trans (e.trans (e₂.trans (MulEquiv.subgroupCongr hS)))⟩⟩

section FixedPlusSix
open CFSG.Open CFSG.LieType.Universal.Spin CFSG.RankThree.GF2n.Stroth80
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne

noncomputable def fixedPlusSixMarking
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : Module.finrank K V = 8) (hF4 : Nat.card K = 4)
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q 5 x)
    {W : Submodule K V} (hW6 : Module.finrank K W = 6)
    (hWplus : IsPlusType (Q.comp W.subtype))
    (hWfix : W = fixedSpace x)
    (J : Subgroup (ProjOrthDerived Q))
    (hJ : J = fixedComponentImage Q x) :
    J ≃* Matrix.SpecialLinearGroup (Fin 4) K := by
  classical
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hWnd : (QuadraticMap.polarBilin (Q.comp W.subtype)).Nondegenerate := by
    rw [hWfix]
    exact hx.polarBilin_fixed_nondegenerate
  let eW := Classical.choice (nonempty_isometry_quadPlus hWnd (n := 3) (by omega) hWplus)
  let eJ0 : J ≃* orthDerived (Q.comp (fixedSpace x).subtype) :=
    (MulEquiv.subgroupCongr hJ).trans (fixedComponentImageEquiv hQ hx)
  let eJ : J ≃* orthDerived (Q.comp W.subtype) := hWfix.symm ▸ eJ0
  let hE := commutator_orthogonalGroup_quadPlus (K := K) (n := 3) (by norm_num)
  let eStated : orthDerived (quadPlus 3 K) ≃* ↥(StatedOmega (StatedQuadPlus 3 K)) :=
    (MulEquiv.subgroupCongr hE).trans (statedOmegaEquiv (coe_quadPlus 3 K) hE).symm
  let eSL : orthDerived (quadPlus 3 K) ≃* Matrix.SpecialLinearGroup (Fin 4) K :=
    (eStated.trans (Classical.choice (nonempty_statedOmega_quadPlus_three_mulEquiv (K := K) (by omega)))).trans
      (specialLinearGroupEquivStatedSL 4 K).symm
  exact eJ.trans ((orthDerivedEquiv eW).trans eSL)

end FixedPlusSix

end CFSG.StandardType.N2Orthogonal

end
