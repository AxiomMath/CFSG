module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenSCDefs
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.LocalAnalysis.ComponentInitial.BlockCentralQuotient
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmBlock
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmSmallBlock
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSpNsFrame
public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassicalOrthTwoLocal
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.Basic
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.RankThree.PartOne.BRANCH.RankRee
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143X.KF64WSimple
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.StandardType

open Module QuadraticMap
open Polynomial
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.HardMathSupport.Timmesfeld.CrossChar (cyc3 cyc3_ne_X_sub_one NoNormalPPrime)

theorem ggTorusCompMeetSC_orthDerivedTwo {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate) :
    GGTorusCompMeetSC 3 ↥(orthDerived Q) := by
  intro E hE _ hsc x hx hx1 J hJ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set a : V ≃ₗ[K] V := (x : V ≃ₗ[K] V) with ha
  have hxpow : x ^ 3 = 1 := hE.2 x hx
  have hxord : orderOf x = 3 := orderOf_eq_prime hxpow hx1
  have hxIso : OddOrderIsometry Q 3 a := by
    rw [ha]
    refine oddOrderIsometry_of_orthDerived Nat.prime_three ?_ hQ x hxord
    rw [ringChar.eq K 2]
    norm_num
  have hcent : (Subgroup.centralizer ({x} : Set ↥(orthDerived Q))).map
      (orthDerived Q).subtype =
      orthDerived Q ⊓ Subgroup.centralizer ({a} : Set (V ≃ₗ[K] V)) := by
    rw [ha]
    exact map_subtype_centralizer_singleton (orthDerived Q) x
  set L : Subgroup (V ≃ₗ[K] V) := J.map (orthDerived Q).subtype with hLdef
  have hL : CFSG.Assembly.IsComponentOf L
      (orthDerived Q ⊓ Subgroup.centralizer ({a} : Set (V ≃ₗ[K] V))) := by
    rw [hLdef, ← hcent]
    exact CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective hJ
      (orthDerived Q).subtype (orthDerived Q).subtype_injective
  obtain ⟨_, _, hnorm, -⟩ :=
    SevOm.exists_block_of_isComponentOf hxIso Nat.prime_three (by norm_num) hL
  have hL' : CFSG.Assembly.IsComponentOf L (isometryCentralizer Q a) :=
    SevOm.isComponentOf_isometryCentralizer hL
  obtain ⟨h', hh', hLF'⟩ := SevOm.exists_le_supportedBlock hxIso hL'
  have h3L : 3 ∣ Nat.card L := by
    rcases CFSG.HardMathSupport.Dickson.Bal207.OrthRow.Two.primaryFactor_cases hK hxIso hh'
      with hX | hcyc
    ·
      subst hX
      rcases SevOmSmall.fixed_case_small hxIso Nat.prime_three (by norm_num) hL' hLF'
        with hin | ⟨hK4, -⟩
      · by_cases hdim2 : finrank K (fixedSpace a) ≤ 2
        ·
          exfalso
          have : Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup
              (Q.comp (fixedSpace a).subtype)) :=
            CFSG.StandardType.LayerCores.OrthRegular.isSolvable_orthogonalGroup_of_finrank_le_two
              hxIso.polarBilin_fixed_nondegenerate hdim2
          have hFsolv : Group.IsSolvable ↥(supportedBlock Q a (X - 1)) :=
            solvable_of_solvable_injective
              (f := (fixedBlockEquiv hxIso).toMonoidHom) (fixedBlockEquiv hxIso).injective
          have hLq : CFSG.IsQuasisimple L :=
            (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native L).1
              hL.2.2
          exact CFSG.StandardType.ClNonsplit.not_isQuasisimple_of_le hFsolv hLF' hLq
        ·
          have hdim3 : 3 ≤ finrank K (fixedSpace a) := by omega
          obtain ⟨k, hk⟩ := hxIso.even_finrank_fixed
          have hk2 : 2 ≤ k := by omega
          have hdim : finrank K (fixedSpace a) = 2 * ((k - 1) + 1) := by omega
          have hm : 1 ≤ k - 1 := by omega
          have h3O : 3 ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup
              (Q.comp (fixedSpace a).subtype)) :=
            CFSG.HardMathSupport.Dickson.Bal207.OrthRow.Two.three_dvd_natCard_orthogonalGroup_two
              (W := fixedSpace a) (R := Q.comp (fixedSpace a).subtype) hK
              hxIso.polarBilin_fixed_nondegenerate (m := k - 1) hdim hm
          obtain ⟨U, hU3, hU1, -⟩ :=
            CFSG.HardMathSupport.Dickson.Bal207.OrthEight.exists_supportedBlock_pow_three
              hxIso h3O
          have hU3' : (U : V ≃ₗ[K] V) ^ 3 = 1 := by
            simpa using congrArg Subtype.val hU3
          have hUmem : (U : V ≃ₗ[K] V) ∈ L := hin U.1 U.2 hU3'
          have hU1' : (U : V ≃ₗ[K] V) ≠ 1 := fun h => hU1 (Subtype.ext h)
          have hord : orderOf (U : V ≃ₗ[K] V) = 3 := orderOf_eq_prime hU3' hU1'
          rw [← hord]
          exact Subgroup.orderOf_dvd_natCard L hUmem
      · rw [hK] at hK4
        omega
    ·
      subst hcyc
      have hLeq : L = specialBlock Q a (cyc3 K) :=
        SevOm.free_case hxIso Nat.prime_three (by norm_num) hh'
          (cyc3_ne_X_sub_one K) hL' hLF'
      rw [Nat.prime_three.dvd_iff_not_coprime]
      intro hcop
      have hNoL : NoNormalPPrime 3 L := by
        rw [hLeq]
        exact CFSG.HardMathSupport.Dickson.Bal207.OrthRow.Two.noNormalPPrime_specialBlock_cyc3
          hK hxIso hh'
      have hbot : L = ⊥ :=
        hNoL L le_rfl (fun y hy z hz => L.mul_mem (L.mul_mem hy hz) (L.inv_mem hy)) hcop
      have hLq : CFSG.IsQuasisimple L :=
        (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native L).1 hL.2.2
      have hLne : L ≠ ⊥ :=
        (Subgroup.nontrivial_iff_ne_bot L).mp (CFSG.LocalCores.isQuasisimple_nontrivial hLq)
      exact hLne hbot
  have : Finite (V ≃ₗ[K] V) := by
    have : Finite V := Module.finite_of_finite K
    exact Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
      fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  set A : Subgroup (V ≃ₗ[K] V) := E.map (orthDerived Q).subtype with hAdef
  have hA3 : IsPGroup 3 A := by
    intro g
    have hg : (g : V ≃ₗ[K] V) ∈ E.map (orthDerived Q).subtype := hAdef ▸ g.2
    obtain ⟨e, he, hge⟩ := Subgroup.mem_map.mp hg
    refine ⟨1, ?_⟩
    rw [pow_one]
    apply Subtype.ext
    show (g : V ≃ₗ[K] V) ^ 3 = 1
    rw [← hge]
    simpa using congrArg Subtype.val (hE.2 e he)
  have hAnorm : ∀ c ∈ A, ∀ l ∈ L, c * l * c⁻¹ ∈ L := by
    intro c hc l hl
    have hc' : c ∈ E.map (orthDerived Q).subtype := hAdef ▸ hc
    obtain ⟨e, he, hce⟩ := Subgroup.mem_map.mp hc'
    have hec : (e : V ≃ₗ[K] V) ∈ isometryCentralizer Q a := by
      refine Subgroup.mem_inf.mpr ⟨orthDerived_le_orthogonalGroup e.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ha]
      have hcomm : (e * x : ↥(orthDerived Q)) = x * e := by
        simpa only [Subgroup.coe_mul] using congrArg Subtype.val
          (hE.1.is_comm.comm (⟨e, he⟩ : E) (⟨x, hx⟩ : E))
      simpa only [Subgroup.coe_mul] using congrArg Subtype.val hcomm
    have he3 : (e : V ≃ₗ[K] V) ^ 3 = 1 := by
      simpa using congrArg Subtype.val (hE.2 e he)
    simpa [← hce] using hnorm (e : V ≃ₗ[K] V) hec he3 l hl
  obtain ⟨w, hwL, hw1, hw3, hwcomm⟩ :=
    SevSpNs.exists_mem_inf_centralizer Nat.prime_three (A := A) (N := L) hA3 hAnorm h3L
  obtain ⟨j, hjJ, hwj⟩ := Subgroup.mem_map.mp hwL
  subst w
  have hjcomm : ∀ Y ∈ E, j * Y = Y * j := by
    intro Y hY
    apply Subtype.ext
    have hY' : (Y : V ≃ₗ[K] V) ∈ A := by
      rw [hAdef]
      exact Subgroup.mem_map.mpr ⟨Y, hY, rfl⟩
    exact (hwcomm (Y : V ≃ₗ[K] V) hY').symm
  have hj3 : j ^ 3 = 1 := Subtype.ext (by simpa using hw3)
  have hj1 : j ≠ 1 := fun h => hw1 (by simpa using congrArg Subtype.val h)
  exact ⟨j, hjJ, hsc j hjcomm hj3, hj1⟩

end CFSG.StandardType
