module

public import CFSG.GH74.Generic.GKFCover
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Co0Cls
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Perf
public import CFSG.Monster.B.Final.PinnedBOrder
public import CFSG.Monster.SteinbergMBXGeneratedPerfectCover
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Generic.Certificates
public import CFSG.GH74.Statements
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.SectionRank.CentralLift
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.PerfectCover.HopfFormula
public import CFSG.Sporadic.Co1Block.TwoBCent
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

open CFSG.RankThree.PerfectCover CFSG.Blueprint

theorem doubleCover_of_card_ker_eq_two {E J : Type} [Group E] [Group J] [Finite E]
    (hE : Group.IsPerfect E) (π : E →* J) (hs : Function.Surjective π)
    (hc : π.ker ≤ Subgroup.center E) (hk : Nat.card π.ker = 2) :
    (∃ (E' : Type) (_ : Group E') (_ : Finite E') (_ : Group.IsPerfect E') (π' : E' →* J),
      Function.Surjective π' ∧ π'.ker ≤ Subgroup.center E' ∧ IsPGroup 2 π'.ker ∧
        Nat.card π'.ker = 2 ^ 1) ∧
      2 ∣ Nat.card (hopfMultiplier J) := by
  refine ⟨⟨E, inferInstance, inferInstance, hE, π, hs, hc, ?_, by rw [hk, pow_one]⟩, ?_⟩
  · exact IsPGroup.of_card (by rw [hk, pow_one])
  · have := CFSG.GH74.Generic.card_ker_dvd_hopfMultiplier hE π hs hc
    rwa [hk] at this

section Co1

open CFSG.Monster CFSG.Monster.ScalarKernel CFSG.Monster.VisQuot CFSG.EvenSporadicStandard.TwoCo1
  CFSG.EvenSporadicStandard.TwoCo1.Co0Cls CFSG.Monster.Existence.Compat CFSG.Blueprint.NativeSporadic

theorem doubleCover_Co1_core :
    (∃ (E : Type) (_ : Group E) (_ : Finite E) (_ : Group.IsPerfect E)
        (π : E →* NativeSporadic.Carrier .Co1),
      Function.Surjective π ∧ π.ker ≤ Subgroup.center E ∧ IsPGroup 2 π.ker ∧
        Nat.card π.ker = 2 ^ 1) ∧
      2 ∣ Nat.card (hopfMultiplier (NativeSporadic.Carrier .Co1)) := by
  have hfin : Finite latticeO := finite_latticeO
  have hperf : Group.IsPerfect latticeO := latticeO_isPerfect
  obtain ⟨e⟩ : IsSporadic OLq .Co1 := isSporadic_OLq
  let π : latticeO →* NativeSporadic.Carrier .Co1 := e.toMonoidHom.comp piOLq
  have hker : π.ker = Subgroup.zpowers negOneO := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff e e.injective, piOLq_eq_one_iff, mem_zpowers_negOneO_iff]
  refine doubleCover_of_card_ker_eq_two hperf π
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) ?_ ?_
  · rw [hker, Subgroup.zpowers_le]
    exact negOneO_mem_center
  · rw [hker, Nat.card_zpowers, orderOf_negOneO]

theorem two_dvd_card_hopfMultiplier_Co1 :
    2 ∣ Nat.card (hopfMultiplier (NativeSporadic.Carrier .Co1)) :=
  doubleCover_Co1_core.2

end Co1

section B

open CFSG.Monster.B CFSG.Blueprint.NativeSporadic

theorem nonempty_B_equiv_Cbar :
    Nonempty (NativeSporadic.B ≃* Cbar) :=
  pinned_B_explicit_native_isomorphism_simplicity_and_order.2.1.elim fun e _ =>
    ⟨e.trans (MulEquiv.inv' Cbar).symm⟩

theorem doubleCover_B_core :
    (∃ (E : Type) (_ : Group E) (_ : Finite E) (_ : Group.IsPerfect E)
        (π : E →* NativeSporadic.Carrier .B),
      Function.Surjective π ∧ π.ker ≤ Subgroup.center E ∧ IsPGroup 2 π.ker ∧
        Nat.card π.ker = 2 ^ 1) ∧
      2 ∣ Nat.card (hopfMultiplier (NativeSporadic.Carrier .B)) := by
  obtain ⟨hcomm, hcen, hZ, ⟨e₁⟩, hfinC, -⟩ := short_centralizer_generated_perfect_cover
  obtain ⟨e₂⟩ := nonempty_B_equiv_Cbar
  have hfin : Finite Cgen := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Zstar, hZ]
    have : Nat.card Cbar ≠ 0 := Nat.card_pos.ne'
    exact mul_ne_zero this two_ne_zero
  have hperf : Group.IsPerfect Cgen := ⟨hcomm⟩
  let e : Cgen ⧸ Subgroup.center Cgen ≃* NativeSporadic.Carrier .B := e₁.trans e₂.symm
  refine doubleCover_of_card_ker_eq_two hperf (CFSG.GH74.Generic.centralQuotientMap e)
    (CFSG.GH74.Generic.centralQuotientMap_surjective e)
    (CFSG.GH74.Generic.centralQuotientMap_ker e).le ?_
  rw [CFSG.GH74.Generic.centralQuotientMap_ker e, hcen, hZ]

theorem two_dvd_card_hopfMultiplier_B :
    2 ∣ Nat.card (hopfMultiplier (NativeSporadic.Carrier .B)) :=
  doubleCover_B_core.2

end B

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
