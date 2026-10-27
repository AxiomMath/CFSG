module

public import CFSG.LocalAnalysis.StandardType.GGOrdPToralLang
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcHardE7
public import CFSG.LocalAnalysis.StandardType.GGExcFieldRankE7
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharE7
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.SevenCharE7
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E7FiveAux.Steinberg
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralE7
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralSevenProved
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralSevenE
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcToralityFive
public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourDescent
public import CFSG.RankThree.PartOne.KE.EvenE7E8QPlusDescent
public import CFSG.LieType.Chevalley.GraphFixedF4GroupDescent
public import CFSG.LieType.SeitzGeneration.ExcHighThree.RegularSolvable
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Frames
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Assembly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerTorus
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LieType.Chevalley.OrdinaryRootHyperplaneGeneration
public import CFSG.LieType.Chevalley.ParabolicRadicalsOpposite
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcBruhat
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Chevalley.SteinbergBNF4NativeB2
public import CFSG.RankThree.Chevalley.SteinbergBUF4B2QuarticDescent
public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourTools
public import CFSG.RankThree.PartOne.K133H.G2Plane
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.SLnShape
public import CFSG.RankThree.PartOne.KE.ThreeA1Group

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (IsElemAbelian)
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple (monomialToralAt_E7_five)
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
  (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E7_five)

theorem ggOrdPToralE7RestHard_holds :
    GGOrdPToralE7RestHard := by
  intro f p hf hp hp2 hp7 hpq _
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have htor : ∀ a : Fin Tag.E7.rank → (AlgebraicClosure (GaloisField 2 f))ˣ,
      rootDiagUnit .E7 a ∈ adjointGroup .E7 (AlgebraicClosure (GaloisField 2 f)) := fun a =>
    CFSG.RankThree.Chevalley.torusGroup_le_adjointGroup_of_any (rootDiagUnit_mem_torusGroup_E7 a)
  have hD : ∀ Fr : AlgebraicClosure (GaloisField 2 f) →+* AlgebraicClosure (GaloisField 2 f),
      (∀ c, Fr c = c ^ Nat.card (GaloisField 2 f)) →
      adjointGroup .E7 (AlgebraicClosure (GaloisField 2 f)) ⊓
          (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) =
        (adjointGroup .E7 (GaloisField 2 f)).map
          (baseChangeGL (algebraMap (GaloisField 2 f) (AlgebraicClosure (GaloisField 2 f)))) := by
    intro Fr hFr
    refine le_antisymm (fun x hx =>
      CFSG.RankThree.PartOne.KE.qplus_frobenius_fixed_mem (Or.inl rfl) Fr hFr hx.1 hx.2) ?_
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨ExcHighThree.baseChangeGL_mem_adjointGroup' _ hg,
      units_map_entrywiseHom_baseChangeGL_algebraMap Fr hFr g⟩
  have hpq' : p ∣ Nat.card (GaloisField 2 f) - 1 ∨ p ∣ Nat.card (GaloisField 2 f) + 1 := by
    rw [hK]
    exact hpq
  have hmax : ∀ A : Subgroup (adjointGroup .E7 (GaloisField 2 f)), IsElemAbelian p A →
      Nat.card A ≤ p ^ Tag.E7.rank := by
    intro A hA
    haveI : Fact p.Prime := ⟨hp⟩
    rcases hpq' with h1 | h1
    · have he : orderOf ((Nat.card (GaloisField 2 f) : ℕ) : ZMod p) = 1 := by
        have h0 : ((Nat.card (GaloisField 2 f) - 1 : ℕ) : ZMod p) = 0 :=
          (ZMod.natCast_eq_zero_iff _ _).2 h1
        rw [Nat.cast_sub (by rw [hK]; exact Nat.one_le_two_pow), Nat.cast_one, sub_eq_zero] at h0
        rw [h0, orderOf_one]
      have h7 : degCount .E7 1 = Tag.E7.rank := by decide
      exact h7 ▸ rankLE_E7 hp hp2 he A hA
    · have he : orderOf ((Nat.card (GaloisField 2 f) : ℕ) : ZMod p) = 2 :=
        OrdPInnerExc.orderOf_natCast_eq_two_of_dvd_add_one hp hp2 h1
      have h7 : degCount .E7 2 = Tag.E7.rank := by decide
      exact h7 ▸ rankLE_E7 hp hp2 he A hA
  have hp' : p = 3 ∨ p = 5 ∨ p = 7 := by
    interval_cases p <;> first | omega | exact absurd hp (by norm_num)
  rcases hp' with rfl | rfl | rfl
  · exact OrdPToralLang.ggOrdPToralMax_adjointGroup_of_lang _ Nat.prime_three (by norm_num)
      (monomialToralAt_three_of_block a2BlockToral_E7) e7Neg_smul htor
      (fun a ha => (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E7_three a ha).le) hD
      hpq' hmax
  · exact OrdPToralLang.ggOrdPToralMax_adjointGroup_of_lang _ (by norm_num) (by norm_num)
      monomialToralAt_E7_five e7Neg_smul htor
      (fun a ha => (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E7_five a ha).le) hD
      hpq' hmax
  · exact OrdPToralLang.ggOrdPToralMax_adjointGroup_of_lang _ (by norm_num) (by norm_num)
      (monomialToralAt_seven_of_chainBlock (fun _ hγ => iform_self_E7 hγ)
        (chainBlockToral_E7_six_of_transitive a6ChainTransitive_E7)) e7Neg_smul htor
      (fun a ha => (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E7_seven a ha).le) hD
      hpq' hmax

end CFSG.StandardType

end
