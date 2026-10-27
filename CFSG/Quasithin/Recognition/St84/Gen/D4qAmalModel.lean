module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStructNorm
import CFSG.RankThree.PartOne.S11c.Sec66D4Tri
import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModD4
import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsD4Data
import CFSG.Quasithin.Vol2.Ch10SecKHLk2C
import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalExcTwCore
public import CFSG.Quasithin.Recognition.St84.Gen.D4qRadical
public import CFSG.Quasithin.Recognition.F112RShapes
public import CFSG.Quasithin.Background.F6GoldschmidtListCat
public import CFSG.Quasithin.Background.F6SolvableQuotient
import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin
  CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6 CFSG.Quasithin.H13.F431.D4q
  CFSG.Quasithin.H13.F431.D4q.Hex CFSG.Quasithin.H13.Sec53F.TriD4
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

theorem isLieOverTwo_d4 {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) : IsLieOverTwo .trialityD4 0 f (Struct.Cm σ) :=
  CFSG.RankThree.PartOne.Sec66T.lieModel_graphFixedRootGroup_trialityD4 hf hK σ (Or.inl hσ)

theorem isYAmalgamPair_d4 {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    IsYAmalgamPair (Struct.Ust σ) (Struct.Pst0 σ) (Struct.Pst1 σ) :=
  (d4_yamStd σ hf hK (fun c => hσ c)).isYAmalgamPair

theorem pCoreOf_Pst1 [CharP K 2] :
    pCoreOf 2 (Struct.Pst1 σ) =
      (Q1 σ).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  unfold Struct.Pst1 Q1 fa1
  apply Subgroup.map_injective
    (f := (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype)
    (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective
  rw [CFSG.Quasithin.Vol2.Ch10.SecB.C10KH.pCoreOf_subgroupOf_map'
    (graphFixedParabolic_le (t := TwistTag.D4) (K := K) (σ := σ.toRingHom)
      {(⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)})]
  rw [Subgroup.map_subgroupOf_eq_of_le
    (graphFixedParabolicRadical_le_graphFixedRootGroup (t := TwistTag.D4) (K := K)
      (σ := σ.toRingHom) {(⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)})]
  exact CFSG.StandardType.GGOppRadExc.pCoreOf_graphFixedParabolic σ
    {(⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)}

theorem normalizer_Ust_eq_inf :
    Subgroup.normalizer (Struct.Ust σ : Set (Struct.Cm σ)) =
      Struct.Pst0 σ ⊓ Struct.Pst1 σ := by
  rw [d4_normalizer_eq σ]
  refine le_antisymm ?_ ?_
  · refine le_inf ?_ ?_
    · exact Subgroup.subgroupOf_mono _ (graphFixedRootBorel_le_graphFixedParabolic
        (t := TwistTag.D4) (K := K) (σ := σ.toRingHom)
        {(⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)})
    · exact Subgroup.subgroupOf_mono _ (graphFixedRootBorel_le_graphFixedParabolic
        (t := TwistTag.D4) (K := K) (σ := σ.toRingHom)
        {(⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)})
  · intro x hx
    obtain ⟨hx0, hx1⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_subgroupOf.mpr ?_
    rw [← P0_inf_P1 σ]
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hx0,
      Subgroup.mem_subgroupOf.mp hx1⟩

theorem card_pCoreOf_Pst1 {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    Nat.card ↥(pCoreOf 2 (Struct.Pst1 σ)) = 2 ^ (11 * f) := by
  haveI : CharP K 2 := CFSG.Quasithin.H13.F431.D4q.NFq.charP_two_of_std hf hK
  have hle : Q1 σ ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedParabolicRadical_le_graphFixedRootGroup (t := TwistTag.D4) (K := K)
      (σ := σ.toRingHom) {fa1}
  rw [pCoreOf_Pst1 σ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    card_d4Q1 σ hf hK hσ]
  rw [Nat.mul_comm, pow_mul]

end CFSG.Quasithin.F112R.St84

end
