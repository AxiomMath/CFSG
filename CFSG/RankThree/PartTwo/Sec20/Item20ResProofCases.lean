module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.RankThree.PartTwo.Sec20.Item208OneProof
public import CFSG.RankThree.PartTwo.Sec20.OneStepsProofV

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def Step208CasesCtx : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20One G A M L N c T → T ≤ N →
    scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G) = {M} →
    kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N →
    (∃ n : ℕ, Odd n ∧ Nonempty (kTwenty M c ⧸ CFSG.pCore 2 (kTwenty M c) ≃*
      projSL 3 (GaloisField 2 n))) →
    ¬ kTwenty M c ≤ N →
    Sec18.IsMaxParabolicRankTwo (((kTwenty M c ⊓ N).subgroupOf (kTwenty M c)).map
      (QuotientGroup.mk' (CFSG.pCore 2 (kTwenty M c)))) →
    kTwenty M c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) = kTwenty M c ⊔ T →
    ∀ i : ℕ, CFSG.Quasithin.IsC134Case i (kTwenty M c ⊔ T) (sTwenty M N c T) (kTwenty M c) →
      IsBlock M (kTwenty M c) ∧ vTwenty M c T = CFSG.Open.pCoreOf 2 (kTwenty M c) ∧
        ∃ n : ℕ, Odd n ∧ IsNaturalL3Module (kTwenty M c) (vTwenty M c T) n

@[expose] def Step208CasesCtxFour : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20One G A M L N c T → T ≤ N →
    scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G) = {M} →
    kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N →
    (∃ n : ℕ, Odd n ∧ Nonempty (kTwenty M c ⧸ CFSG.pCore 2 (kTwenty M c) ≃*
      projSL 3 (GaloisField 2 n))) →
    ¬ kTwenty M c ≤ N →
    Sec18.IsMaxParabolicRankTwo (((kTwenty M c ⊓ N).subgroupOf (kTwenty M c)).map
      (QuotientGroup.mk' (CFSG.pCore 2 (kTwenty M c)))) →
    kTwenty M c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) = kTwenty M c ⊔ T →
    ∀ i : ℕ, 1 ≤ i → i ≤ 4 →
      CFSG.Quasithin.IsC134Case i (kTwenty M c ⊔ T) (sTwenty M N c T) (kTwenty M c) →
      IsBlock M (kTwenty M c) ∧ vTwenty M c T = CFSG.Open.pCoreOf 2 (kTwenty M c) ∧
        ∃ n : ℕ, Odd n ∧ IsNaturalL3Module (kTwenty M c) (vTwenty M c T) n

variable {G : Type} [Group G] [Finite G]

theorem not_isC134Case_five_core {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20 G A M L N c T) (hTN : T ≤ N)
    (h207 : kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N)
    (hKN : ¬ kTwenty M c ≤ N) :
    ¬ CFSG.Quasithin.IsC134Case 5 (kTwenty M c ⊔ T) (sTwenty M N c T) (kTwenty M c) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro ⟨-, h5⟩
  have hKM : kTwenty M c ≤ M := kTwenty_le_of_hyp201 hT.toHyp201
  have hTKT : CFSG.ABGLocalTools.IsSylowOf 2 T (kTwenty M c ⊔ T) :=
    hT.sylow.of_le le_sup_right (sup_le hKM hT.sylow.le)
  have hsyl : CFSG.QuasithinUnique.IsSylowTwoOf T (kTwenty M c ⊔ T) := by
    obtain ⟨h1, h2, h3⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hTKT
    exact ⟨h1, h2, h3⟩
  have hST : sTwenty M N c T ≤ T :=
    pCoreOf_le_of_isSylowOf (hT.sylow.of_le (le_inf le_sup_right hTN)
      (inf_le_left.trans (sup_le hKM hT.sylow.le)))
  obtain ⟨hZ, -⟩ := h5 T hsyl hST
  apply hKN
  refine le_trans ?_ h207
  refine le_inf le_rfl fun k hk => Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
  obtain ⟨hzT, hzc⟩ := mem_and_commute_of_mem_zTwenty hz
  have hz2 : z ^ 2 = 1 := by
    obtain ⟨w, hw, rfl⟩ := hz
    rw [SetLike.mem_coe, mem_omegaOneCenter_top_iff] at hw
    have := congrArg Subtype.val hw.2
    simpa using this
  have hzO : z ∈ CFSG.Quasithin.omegaOneCenterOf T :=
    Subgroup.subset_closure ⟨⟨hzT, Subgroup.mem_centralizer_iff.mpr fun t ht => hzc t ht⟩, hz2⟩
  have hzC := (hZ hzO).2
  exact (Subgroup.mem_centralizer_iff.mp hzC k (Subgroup.mem_sup_left hk)).symm

theorem not_isC134Case_five {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20One G A M L N c T) (hTN : T ≤ N)
    (h207 : kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N)
    (hKN : ¬ kTwenty M c ≤ N) :
    ¬ CFSG.Quasithin.IsC134Case 5 (kTwenty M c ⊔ T) (sTwenty M N c T) (kTwenty M c) :=
  not_isC134Case_five_core hT.toCtx20 hTN h207 hKN

theorem step208CasesCtx_of_four (h : Step208CasesCtxFour) : Step208CasesCtx := by
  intro G _ _ A M L N c T hT hTN h204 h207 h3 hKN hpar hLQ i hi
  rcases i with _ | _ | _ | _ | _ | _ | i
  · exact hi.elim
  · exact h G A M L N c T hT hTN h204 h207 h3 hKN hpar hLQ 1 le_rfl (by norm_num) hi
  · exact h G A M L N c T hT hTN h204 h207 h3 hKN hpar hLQ 2 (by norm_num) (by norm_num) hi
  · exact h G A M L N c T hT hTN h204 h207 h3 hKN hpar hLQ 3 (by norm_num) (by norm_num) hi
  · exact h G A M L N c T hT hTN h204 h207 h3 hKN hpar hLQ 4 (by norm_num) le_rfl hi
  · exact (not_isC134Case_five hT hTN h207 hKN hi).elim
  · exact hi.elim

end CFSG.RankThree.PartTwo.Sec20
