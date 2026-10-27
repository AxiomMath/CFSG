module

public import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
public import CFSG.Quasithin.EmptyFaithful.R3c3Lie
public import CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProofRank
public import CFSG.RankThree.PartTwo.Sec21.Item223Rank2ProofD4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG CFSG.Blueprint

variable {X : Type} [Group X] [Finite X]

theorem pRank_three_eq_two_of_reeTitsModel_twistedF4
    {f : ℕ} (hX : ReeTitsModel X .twistedF4 2 f) :
    CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 := by
  have hlow : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
    CFSG.Quasithin.R3c3.two_le_pRank_three_is2F4 (f := f) (X := X)
      (show CFSG.Quasithin.Is2F4 f X from hX)
  have hle : CFSG.pRank 3 (X ⧸ Subgroup.center X) ≤ 2 :=
    CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProof.twistedF4EvenThreeRankTwo_holds X f hX
  have hmodel : ReeTitsModel X .twistedF4 2 f := hX
  obtain ⟨hadm, a, hfa, K, _, _, hK, ⟨e⟩⟩ := hmodel
  have ha : 1 ≤ a := by
    have := hadm.2.2.2.2.2
    omega
  have : Fintype K := Fintype.ofFinite K
  have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime :=
    charP_of_card_eq_prime_pow (f := f) (by
      rw [← Nat.card_eq_fintype_card, hK]
      rfl)
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  obtain ⟨E⟩ :=
    (CFSG.LieType.Ree.ReeTag.large_Ree_model_Schreier X 2 f hX).2.2.2.2.2 a K hfa hK ⟨e⟩
  have hZ : Subgroup.center X = ⊥ :=
    CFSG.RankThree.PartTwo.Sec21.Item223RankResProof.center_eq_bot_of_mulEquiv E
      (CFSG.LieType.Ree.ReeTag.large_Ree_fixed_group_center_trivial a K hK')
  let eX : X ⧸ Subgroup.center X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hupper : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2 := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top 3 X]
    rw [← CFSG.pRank_congr_of_mulEquiv eX 3]
    exact hle
  exact le_antisymm hupper hlow

theorem pRank_three_eq_two_of_lieModel_twistedF4
    {f : ℕ} (h : LieModel X .twistedF4 0 2 f) :
    CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 :=
  pRank_three_eq_two_of_reeTitsModel_twistedF4
    (h.reeTitsModel (by decide)).2

theorem pRank_three_eq_two_of_chevalleyExceptionalModel_trialityD4
    {f : ℕ}
    (hX : ChevalleyExceptionalModel X .trialityD4 2 f) :
    CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 := by
  have hlow : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
    CFSG.Quasithin.R3c3.two_le_pRank_three_is3D4 (f := f) (X := X)
      (show CFSG.Quasithin.Is3D4 2 f X from hX)
  have hle : CFSG.pRank 3 (X ⧸ Subgroup.center X) ≤ 2 :=
    CFSG.RankThree.PartTwo.Sec21.trialityD4EvenThreeRankTwo_holds X f hX
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hX
  have hZ : Subgroup.center X = ⊥ :=
    CFSG.RankThree.PartTwo.Sec21.Item223RankResProof.center_eq_bot_of_mulEquiv
      (e.trans (CFSG.TauCetiBridge.Twisted.nativeEquiv hp hf hK hσ))
      (CFSG.TauCetiBridge.Twisted.center_graphFixedRootGroup_eq_bot σ)
  let eX : X ⧸ Subgroup.center X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hupper : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2 := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top 3 X]
    rw [← CFSG.pRank_congr_of_mulEquiv eX 3]
    exact hle
  exact le_antisymm hupper hlow

theorem pRank_three_eq_two_of_lieModel_trialityD4
    {f : ℕ}
    (h : LieModel X .trialityD4 0 2 f) :
    CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 :=
  pRank_three_eq_two_of_chevalleyExceptionalModel_trialityD4
    (h.chevalleyExceptionalModel (by decide))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
