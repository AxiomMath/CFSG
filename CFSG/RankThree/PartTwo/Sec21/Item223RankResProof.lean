module

public import CFSG.RankThree.PartTwo.Sec21.Item223RankResProofSeven
public import CFSG.RankThree.PartTwo.Sec21.Item223RankResProofZorn
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusResProofRankTwo
import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
import CFSG.Quasithin.Background.SmithB42G2Id

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Blueprint CFSG.Blueprint.Chevalley

namespace Item223RankResProof

theorem center_eq_bot_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : Subgroup.center Y = ⊥) : Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hz' : e z ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hz x]
  rw [h, Subgroup.mem_bot] at hz'
  rw [Subgroup.mem_bot]
  exact e.injective (hz'.trans (map_one e).symm)

theorem pRank_quotient_center_le_two_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (hZ : Subgroup.center Y = ⊥)
    (h : ∀ F : Subgroup Y, CFSG.Assembly.IsElemAbelian 3 F → Nat.card F ≤ 9) :
    CFSG.pRank 3 (X ⧸ Subgroup.center X) ≤ 2 := by
  have hZX := center_eq_bot_of_mulEquiv e hZ
  let φ : X ⧸ Subgroup.center X ≃* Y :=
    ((QuotientGroup.quotientMulEquivOfEq hZX).trans QuotientGroup.quotientBot).trans e
  refine Item223CensusProof.pRank_le_two_of_card_le_nine fun F hF => ?_
  have := h (F.map φ.toMonoidHom) (Sec4.isElemAbelian_map φ.toMonoidHom hF)
  rwa [Subgroup.card_map_of_injective φ.injective] at this

end Item223RankResProof

open Item223RankResProof

theorem g2OddThreeRankTwo_holds :
    G2OddThreeRankTwo := by
  intro p _ hp3 X _ hX
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup .G2 hX.2
  have hp : p.Prime := Fact.out
  have : Fintype K := Fintype.ofFinite K
  have : CharP K p := charP_of_card_eq_prime_pow (f := 1)
    (by rw [← Nat.card_eq_fintype_card, hK])
  have hK2 : ringChar K ≠ 2 := by
    rw [ringChar.eq K p]
    omega
  have hK3 : (3 : K) ≠ 0 := Sec4.three_ne_zero_of_card hp (by omega) hK
  exact pRank_quotient_center_le_two_of_mulEquiv e
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
    (fun F hF => adjointG2_card_le_nine K hK2 hK3 F hF)

theorem g2EvenThreeRankTwo
    (X : Type) [Group X] (f : ℕ) (hX : ChevalleyExceptionalModel X .G2 2 f) :
    CFSG.pRank 3 (X ⧸ Subgroup.center X) ≤ 2 := by
  obtain ⟨hf, K, _, _, _, hK, ⟨e⟩⟩ :=
    CFSG.Quasithin.B42G2Id.exists_cayleyGroup_of_chevalleyExceptionalModel hX
  obtain ⟨c, hc0, hc1⟩ := CFSG.Quasithin.B42G2Id.exists_ne_zero_ne_one_of_three_le (K := K)
    (by rw [hK]; exact CFSG.Quasithin.B42G2Id.three_le_two_pow hf)
  exact pRank_quotient_center_le_two_of_mulEquiv e
    (CFSG.Quasithin.A318Excl.center_cayleyGroup_eq_bot hc0 hc1)
    (fun F hF => cayleyGroup_card_le_nine F hF)

@[expose] def TrialityD4EvenThreeRankTwo : Prop :=
  ∀ (X : Type) [Group X] (f : ℕ), ChevalleyExceptionalModel X .trialityD4 2 f →
    CFSG.pRank 3 (X ⧸ Subgroup.center X) ≤ 2

@[expose] def TwistedF4EvenThreeRankTwo : Prop :=
  ∀ (X : Type) [Group X] (f : ℕ), ReeTitsModel X .twistedF4 2 f →
    CFSG.pRank 3 (X ⧸ Subgroup.center X) ≤ 2

theorem excEvenThreeRankTwo_of
    (hD4 : TrialityD4EvenThreeRankTwo) (hF4 : TwistedF4EvenThreeRankTwo) :
    ExcEvenThreeRankTwo := by
  intro X _ f hX
  rcases hX with h | h | h
  · exact g2EvenThreeRankTwo X f h
  · exact hD4 X f h
  · exact hF4 X f h

end CFSG.RankThree.PartTwo.Sec21
