module

import CFSG.Models.Blueprint
public import CFSG.Alternating.Multipliers.Small
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem r925_card_generic_exceptional (t : CFSG.Assembly.LowTwoRank.StatedLieTag)
    (n p f : ℕ) :
    Nat.card (CFSG.Blueprint.Multiplier.generic t n p f ×
        CFSG.Blueprint.Multiplier.exceptional t n p f) =
      ((CFSG.Blueprint.Multiplier.genericOrders t n p f).1 *
        (CFSG.Blueprint.Multiplier.genericOrders t n p f).2) *
      ((CFSG.Blueprint.Multiplier.exceptionalOrders t n p f).1 *
        (CFSG.Blueprint.Multiplier.exceptionalOrders t n p f).2) := by
  simp only [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional,
    Nat.card_prod,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod _) ≃ _), Nat.card_zmod]

private theorem r925_card_psl_three_five :
    Nat.card (CFSG.Blueprint.Multiplier.generic .PSL 3 5 1 ×
        CFSG.Blueprint.Multiplier.exceptional .PSL 3 5 1) = 1 := by
  rw [r925_card_generic_exceptional .PSL 3 5 1]
  decide

theorem l35_central_trivial (hGA : CFSG.Open.GriessAllModelsStatement) {E : Type} [Group E]
    [Finite E] (W : Subgroup E) [W.Normal] (hW : W ≤ Subgroup.center E)
    (hE : commutator E = ⊤) (hq : IsL3Five (E ⧸ W)) : W = ⊥ := by
  haveI : Group.IsPerfect E := ⟨hE⟩
  let q : E →* E ⧸ W := QuotientGroup.mk' W
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective W
  have hkerq : q.ker = W := QuotientGroup.ker_mk' W
  have hker_le : q.ker ≤ Subgroup.center E := by rw [hkerq]; exact hW
  have hdvd : Nat.card W ∣
      Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (E ⧸ W)) := by
    have hsurj := CFSG.RankThree.PerfectCover.hopfMultiplierToKer_surjective q hqsurj hker_le
    have h := Subgroup.card_dvd_of_surjective hsurj
    rwa [hkerq] at h
  have hcard : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (E ⧸ W)) =
      Nat.card (griessHopfMultiplier (E ⧸ W)) :=
    (Nat.card_congr
      (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess (E ⧸ W)).toEquiv).symm
  rw [hcard] at hdvd
  have hm : CFSG.Models.LieModel (E ⧸ W) .PSL 3 5 1 :=
    CFSG.Models.LieModel.of_blueprint (t := .PSL) (n := 3) (p := 5) (f := 1) (by decide) hq
  obtain ⟨-, ⟨eG⟩⟩ := hGA (E ⧸ W) .PSL 3 5 1 hm
  have hone : Nat.card (griessHopfMultiplier (E ⧸ W)) = 1 := by
    rw [Nat.card_congr eG.toEquiv, r925_card_psl_three_five]
  rw [hone] at hdvd
  exact Subgroup.eq_bot_of_card_eq W (Nat.dvd_one.mp hdvd)

theorem a5_central_card_le_two {E : Type} [Group E] [Finite E]
    (W : Subgroup E) [W.Normal] (hW : W ≤ Subgroup.center E) (hE : commutator E = ⊤)
    (hq : IsAlt (E ⧸ W) 5) : Nat.card W ≤ 2 := by
  haveI : Group.IsPerfect E := ⟨hE⟩
  obtain ⟨e⟩ := hq
  let q : E →* alternatingGroup (Fin 5) := e.toMonoidHom.comp (QuotientGroup.mk' W)
  have hqsurj : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective W)
  have hkerq : q.ker = W := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hker_le : q.ker ≤ Subgroup.center E := by rw [hkerq]; exact hW
  have hdvd : Nat.card W ∣
      Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (alternatingGroup (Fin 5))) := by
    have hsurj := CFSG.RankThree.PerfectCover.hopfMultiplierToKer_surjective q hqsurj hker_le
    have h := Subgroup.card_dvd_of_surjective hsurj
    rwa [hkerq] at h
  rw [(CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_five).2] at hdvd
  exact Nat.le_of_dvd (by norm_num) hdvd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
