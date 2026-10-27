module

public import CFSG.RankThree.PartTwo.Sec15.Item153Push2ProofAlt
import CFSG.RankThree.PartTwo.Sec15.Item153Push2ProofA6
import CFSG.RankThree.PartTwo.KFacts.K71Residual
import CFSG.CGT.PushingUpLit.CGT6.EmbModule.SL2Alt5
public import CFSG.RankThree.PartTwo.Sec15.Item153Push2ProofPerm
public import CFSG.Sporadic.Schreier.Co1WeightChar

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS Equiv
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] noncomputable def Step153ListedL2R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y ∈ scriptY0Star A (lB A), ∀ n : ℕ, 4 ≤ n → Even n →
      IsEmpty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* projSL 2 (GaloisField 2 n))

@[expose] noncomputable def Step153ListedA6R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y ∈ scriptY0Star A (lB A),
      ∀ S ∈ scriptQPiStar A (lB A) (n155 A Y) (piOf 2), ¬ CharNormal153 Y S → FF153 Y S →
        S ≤ Subgroup.normalizer (Y : Set G) →
        Sec4.IsTripleCover (↥Y ⧸ CFSG.pCore 2 ↥Y) (alternatingGroup (Fin 6)) →
          InvA315 (Y ⊔ S) S

theorem nonempty_projSL_two_two_mulEquiv_alt5 :
    Nonempty (projSL 2 (GaloisField 2 2) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨ι⟩ := KFacts.nonempty_sl2_mulEquiv_projSL (F := GaloisField 2 2) (f := 2)
    (GaloisField.card 2 2 (by norm_num))
  obtain ⟨κ⟩ := CFSG.CGT.PushingUpLit.CGT6.sl2_four_equiv_alt5
  exact ⟨ι.symm.trans κ⟩

theorem step153PushListedR_of (hL2 : Step153ListedL2R) (hA6 : Step153ListedA6R) :
    Step153PushListedR := by
  intro G _ _ A c L hR Y hY S hS hno hFF hSY hT
  have hAF : A ∈ CFSG.RankThree.LocalRank.partTwoF G := hR.mem_partTwoF
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.prop.1.1.2
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := hS.prop.1.1.1.2.2
  have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop
  have hY2 : CFSG.Open.pCoreOf 2 Y ≠ ⊥ := hY.prop.2.2
  rcases hT with ⟨n, hn1, hev, ⟨e⟩⟩ | h6 | h7
  · by_cases hn2 : n = 2
    · subst hn2
      obtain ⟨κ⟩ := nonempty_projSL_two_two_mulEquiv_alt5
      exact Push153B.invA315_of_alt (n := 5) (by norm_num) (by norm_num)
        (fun P _ _ h2 hle hne hn1 hn2 => Push153B.le_of_sylow_five P h2 hle hne hn1 hn2)
        Push153B.sylow_five_comm Push153B.sylow_five_pow hAF hAY hAS hS2 hSY hFF.1 hY2 hno
        (e.trans κ)
    · have hn4 : 4 ≤ n := by
        obtain ⟨k, hk⟩ := hev
        omega
      exact ((hL2 G A c L hR Y hY n hn4 hev).false e).elim
  · exact hA6 G A c L hR Y hY S hS hno hFF hSY h6
  · obtain ⟨e⟩ := h7
    exact Push153B.invA315_of_alt (n := 7) (by norm_num) (by norm_num)
      (fun P _ _ h2 hle hne hn1 hn2 => Push153B.le_of_sylow_seven P h2 hle hne hn1 hn2)
      Push153B.sylow_seven_comm Push153B.sylow_seven_pow hAF hAY hAS hS2 hSY hFF.1 hY2 hno e

theorem step153ListedA6R_of : Step153ListedA6R := by
  intro G _ _ A c L hR Y hY S hS hno hFF hSY hT
  exact Push153B.invA315_of_a6 hR.mem_partTwoF hY.prop.1.1.2 hS.prop.1.1.1.2.2
    (isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop) hSY hFF.1 hY.prop.2.2 hno
    hY.prop.1.2.2.2 hT

theorem step153PushListedR_of_L2 (hL2 : Step153ListedL2R) : Step153PushListedR :=
  step153PushListedR_of hL2 step153ListedA6R_of

end CFSG.RankThree.PartTwo.Sec15
