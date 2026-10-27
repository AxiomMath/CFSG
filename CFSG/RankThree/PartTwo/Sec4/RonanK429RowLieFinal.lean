module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowsS
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieG2Row
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieSp4

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429Lie

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

section L3


theorem seven_SL3 : ∀ n : ℕ, 1 ≤ n → RowSOf429 (projSL 3 (GaloisField 2 n)) :=
  rowS429_seven_SL3

theorem seven_SU3 : ∀ n : ℕ, 1 ≤ n → RowSOf429 (projSU 3 2 n) :=
  rowS429_seven_SU3

theorem seven_Sp4 : ∀ n : ℕ, 1 ≤ n → RowSOf429 (projSp 2 (GaloisField 2 n)) :=
  fun n hn => rowSOf429_of_noCfg (noCfgS429_seven_Sp4 n hn)

end L3

section Exc


theorem seven_D4 : ∀ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
    q.p = 2 → RowSOf429 (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group :=
  fun q hq hq2 => rowSOf429_of_noL3 (rowS429NoL3_seven_D4 g2Excl429 q hq hq2)

theorem seven_G2 : ∀ q : TauCeti.PrimePower, q.p = 2 → ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid,
    RowSOf429 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group := by
  intro q hq2 hq
  refine rowSOf429_of_noCfg fun S _ _ hs hna ⟨e⟩ => ?_
  have h3 : 3 ≤ q.p ^ q.exponent := by
    have h := ((TauCeti.LieTypeIndex.valid_iff _).1 hq).1
    simpa only [TauCeti.LieTypeIndex.inStandardRange_iff, TauCeti.PrimePower.card_def] using h
  obtain ⟨F, _, _, hF, ⟨eA⟩⟩ := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
    CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hq hq2 e
  rw [hq2] at hF h3
  have hn : 2 ≤ q.exponent := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ q.exponent ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have eC : AdjointQuotient .G2 F ≃* adjointGroup .G2 F :=
    (QuotientGroup.quotientMulEquivOfEq (center_adjointGroup_eq_bot (τ := .G2) (K := F))).trans
      QuotientGroup.quotientBot
  exact noCfgS429_of_adjointG2 hF hn (eA.trans eC)

end Exc

end CFSG.RankThree.PartTwo.Sec4.RonanK429Lie
