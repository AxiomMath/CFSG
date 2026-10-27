module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowD4
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowF4Ree
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowTits
import CFSG.LocalAnalysis.UniquenessCase.UC6K332Bridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route

open CFSG.Blueprint
open CFSG.RankThree.PartTwo.Sec4.RonanK432
open CFSG.RankThree.PartTwo.Sec4 (exists_mulEquiv_reeGamma)

theorem three_le_pRank_of_G2_char_three
    {L : Type} [Group L] [Finite L] {f : ℕ} (h : LieModel L .G2 0 3 f) :
    3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hm := h.chevalleyExceptionalModel (by decide)
  have h3 := CFSG.SectionRank.three_mul_le_pRank_of_G2Model (p := 3) (f := f) hm.2
  have hf : 1 ≤ f := hm.1.2.1
  omega

theorem four_le_pRank_of_trialityD4_char_three
    {L : Type} [Group L] [Finite L] {f : ℕ} (h : LieModel L .trialityD4 0 3 f) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hm := h.chevalleyExceptionalModel (by decide)
  exact CFSG.SectionRank.four_le_pRank_of_trialityD4Model (p := 3) (f := f) hm.1.2.1 hm.2

theorem goodRow_trialityD4_two
    {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a)
    {f : ℕ} (h : LieModel S .trialityD4 0 2 f) : GoodRow S := by
  obtain ⟨hadm, K, _, _, hK, σ, hσ, ⟨e⟩⟩ := h.chevalleyExceptionalModel (by decide)
  obtain ⟨q, hqp, hqe⟩ : ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = f :=
    ⟨⟨2, f, Nat.prime_two, hadm.2.1⟩, rfl, rfl⟩
  have hqc : q.card = 2 ^ f := by rw [TauCeti.PrimePower.card_def, hqp, hqe]
  have hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid := by simp
  obtain ⟨φ⟩ := CFSG.TauCetiBridge.Even.twistedBridgeEven_trialityD4 q hq hqp K
    (by rw [hqc]; exact hK) σ (fun x => by rw [hqc]; exact hσ x)
  exact rowOf_trialityD4 q hq hqp S hs hna ⟨e.trans φ⟩

theorem goodRow_twistedF4
    {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a)
    {f : ℕ} (h : LieModel S .twistedF4 0 2 f) : GoodRow S := by
  have hR := (h.reeTitsModel (by decide)).2
  obtain ⟨-, a, -, rfl, K, _, _, _, hK, ⟨e'⟩⟩ := exists_mulEquiv_reeGamma hR
  exact ⟨ListRow.of_mulEquiv e'.symm (listRow_reeGamma a K hK),
    outerRow_of_lieModel_twistedF4 hR.1 h (center_eq_bot_of_simple hs hna)⟩

theorem goodRow_tits
    {S : Type} [Group S] [Finite S] (h : LieModel S .Tits 0 2 1) : GoodRow S := by
  have hm : ReeTitsModel S .Tits 2 1 := (h.reeTitsModel (by decide)).2
  obtain ⟨e'⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv S 2 1 hm
  exact ⟨ListRow.of_mulEquiv e'.symm listRow_titsD,
    outerRow_of_not_three_dvd_outer fun h3 =>
      CFSG.Quasithin.A318P.not_dvd_outer_tits hm Nat.prime_three (by norm_num) h3⟩

end CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route
