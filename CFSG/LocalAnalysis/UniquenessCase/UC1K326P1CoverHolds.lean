module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K326P1Data
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326CompTop
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326SL3Out
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326SL3Gen
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.TripleCoverWideHolds
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3ResCenter
import CFSG.Adapters.LinearCatalogStated

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

open CFSG.Blueprint (LieModel)

theorem k334Cover_of_kFacts
    (hZ : CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.Bal3ThreeCenter)
    (hW : CFSG.LocalAnalysis.RankThreeTheoremC.KFactAlphaListM3Wide) : K334Cover := by
  intro L _ _ hq hc h3 hr hz
  have hrk : CFSG.Open.pRank 3 (⊤ : Subgroup L) ≤ 3 := by omega
  obtain ⟨hcyc, hZ3⟩ := hZ L hq hc hz h3 hrk
  rcases hW L hq hc hz h3 hcyc hrk with h6 | h7 | hM | hON | ⟨d, hd, ⟨e⟩⟩
  · exact Or.inr (Or.inl ⟨hq, hZ3, h6⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hq, hZ3, h7⟩))
  · obtain ⟨e⟩ := hM
    obtain ⟨φ⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hq, hZ3, ⟨e.trans φ.symm⟩⟩)))
  · obtain ⟨e⟩ := hON
    obtain ⟨φ⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hq, hZ3, ⟨e.trans φ.symm⟩⟩)))
  · obtain ⟨tag, hval⟩ := d
    rcases hd with ⟨q, hdq, h1⟩ | ⟨q, hdq, h1⟩
    · cases hdq
      have hm : CFSG.Open.StatedClassicalModel (L ⧸ Subgroup.center L) .PSL (2 + 1)
          q.p q.exponent :=
        CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hval e
      have hmod : q.p ^ q.exponent % 3 = 1 := by
        have hpos : 0 < q.card := by
          rw [TauCeti.PrimePower.card_def]
          exact Nat.pow_pos q.prime_p.pos
        obtain ⟨k, hk⟩ := h1
        have hcard : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
        omega
      exact Or.inl (Or.inl ⟨q.p, q.exponent, hmod, hq, hZ3, Or.inl ⟨by decide, hm⟩⟩)
    · cases hdq
      have hm : CFSG.Open.StatedClassicalModel (L ⧸ Subgroup.center L) .PSU (2 + 1)
          q.p q.exponent :=
        CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hval e
      have hmod : q.p ^ q.exponent % 3 = 2 := by
        obtain ⟨k, hk⟩ := h1
        have hcard : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
        omega
      exact Or.inl (Or.inr ⟨q.p, q.exponent, hmod, hq, hZ3, Or.inl ⟨by decide, hm⟩⟩)

section

theorem k334Cover_holds : K334Cover :=
  k334Cover_of_kFacts
    (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.bal3ThreeCenter_of_tables
      CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
      CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput
      CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds)
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.TripleCover.kFactAlphaListM3Wide_holds

end

section

theorem k326P2S_holds : K326P2S :=
  K326P2S_of_inputs (k326P1_holds k334Cover_holds) sl3Out_holds sl3Gen_holds

end

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326
