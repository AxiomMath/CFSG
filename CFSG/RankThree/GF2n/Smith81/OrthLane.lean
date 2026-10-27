module

public import CFSG.RankThree.GF2n.Smith81.OrthStmt
public import CFSG.RankThree.GF2n.Smith81.Sec2FStar
public import CFSG.RankThree.GF2n.Smith81.Sec2Stmt

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

variable {G : Type} [Group G]

@[expose] def LaneOrthStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Smith1981Below (Nat.card G) →
    ∀ (M Q Z : Subgroup G), StrothHyp M Q Z →
      ∀ B : Subgroup G, (∃ g : G, B = conjSubgroup g Z) → B ≤ Q → B ≠ Z →
        StrothConclusion M Q Z B → SmithLaneOrth M Q Z B

section Assembly

theorem smith218Orth_of_statements (h213 : Smith213OrthStatement)
    (h216 : Smith216OrthStatement) (h217 : Smith217Statement) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
      SmithOrthCfg M Q Z B → ∀ z ∈ Z, z ≠ 1 → Timmesfeld.IsRootInvolutionSet (conjClassSet z) := by
  intro G _ _ M Q Z B IH hc z hz hz1
  have hred : ∀ x ∈ conjClassSet z, ∀ z' ∈ conjClassSet z, ∀ w ∈ conjClassSet z,
      ∀ y ∈ conjClassSet z, Commute x z' → Commute z' w → Commute w y →
        ∃ v ∈ conjClassSet z, Commute x v ∧ Commute v y := by
    intro x hx z' hz' w hw y hy h1 h2 h3
    obtain ⟨v, hv, h4, h5⟩ :=
      h216 G M Q Z B IH hc.toRemCfg hc.orth z hz hz1 x z' w y hx hz' hw hy h1 h2 h3
    exact ⟨v, hv, h4, h5⟩
  have hdiam := diam_two_of_connected hred
    (fun x hx y hy => h217 G M Q Z B IH hc.toRemCfg z hz hz1 x y hx hy)
  exact isRootInvolutionSet_conjClassSet hc.ctx.hyp hz hz1 (h213 G M Q Z B hc z hz hz1) hdiam

theorem smithLaneOrth_of_inputs (hT : TimmesfeldOutcomeStatement)
    (h212 : Smith212OrthCoreStatement) (h213 : Smith213OrthStatement)
    (hCount : Smith216OrthCountStatement) (hOdd : Smith216OrthOddStatement)
    (h217 : Smith217Statement) (hInsp : Smith219OrthInspectionStatement) : LaneOrthStep := by
  intro G _ _ hb M Q Z hH B hB hBQ hBZ hC
  have hcfg : Cfg M Q Z B := ⟨⟨hH, hB, hBQ, hBZ⟩, hC⟩
  have h216 := smith216Orth_of_statements h212 h213 hCount hOdd
  have key : OrthCase M Q Z B → SmithLaneOrth M Q Z B := by
    intro hO
    have hOC : SmithOrthCfg M Q Z B := ⟨hcfg, hO⟩
    obtain ⟨z₀, hz₀, hz₀1, -⟩ := exists_mem_Z_ne hH 1
    have hroot := smith218Orth_of_statements h213 h216 h217 G M Q Z B hb hOC
    exact hInsp G M Q Z B hOC hroot
      (outcome_of_conjClassSet hT hH hz₀ hz₀1 (hroot z₀ hz₀ hz₀1))
  refine ⟨fun t ht h => ?_, fun t ht h => ?_, fun t m ht h => ?_, fun t m ht h => ?_⟩
  · exact (key ⟨t, ht, Or.inl ((caseE1_iff M Q Z B t).mpr (Or.inl h))⟩).1 t ht h
  · exact (key ⟨t, ht, Or.inl ((caseE1_iff M Q Z B t).mpr (Or.inr h))⟩).2.1 t ht h
  · exact (key ⟨t, ht, Or.inr ⟨m, (caseE2_iff M Q Z B t m).mpr (Or.inl h)⟩⟩).2.2.1 t m ht h
  · exact (key ⟨t, ht, Or.inr ⟨m, (caseE2_iff M Q Z B t m).mpr (Or.inr h)⟩⟩).2.2.2 t m ht h

end Assembly

end CFSG.RankThree.GF2n.Smith81
