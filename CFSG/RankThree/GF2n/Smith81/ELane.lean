module

public import CFSG.RankThree.GF2n.Smith81.EStmt
public import CFSG.RankThree.GF2n.Smith81.Sec215
public import CFSG.RankThree.GF2n.Smith81.Sec2Stmt

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

variable {G : Type} [Group G]

@[expose] def LaneEStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Smith1981Below (Nat.card G) →
    ∀ (M Q Z : Subgroup G), StrothHyp M Q Z →
      ∀ B : Subgroup G, (∃ g : G, B = conjSubgroup g Z) → B ≤ Q → B ≠ Z →
        StrothConclusion M Q Z B → SmithLaneE M Q Z B

section Assembly

theorem smith218E_of_statements (h213 : Smith213EStatement) (h216 : Smith216EStatement)
    (h217 : Smith217Statement) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
      SmithECfg M Q Z B → ∀ z ∈ Z, z ≠ 1 → Timmesfeld.IsRootInvolutionSet (conjClassSet z) := by
  intro G _ _ M Q Z B IH hc z hz hz1
  have hred : ∀ x ∈ conjClassSet z, ∀ z' ∈ conjClassSet z, ∀ w ∈ conjClassSet z,
      ∀ y ∈ conjClassSet z, Commute x z' → Commute z' w → Commute w y →
        ∃ v ∈ conjClassSet z, Commute x v ∧ Commute v y := by
    intro x hx z' hz' w hw y hy h1 h2 h3
    obtain ⟨v, hv, h4, h5⟩ :=
      h216 G M Q Z B IH hc z hz hz1 x z' w y hx hz' hw hy h1 h2 h3
    exact ⟨v, hv, h4, h5⟩
  have hdiam := diam_two_of_connected hred
    (fun x hx y hy => h217 G M Q Z B IH hc.toRemCfg z hz hz1 x y hx hy)
  exact isRootInvolutionSet_conjClassSet hc.ctx.hyp hz hz1 (h213 G M Q Z B IH hc z hz hz1) hdiam

end Assembly

end CFSG.RankThree.GF2n.Smith81
