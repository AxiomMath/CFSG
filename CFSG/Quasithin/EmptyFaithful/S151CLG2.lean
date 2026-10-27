module

public import CFSG.Quasithin.EmptyFaithful.S151CLDef
public import CFSG.Quasithin.EmptyFaithful.S151CLG2Pkg
public import CFSG.Quasithin.EmptyFaithful.S151CLG2Norm
public import CFSG.Timmesfeld.Orders.Exceptional

public section

namespace CFSG.Quasithin.CLG2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin
open CFSG.Quasithin.H13.VolI CFSG.QuasithinUnique.Setup.X6
open CFSG.Blueprint

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G]

section G2


theorem rankTwoOrder_of_g2 {Y : Type} [Group Y] {n : ℕ} (hn : 2 ≤ n) (h : IsG2 2 n Y) :
    RankTwoOrder (Nat.card Y) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨n, hn, CFSG.Timmesfeld.card_chevalleyExceptionalModel_two h⟩)))))

theorem isG2_quot_of_isG2 {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hY : IsG2 2 n Y)
    (hq : CFSG.Open.IsQuasisimple Y) : IsG2 2 n (Y ⧸ CFSG.pCore 2 Y) := by
  have hZ : Subgroup.center Y = ⊥ := (even_G2_model_two_extensions hY).1
  have h1 : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hq.2
  have hs : IsSimpleGroup Y :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  have h0 : CFSG.pCore 2 Y = ⊥ := GoldMLA.pCore_two_eq_bot_of_simple hq.1 hs
  exact IsG2.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq h0).trans QuotientGroup.quotientBot).symm hY

theorem compListNoG2_holds (h38 : A38ForSQTK) (h42 : AsB42) (hLJ : Input15120LJ)
    (h118 : TheoremC118) (h126 : TheoremC126) (h1416 : StageLemma1416)
    (h15 : StageLemma1515CE) : CompListNoG2 := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp
  have key : ∀ n : ℕ, 2 ≤ n → IsG2 2 n (↥L ⧸ CFSG.pCore 2 ↥L) → False := by
    intro n hn hY
    have hXL := g1_le_normalizer_of_rankTwoOrder h38 hc hcomp (rankTwoOrder_of_g2 hn hY)
    have hSN : s1516 T Z₁ ≤ Subgroup.normalizer (L : Set G) := (s1516_le_g1 T Z₁).trans hXL
    have hsyl : IsSylowTwoOf (s1516 T Z₁ ⊓ L) L := lemma_15_1_20_sylow hc.h18.four hc.hL
    have hS₀' : IsSylowTwoOf ((s1516 T Z₁ ⊓ L).subgroupOf L) (⊤ : Subgroup ↥L) := by
      rw [A312.isSylowTwoOf_top_iff_map, Subgroup.map_subgroupOf_eq_of_le inf_le_right]
      exact hsyl
    have hU := A312.isSylowTwoOf_top_map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
      (QuotientGroup.mk'_surjective _) hS₀'
    obtain ⟨P, hP⟩ := rankTwoPar_g2 hY hU
    exact false_of_rankTwoPar h118 h126 h42 hLJ h1416 h15 hc hSN hP
  exact ⟨fun n hn hL => key n hn (isG2_quot_of_isG2 hL hcomp.2.2), fun hY => key 2 le_rfl hY⟩

end G2

end CFSG.Quasithin.CLG2
