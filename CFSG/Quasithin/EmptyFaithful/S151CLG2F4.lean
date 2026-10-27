module

public import CFSG.Quasithin.EmptyFaithful.S151CLG2F4Pkg
public import CFSG.Quasithin.EmptyFaithful.S151CLG2Norm
public import CFSG.Quasithin.EmptyFaithful.S151CLDef
public import CFSG.Quasithin.H13.ExcludedOrders

public section

namespace CFSG.Quasithin.CLG2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin
open CFSG.Quasithin.H13.VolI CFSG.QuasithinUnique.Setup.X6 CFSG.Blueprint

set_option linter.unusedSectionVars false

section F4


theorem rankTwoOrder_of_f4 {Y : Type} [Group Y] {n : ℕ} (h : Is2F4 n Y) :
    RankTwoOrder (Nat.card Y) := by
  obtain ⟨k, hk, hcard⟩ := CFSG.Quasithin.H13.card_eq_ordTwistedF4_of_reeTitsModel h
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨k, hk, hcard⟩))))))))

theorem isF4_quot_of_isF4 {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hY : Is2F4 n Y)
    (hq : CFSG.Open.IsQuasisimple Y) : Is2F4 n (Y ⧸ CFSG.pCore 2 Y) := by
  have hZ : Subgroup.center Y = ⊥ := (large_Ree_model_two_extensions hY).1
  have h1 : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hq.2
  have hs : IsSimpleGroup Y :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  have h0 : CFSG.pCore 2 Y = ⊥ := GoldMLA.pCore_two_eq_bot_of_simple hq.1 hs
  exact Is2F4.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq h0).trans QuotientGroup.quotientBot).symm hY

theorem compListNo2F4_holds (h38 : A38ForSQTK) (h42 : AsB42) (hLJ : Input15120LJ)
    (hB42 : Input15120B42List) (h118 : TheoremC118) (h126 : TheoremC126)
    (h1416 : StageLemma1416) (h15 : StageLemma1515CE) : CompListNo2F4 := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp n hn hn3 hL
  have hY := isF4_quot_of_isF4 hL hcomp.2.2
  have hXL := g1_le_normalizer_of_rankTwoOrder h38 hc hcomp (rankTwoOrder_of_f4 hY)
  have hSN : s1516 T Z₁ ≤ Subgroup.normalizer (L : Set G) := (s1516_le_g1 T Z₁).trans hXL
  have hsyl : IsSylowTwoOf (s1516 T Z₁ ⊓ L) L := lemma_15_1_20_sylow hc.h18.four hc.hL
  have hS₀' : IsSylowTwoOf ((s1516 T Z₁ ⊓ L).subgroupOf L) (⊤ : Subgroup ↥L) := by
    rw [A312.isSylowTwoOf_top_iff_map, Subgroup.map_subgroupOf_eq_of_le inf_le_right]
    exact hsyl
  have hU := A312.isSylowTwoOf_top_map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
    (QuotientGroup.mk'_surjective _) hS₀'
  obtain ⟨P, hP⟩ := rankTwoParG_f4 hY hU
  exact false_of_rankTwoParG h118 h126 h42 hLJ hB42 h1416 h15 hc hSN hP

end F4

end CFSG.Quasithin.CLG2
