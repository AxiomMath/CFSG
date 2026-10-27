module

public import CFSG.Quasithin.EmptyFaithful.S151cStmt2
public import CFSG.Quasithin.EmptyFaithful.S152L02
public import CFSG.Quasithin.EmptyFaithful.S152Y21
public import CFSG.Quasithin.EmptyFaithful.S152Y30
public import CFSG.Quasithin.EmptyFaithful.S152Y31
public import CFSG.Quasithin.Background.C1PackS15205J
public import CFSG.Quasithin.EmptyFaithful.S152Y20

public section

namespace CFSG.Quasithin

section Stage15202

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

theorem stageLemma15202_of_ce (h15 : StageLemma1515CE) (h159 : StageLemma1519) :
    StageLemma15202 := by
  intro G _ _ T Mc M hs X hTX hXM hX
  exact lemma_15_2_2 hs.qtfe hs.mf (h15 G T Mc M hs.qtfe hs.mf hs.ce)
    (h159 G T Mc M hs.qtfe hs.mf hs.ce).two hTX hXM hX

end Stage15202

section Stage15203

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

theorem stageLemma15203_of_ce (h113 : StageLemma14113) (h1515 : StageLemma1515CE)
    (h15113 : StageLemma15113) (h15114 : StageLemma15114) (h1521 : StageLemma15201)
    (h1522 : StageLemma15202) (hOm : Om4IsoStatement) : StageLemma15203 := by
  intro G _ _ T Mc M hs
  have h : S152Y.Data T Mc M :=
    ⟨hs.qtfe, hs.mf, h1515 G T Mc M hs.qtfe hs.mf hs.ce, h1521 G T Mc M hs⟩
  have hF := S152Y.frattini_field h (h15113 G T Mc M hs.qtfe hs.mf hs.ce)
    (h15114 G T Mc M hs.qtfe hs.mf hs.ce)
  have hnorm := S152Y.normal_of_frattini h hF
  have key : autOn (yOf152 T Mc M) (V154 T Mc M) ≠ ⊥ ∧
      autOn (yOf152 T Mc M) (V154 T Mc M) =
        ⁅autOn (yOf152 T Mc M) (V154 T Mc M), autOn (rcOf Mc M) (V154 T Mc M)⁆ ∧
      (Case15203i T Mc M ∨ Case15203ii T Mc M ∨ Case15203iii T Mc M) := by
    rcases h.h1521.cases with hOne | hTwo | hThree | hFive
    · have hinv := S152Y.involution_mem_mBar0 h (Or.inl hOne)
      obtain ⟨-, -, ⟨e⟩⟩ := hOne
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨a, b, c⟩ := S152Y.concl_of_dihedral h h113 hOm (n := 3) (by decide) (by decide) e hinv
      exact ⟨a, b, Or.inl c⟩
    · have hinv := S152Y.involution_mem_mBar0 h (Or.inr (Or.inl hTwo))
      obtain ⟨-, ⟨e⟩, -⟩ := hTwo
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨a, b, c⟩ := S152Y.concl_of_dihedral h h113 hOm (n := 3) (by decide) (by decide) e hinv
      exact ⟨a, b, Or.inl c⟩
    · exact S152Y.three_main h h113 hOm hThree hnorm
    · have hinv := S152Y.involution_mem_mBar0 h (Or.inr (Or.inr hFive))
      obtain ⟨-, ⟨e⟩, -⟩ := hFive
      have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      obtain ⟨a, b, c⟩ := S152Y.concl_of_dihedral h h113 hOm (n := 5) (by decide) (by decide) e hinv
      exact ⟨a, b, Or.inl c⟩
  exact ⟨key.1, key.2.1, key.2.2, hnorm, fun hYb => S152Y.unique_of_Yb_eq hs h h1522 hYb, hF,
    S152Y.centralizes_field h⟩

end Stage15203

section Stage15205

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace C1Pack5

variable {G : Type} [Group G] [Finite G]

theorem std5_of_stages_ce {T Mc M : Subgroup G} (h1515 : StageLemma1515CE)
    (h15201 : StageLemma15201) (h15202 : StageLemma15202) (h15203 : StageLemma15203)
    (hs : Setting152 T Mc M) : Std5 T Mc M :=
  ⟨hs, h1515 G T Mc M hs.qtfe hs.mf hs.ce, h15201 G T Mc M hs,
    fun X hTX hXM hX => h15202 G T Mc M hs X hTX hXM hX, h15203 G T Mc M hs⟩

theorem input15205Hard_of_ce (h113 : StageLemma14113) (h1515 : StageLemma1515CE)
    (h15201 : StageLemma15201) (h15202 : StageLemma15202) (h15203 : StageLemma15203)
    (hOm : Om4IsoStatement) : Input15205Hard := by
  intro G _ _ T Mc M hs M₁ hM₁
  by_contra hne
  push Not at hne
  have c : Ctr5 T Mc M M₁ :=
    ⟨std5_of_stages_ce h1515 h15201 h15202 h15203 hs, hM₁, hne.1, hne.2⟩
  by_cases hSix : Case1512Six T Mc M
  · exact c.false_of_Six h113 hOm hSix
  · exact c.false_of_VZ h113 hOm (V154_eq_VZ hSix)

end C1Pack5

end Stage15205

section Stage15206

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType
open scoped commutatorElement

theorem stageLemma15206_of_ce (hFr : S152N2.Frobenius20IsSz2) (h1515 : StageLemma1515CE)
    (h1521 : StageLemma15201) (h3 : StageLemma15203) (h5 : StageLemma15205)
    (hOm : Om4IsoStatement) : StageLemma15206 := by
  intro G _ _ T Mc M hs
  have h : S152Y.Data T Mc M :=
    ⟨hs.qtfe, hs.mf, h1515 G T Mc M hs.qtfe hs.mf hs.ce, h1521 G T Mc M hs⟩
  have c3 := h3 G T Mc M hs
  rcases c3.cases with hi | hii | hiii
  · rcases h.h1521.cases with hOne | hTwo | hThree | hFive
    · obtain ⟨-, hA, ⟨e⟩⟩ := hOne
      refine S152Y.exists_Y1_small_three h c3 hi e ?_
      rw [hA, Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
      omega
    · obtain ⟨-, ⟨e⟩, ⟨e'⟩⟩ := hTwo
      refine S152Y.exists_Y1_small_three h c3 hi e ?_
      rw [Nat.card_congr e'.toEquiv, Nat.card_prod, DihedralGroup.nat_card]
      have : Nat.card (Multiplicative (ZMod 3)) = 3 := by
        rw [Nat.card_eq_fintype_card]
        rfl
      rw [this]
      omega
    · exact S152Y.exists_Y1_i hs h h5 c3 hOm hThree hi
    · exact S152Y.exists_Y1_five hFr h c3 hi hFive
  · exact S152Y.exists_Y1_ii hs h h5 c3 hOm hii
  · exact S152Y.exists_Y1_iii hs h h5 c3 hiii

end Stage15206

end CFSG.Quasithin
