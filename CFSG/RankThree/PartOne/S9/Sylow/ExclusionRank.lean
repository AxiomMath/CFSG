module

public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Foundations.Basic

public section

namespace CFSG.RankThree.PartOne.Sec9Excl

open Subgroup CFSG

variable {G : Type*} [Group G]

theorem le_localRank_of_normalizes [Finite G] {q r : ℕ} (hq : 1 < q) {U X : Subgroup G}
    (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U) (hXc : IsMulCommutative X) (hXe : ∀ x ∈ X, x ^ q = 1)
    (hXr : Nat.card X = q ^ r) (hXU : X ≤ normalizer (U : Set G)) :
    r ≤ CFSG.Assembly.RankThreeEven.localRank q G := by
  have hbdd : BddAbove {k | ∃ H : Subgroup G, CFSG.Assembly.IsTwoLocal H ∧
      CFSG.Assembly.pRank q H = k} := by
    refine ⟨Nat.card G, ?_⟩
    rintro _ ⟨H, -, rfl⟩
    obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank hq H
    have h1 : CFSG.Open.pRank q H < q ^ CFSG.Open.pRank q H := Nat.lt_pow_self hq
    have h2 : Nat.card E ≤ Nat.card G := Subgroup.card_le_card_group E
    change CFSG.Open.pRank q H ≤ Nat.card G
    omega
  exact (CFSG.SectionRank.le_pRank hq hXU ⟨hXc, hXe⟩ hXr).trans
    (le_csSup hbdd ⟨_, ⟨U, hU, hU2, rfl⟩, rfl⟩)

theorem exists_elemAbelian_of_three_le_pRank {q : ℕ} (hq : q.Prime) {P : Subgroup G}
    (h : 3 ≤ CFSG.pRank q P) :
    ∃ r : ℕ, 3 ≤ r ∧ ∃ X : Subgroup G, X ≤ P ∧ IsMulCommutative X ∧ (∀ x ∈ X, x ^ q = 1) ∧
      Nat.card X = q ^ r := by
  have : Fact q.Prime := ⟨hq⟩
  by_contra hcon
  push Not at hcon
  have hle : CFSG.pRank q P ≤ 2 := by
    apply csSup_le'
    rintro r ⟨A, hA, hcard⟩
    by_contra hr
    push Not at hr
    have hAm : IsElementaryAbelian q (A.map P.subtype) := IsElementaryAbelian.map_subtype
    exact hcon r hr (A.map P.subtype) (fun x hx => by
        obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
        exact y.2) hAm.toIsMulCommutative
      (fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx)
      (by rw [Subgroup.card_map_of_injective P.subtype_injective, hcard])
  omega

end CFSG.RankThree.PartOne.Sec9Excl
