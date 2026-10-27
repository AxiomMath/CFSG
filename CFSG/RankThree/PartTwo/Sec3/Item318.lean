module

public import CFSG.RankThree.PartTwo.Sec3.OrderThreeFixedPointFreeModule
public import CFSG.LocalAnalysis.UniquenessCase.UCKAsc82Q64Fix

public section

namespace CFSG.RankThree.PartTwo.Sec3

open Subgroup CFSG.Assembly.LowTwoRank

universe u

variable {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]

theorem false_of_psl_two_gt_seven {K : Type} [Group K] [Finite K]
    {p f : ℕ} (hK : StatedClassicalModel K .PSL 2 p f) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (hq : 7 < p ^ f) {x : K} (hx : orderOf x = 3) [Finite V]
    (ρ : Representation (ZMod 2) K V) (hV : ∃ k v, ρ k v ≠ v)
    (hCV : ∀ v, ρ x v = v → v = 0) : False := by
  obtain ⟨U, hU4, hU2, hxU, hCU⟩ := exists_fourGroup_psl_two hK hp2 hp3 hx
  obtain ⟨g, hg, g', hg', v, hne⟩ :=
    asc82Lemma64Fix_holds K p f hK hp2 hp3 hq V ρ hV U hU4 hU2 x hx hxU hCU hCV
  exact hne (quadratic_of_fixedPointFree_three ρ (hx ▸ pow_orderOf_eq_one x) hCV hxU hCU hg hg' v)

theorem rank3II_3_18_classical_of_singer (hL3 : L3SingerFact)
    {K : Type} [Group K] [Finite K]
    (hK : (∃ p f, StatedClassicalModel K .PSL 2 p f ∧ p ≠ 3) ∨
      (∃ p f, StatedClassicalModel K .PSL 3 p f ∧ p ^ f % 3 = 2) ∨
      (∃ p f, StatedClassicalModel K .PSU 3 p f ∧ p ^ f % 3 = 1))
    {x : K} (hx : orderOf x = 3) [Finite V] [Nontrivial V] (ρ : Representation (ZMod 2) K V)
    (hCV : ∀ v, ρ x v = v → v = 0) :
    ∃ n, StatedClassicalModel K .PSL 2 2 n := by
  have hV : ∃ k v, ρ k v ≠ v := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact ⟨x, v, fun h => hv (hCV v h)⟩
  rcases hK with ⟨p, f, hK, hp3⟩ | ⟨p, f, hK, hq⟩ | ⟨p, f, hK, hq⟩
  · by_cases hp2 : p = 2
    · subst hp2
      exact ⟨f, hK⟩
    have hp : p.Prime := hK.1.1
    have hf : 1 ≤ f := hK.1.2.1
    have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    have hp5 : 5 ≤ p := by
      have := hp.two_le
      have : p ≠ 4 := by rintro rfl; exact absurd hp (by decide)
      omega
    have h5 : 5 ≤ p ^ f := le_trans hp5 (Nat.le_self_pow (by omega) p)
    have h6 : p ^ f ≠ 6 := by rintro h; rw [h] at hodd; exact absurd hodd (by decide)
    rcases (show p ^ f = 5 ∨ p ^ f = 7 ∨ 7 < p ^ f by omega) with h | h | h
    · exact ⟨2, statedClassicalModel_psl_two_four_of_five hK h⟩
    · exact (false_of_psl_three hL3 (statedClassicalModel_psl_three_two_of_seven hK h)
        (by norm_num) hx ρ hV hCV).elim
    · exact (false_of_psl_two_gt_seven hK hp2 hp3 h hx ρ hV hCV).elim
  · exact (false_of_psl_three hL3 hK hq hx ρ hV hCV).elim
  · exact (false_of_psu_three hL3 hK hq hx ρ hV hCV).elim

theorem rank3II_3_18_of_singer_j1
    (hL3 : L3SingerFact) (hJ1 : J1SevenFact) {K : Type} [Group K] [Finite K]
    (hK : (∃ p f, StatedClassicalModel K .PSL 2 p f ∧ p ≠ 3) ∨
      (∃ p f, StatedClassicalModel K .PSL 3 p f ∧ p ^ f % 3 = 2) ∨
      (∃ p f, StatedClassicalModel K .PSU 3 p f ∧ p ^ f % 3 = 1) ∨
      Nonempty (K ≃* CFSG.Blueprint.NativeSporadic.J1))
    {x : K} (hx : orderOf x = 3) [Finite V] [Nontrivial V] (ρ : Representation (ZMod 2) K V)
    (hCV : ∀ v, ρ x v = v → v = 0) :
    ∃ n, StatedClassicalModel K .PSL 2 2 n := by
  rcases hK with hK | hK | hK | hJ
  · exact rank3II_3_18_classical_of_singer hL3 (Or.inl hK) hx ρ hCV
  · exact rank3II_3_18_classical_of_singer hL3 (Or.inr (Or.inl hK)) hx ρ hCV
  · exact rank3II_3_18_classical_of_singer hL3 (Or.inr (Or.inr hK)) hx ρ hCV
  · obtain ⟨e⟩ := hJ
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact (false_of_J1 hJ1 e hx ρ ⟨x, v, fun h => hv (hCV v h)⟩ hCV).elim

end CFSG.RankThree.PartTwo.Sec3
