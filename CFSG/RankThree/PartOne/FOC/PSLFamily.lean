module

public import CFSG.RankThree.PartOne.FOC.PSLOuter
public import CFSG.RankThree.PartOne.FOC.InnerCase
public import CFSG.RankThree.PartOne.FOC.PSLSemisimple
public import CFSG.RankThree.PartOne.FOC.Transfer

public section

namespace CFSG.RankThree.PartOne.FOC

open Subgroup CFSG CFSG.RankThree.PartOne.Sec66T
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def PSLTwoOuter : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p : ℕ), p.Prime → 5 ≤ p → (p : K) ≠ 0 →
    ∀ α : MulAut (projectiveSL 2 K), α ^ p = 1 → α ∉ innerAut (projectiveSL 2 K) →
      ∀ x ∈ fixSub α, x ^ p = 1 → ∀ E : Subgroup (projectiveSL 2 K), IsComponentOf (fixSub α) E →
        x ∈ E

theorem fieldInnerT_psl (h2 : PSLTwoOuter) {p n : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : (p : K) ≠ 0) (hn : 2 ≤ n)
    (hs : IsSimpleGroup (projectiveSL n K)) (hnab : ∃ a b : projectiveSL n K, a * b ≠ b * a) :
    FieldInnerT p (projectiveSL n K) := by
  intro hLR x β E hxp hβp hβx hβinn hE hxN hxnot hLie
  by_cases hβ : β ∈ innerAut (projectiveSL n K)
  · obtain ⟨b, hb⟩ := hβ
    have hcen : Subgroup.center (projectiveSL n K) = ⊥ := center_eq_bot_of_nonab hs hnab
    obtain ⟨hbp, hfix, hbx⟩ := inner_case hcen hb hβp hβx
    rw [hfix] at hE
    exact hxnot (mem_sup_centralizer_of_component_psl hp hp5 hpK (by omega) hLR hbp hxp hbx hE)
  ·
    have hxfix : x ∈ fixSub β := hβx
    by_cases hn2 : n = 2
    · subst hn2
      exact hxnot (Subgroup.mem_sup_left (h2 K p hp hp5 hpK β hβp hβ x hxfix hxp E hE))
    · have hn3 : 3 ≤ n := by omega
      obtain ⟨ℓ, hℓchar⟩ := CharP.exists K
      have hℓ : ℓ.Prime := CharP.char_is_prime K ℓ
      have : Fintype K := Fintype.ofFinite K
      obtain ⟨f, hℓ', hcard⟩ := FiniteField.card K ℓ
      have hK : Nat.card K = ℓ ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hcard
      have hf : 1 ≤ (f : ℕ) := f.pos
      have hpℓ : p ≠ ℓ := by
        intro h
        subst h
        exact hpK (CharP.cast_eq_zero K p)
      have hdiagK : ¬ p ∣ Nat.gcd n (Nat.card K - 1) := by
        intro hd
        have hpn : p ∣ n := hd.trans (Nat.gcd_dvd_left _ _)
        have hpq : p ∣ Nat.card K - 1 := hd.trans (Nat.gcd_dvd_right _ _)
        have hn5 : 5 ≤ n := hp5.trans (Nat.le_of_dvd (by omega) hpn)
        have hpF : p ∣ Nat.card Kˣ := by rw [Nat.card_units]; exact hpq
        exact not_localRankLeTwo_of_SL_hom hp hn5 hpF (proj n K) (fun s hs => by
          rw [← scalars_eq_center, ← ker_proj]
          exact hs) hLR
      obtain ⟨hsimple, -⟩ := fixSub_simple_of_outer_psl hℓ hp hp5 hpℓ hn3 hf hK hdiagK β hβp hβ
      have hEeq := eq_of_isComponentOf_simple hE
      exact hxnot (Subgroup.mem_sup_left (by rw [hEeq]; exact hxfix))

end CFSG.RankThree.PartOne.FOC
