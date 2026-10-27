module

public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailStmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

section Arith

theorem sec7_four_lt_pow (m : ℕ) (hm : 6 ≤ m) : 4 * m - 2 < 2 ^ (m - 1) := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have e : k + 1 - 1 = (k - 1) + 1 := by omega
    rw [e, pow_succ]
    omega

theorem sec7_four_lt_pow_self (m : ℕ) (hm : 4 ≤ m) : 4 * m - 2 < 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ]
    omega

theorem sec7_two_lt_pow (m : ℕ) (hm : 3 ≤ m) : 2 * m < 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ]
    omega

theorem sec7_two_lt_pow_pred (m : ℕ) (hm : 5 ≤ m) : 2 * m < 2 ^ (m - 1) := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have e : k + 1 - 1 = (k - 1) + 1 := by omega
    rw [e, pow_succ]
    omega

end Arith

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem step71Vanish_of_steps (hBound : Step71VanishBoundStatement)
    (hOrder : Sec7WVOrderStatement) (hF7 : Sec7WVGeOm4Statement) (hGe : Sec7WVGeStatement)
    (hOm10 : Step71VanishOmega10Statement) : Step71VanishStatement := by
  intro G _ _ M Q Z B hc n t hs hno x hx hxt v hv
  by_contra hcon
  have hex : ∃ x : G, ConjMod M Q t x ∧ ⁅x, t⁆ ∈ Q ∧
      ∃ v ∈ Vt M (LB M Q B) B Z t, ⁅x, v⁆ ∉ Z := ⟨x, hx, hxt, v, hv, hcon⟩
  obtain ⟨m, hm2, hm⟩ := hs.orth
  have hb := hBound G M Q Z B hc n t hs hno hex m hm2 hm
  obtain ⟨hOM, hOP⟩ := hOrder G M Q Z B hc n t hs m hm2
  rcases hm with hP | hMi
  · have hm3 : 3 ≤ m := by
      by_contra hlt
      have h2 : m = 2 := by omega
      subst h2
      exact hs.notPlus4 hP
    obtain ⟨y, hy1, hy2⟩ := hOP hP hm3
    have hy3 : y * 2 ^ (m - 1) ≤ 4 * m - 2 := by omega
    have hpow : 2 ^ (m - 1) ≤ y * 2 ^ (m - 1) := Nat.le_mul_of_pos_left _ hy1
    have hm5 : m ≤ 5 := by
      by_contra h6
      have := sec7_four_lt_pow m (by omega)
      omega
    interval_cases m
    · norm_num at hy2 hy3
      have hy : y = 1 ∨ y = 2 := by omega
      rcases hy with rfl | rfl
      · have h10 := hGe G M Q Z B hc n t hs hP
        omega
      · exact hno (Or.inr (Or.inr (Or.inl ⟨hP, by omega⟩)))
    · norm_num at hy2 hy3
      have hy : y = 1 := by omega
      subst hy
      exact hno (Or.inr (Or.inr (Or.inr ⟨hP, by omega⟩)))
    · norm_num at hy2 hy3
      have hy : y = 1 := by omega
      subst hy
      exact hcon (hOm10 G M Q Z B hc n t hs hno hP (by omega) x hx hxt v hv)
  · obtain ⟨y, hy1, hy2⟩ := hOM hMi
    have hy3 : y * 2 ^ m ≤ 4 * m - 2 := by omega
    have hpow : 2 ^ m ≤ y * 2 ^ m := Nat.le_mul_of_pos_left _ hy1
    have hm4 : m ≤ 3 := by
      by_contra h4
      have := sec7_four_lt_pow_self m (by omega)
      omega
    interval_cases m
    · norm_num at hy2 hy3
      have hy : y = 1 := by omega
      subst hy
      have h8 := hF7 G M Q Z B hc n t hs hMi
      omega
    · norm_num at hy2 hy3
      have hy : y = 1 := by omega
      subst hy
      exact hno (Or.inr (Or.inl ⟨hMi, by omega⟩))

theorem step71Type_of_steps (hV : Step71VanishStatement) (hSec : Step71TypeSecStatement)
    (hOrd : Sec7WVSecOrderStatement) : Step71TypeStatement := by
  intro G _ _ M Q Z B hc n t hs hno ⟨x, hx, hxt, w, hw, hwV⟩
  have hvan := hV G M Q Z B hc n t hs hno x hx hxt
  obtain ⟨P, hVP, hPW, hPR, hPN, hPdec, hPcard⟩ :=
    hSec G M Q Z B hc n t hs hno x hx hxt hvan ⟨w, hw, hwV⟩
  obtain ⟨m, hm2, hm⟩ := hs.orth
  have hcardP := hPcard m hm2 hm
  have hord := hOrd G M Q Z B hc n t hs P hVP hPW hPR hPN hPdec m hm2
  have hq : 1 < Nat.card Z := by
    have := hc.hyp.q4
    omega
  have hVpos : 0 < Nat.card ↥(Vt M (LB M Q B) B Z t) := Nat.card_pos
  rcases hm with hP | hMi
  · have hm3 : 3 ≤ m := by
      by_contra hlt
      have h2 : m = 2 := by omega
      subst h2
      exact hs.notPlus4 hP
    have h1 := (hord.2 hP hm3).trans hcardP
    have h2 := Nat.le_of_mul_le_mul_left h1 hVpos
    have h3 := (Nat.pow_le_pow_iff_right hq).mp h2
    have h4 : m ≤ 4 := by
      by_contra h5
      have := sec7_two_lt_pow_pred m (by omega)
      omega
    interval_cases m
    · exact Or.inr (Or.inl hP)
    · exact Or.inr (Or.inr hP)
  · have h1 := (hord.1 hMi).trans hcardP
    have h2 := Nat.le_of_mul_le_mul_left h1 hVpos
    have h3 := (Nat.pow_le_pow_iff_right hq).mp h2
    have h4 : m ≤ 2 := by
      by_contra h5
      have := sec7_two_lt_pow m (by omega)
      omega
    have h5 : m = 2 := by omega
    subst h5
    exact Or.inl hMi

theorem sec73Card_of_parts (hα : Sec73CardAlphaStatement) (hβ : Sec73CardBetaStatement)
    (hF7 : Sec7WVGeOm4Statement) : Sec73CardStatement := by
  intro G _ _ M Q Z B hc n t hs hno hom
  refine ⟨hα G M Q Z B hc n t hs hno hom, fun β hβL hβN => ?_⟩
  have h8 := hF7 G M Q Z B hc n t hs hom
  have hq : 1 < Nat.card Z := by
    have := hc.hyp.q4
    omega
  calc Nat.card Z ^ 8 < Nat.card Z ^ (n + 1) := Nat.pow_lt_pow_right hq (by omega)
    _ ≤ Nat.card ↥(Ut Q Z β) := hβ G M Q Z B hc n t hs hno hom β hβL hβN

end CFSG.RankThree.GF2n.Stroth80
