module

public import CFSG.Quasithin.Vol2.KGFactInspL3Two
public import CFSG.Quasithin.Vol2.KGFactInspL2U3
public import CFSG.Quasithin.Vol2.KGFactInsp4316Out
public import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder

public section

namespace CFSG.Quasithin.H13.KGInsp4316

open CFSG.Open hiding StatedSL StatedSp StatedClassicalModel StatedLieTag
open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def Insp4316L3epsOdd : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (S R K : Subgroup X) (n : ℕ) (x : X), Cfg4316 S R K n x →
    R ≤ S → ∀ x' ∈ Subgroup.zpowers x, orderOf x' = 3 → x' ∈ S →
    ∀ (s : Bool) (p e : ℕ), p.Prime → p ≠ 2 → 1 ≤ e →
      Int.ModEq 3 ((p ^ e : ℕ) : ℤ) (if s then 1 else -1) → IsPSLEps3 s p e ↥S →
        n = 2 ∧ (IsPSL 3 2 2 ↥S ∨ IsPSU 3 5 1 ↥S)

@[expose] def Insp4316OutLieOdd : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (S R K : Subgroup X) (n : ℕ) (x : X), Cfg4316 S R K n x →
    R ≤ S → ∀ p₀ : ℕ, p₀.Prime → p₀ ≠ 2 →
    (StatedClassicalModel ↥S .PSL 3 p₀ 1 ∨ StatedClassicalModel ↥S .PSU 3 p₀ 1) →
    ∀ x' ∈ Subgroup.zpowers x, ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ 2 ^ n - 1 → orderOf x' = p →
      x' ∉ S → n = 2 ∧ (IsPSL 3 2 2 ↥S ∨ IsPSU 3 5 1 ↥S)

@[expose] def Insp4316OutLieRank2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (S R K : Subgroup X) (n : ℕ) (x : X), Cfg4316 S R K n x →
    R ≤ S → (∃ f : ℕ,
      (2 ≤ f ∧ StatedClassicalModel ↥S .PSp 2 2 f) ∨
      (2 ≤ f ∧ ChevalleyExceptionalModel ↥S .G2 2 f) ∨
      (1 ≤ f ∧ ChevalleyExceptionalModel ↥S .trialityD4 2 f) ∨
      (Odd f ∧ 3 ≤ f ∧ ReeTitsModel ↥S .twistedF4 2 f)) →
    ∀ x' ∈ Subgroup.zpowers x, ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ 2 ^ n - 1 → orderOf x' = p →
      x' ∉ S → n = 2 ∧ (IsPSL 3 2 2 ↥S ∨ IsPSU 3 5 1 ↥S)

theorem insp4316L3eps_of (hOdd : Insp4316L3epsOdd) : Insp4316L3eps := by
  intro X _ _ S R K n x h hRS x' hx'z hx'o hx'S hL
  obtain ⟨s, q, hq, p, e, hp, he1, rfl, hm⟩ := hL
  by_cases hp2 : p = 2
  · subst hp2
    cases s
    · exfalso
      have hm' : StatedClassicalModel ↥S .PSU 3 2 e := hm
      obtain ⟨-, -, -, hne⟩ := hm'.1
      have he2 : 2 ≤ e := by
        by_contra hlt
        have : e = 1 := by omega
        subst this
        exact hne rfl
      exact h.toCfg.false_of_psu3_two hRS he2 hm'
    · have hm' : StatedClassicalModel ↥S .PSL 3 2 e := hm
      have he2 : 2 ≤ e := by
        by_contra hlt
        have : e = 1 := by omega
        subst this
        revert hq
        decide
      obtain ⟨hn, he⟩ := h.eq_two_of_psl3_two hRS he2 hm'
      subst he
      exact ⟨hn, Or.inl hm'⟩
  · exact hOdd X S R K n x h hRS x' hx'z hx'o hx'S s p e hp hp2 he1 hq hm

theorem insp4316OutLie_of
    (hO : Insp4316OutLieOdd) (hR2 : Insp4316OutLieRank2) : Insp4316OutLie := by
  intro X _ _ S R K n x h hRS hLie x' hx'z p hp hp2 hpn hx'o hx'S
  rcases hLie with ⟨p₀, hp₀, hp₀2, hm⟩ | ⟨f, ⟨-, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ |
      ⟨hf, hm⟩ | ⟨hf1, hf3, hm⟩ | ⟨hf1, hf3, hm⟩⟩
  · exact hO X S R K n x h hRS p₀ hp₀ hp₀2 hm x' hx'z p hp hp2 hpn hx'o hx'S
  · exact (h.toCfg.false_of_psl2 hRS hm).elim
  · by_cases hf2 : 2 ≤ f
    · obtain ⟨hn, he⟩ := h.eq_two_of_psl3_two hRS hf2 hm
      subst he
      exact ⟨hn, Or.inl hm⟩
    · exfalso
      have hf1 : f = 1 := by omega
      subst hf1
      have := h.normal
      have hdvd := dvd_card_outer_of_not_mem h.cent hx'S hp hx'o
      obtain ⟨hout, -⟩ :=
        CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
          (T := ↥S) (Or.inl rfl) (le_refl 3) Nat.prime_two le_rfl hm
      have h2 : CFSG.RankThree.OuterOrder.determinantParameter .PSL 3 (2 ^ 1) = 1 := by
        simp [CFSG.RankThree.OuterOrder.determinantParameter]
      rw [h2] at hout
      have := Nat.le_of_dvd (by norm_num) (hdvd.trans hout)
      have := hp.two_le
      omega
  · exact (h.toCfg.false_of_psu3_two hRS hf hm).elim
  · exact hR2 X S R K n x h hRS ⟨f, Or.inl ⟨hf, hm⟩⟩ x' hx'z p hp hp2 hpn hx'o hx'S
  · exact hR2 X S R K n x h hRS ⟨f, Or.inr (Or.inl ⟨hf, hm⟩)⟩ x' hx'z p hp hp2 hpn hx'o hx'S
  · exact hR2 X S R K n x h hRS ⟨f, Or.inr (Or.inr (Or.inl ⟨hf, hm⟩))⟩ x' hx'z p hp hp2 hpn
      hx'o hx'S
  · exact hR2 X S R K n x h hRS ⟨f, Or.inr (Or.inr (Or.inr ⟨hf1, hf3, hm⟩))⟩ x' hx'z p hp hp2
      hpn hx'o hx'S
  · exact (h.toCfg.false_of_isSz hm).elim

end CFSG.Quasithin.H13.KGInsp4316
