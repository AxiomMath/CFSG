module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsB
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20p
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20v

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Open CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

private theorem lieModel_bar2_of_barInf_native (hN : uc22p20rNativeGriess) {M L : Subgroup G}
    (hL : L ∈ calC M) {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m n : ℕ}
    (hM : LieModel (BarInf L) t m 2 n) (hn : 1 ≤ n)
    (htype : (t = .PSU ∧ m = 4) ∨ (t = .PSp ∧ m = 2) ∨ (t = .G2 ∧ m = 0) ∨
      (t = .trialityD4 ∧ m = 0) ∨ (t = .twistedF4 ∧ m = 0) ∨ (t = .Tits ∧ m = 0)) :
    LieModel (Bar2 L) t m 2 n := by
  have hq : CFSG.Open.IsQuasisimple (Bar2 L) := hL.2.2
  obtain ⟨e₀⟩ := uc22p21k_barInf_equiv_of_calC hL
  have hM₀ : LieModel (Bar2 L ⧸ Subgroup.center (Bar2 L)) t m 2 n :=
    LieModel.of_mulEquiv e₀ hM
  have hodd : Odd (Nat.card (Subgroup.center (Bar2 L))) := by
    simpa [Bar2] using uc22p20p_odd_center_bar2 ↥L
  have hev : Even (2 ^ n) := Nat.even_pow.2 ⟨even_two, by omega⟩
  have hsub : Odd (2 ^ n - 1) := Nat.Even.sub_odd Nat.one_le_two_pow hev odd_one
  have hadd : Odd (2 ^ n + 1) := hev.add_one
  have hg : CFSG.Blueprint.Multiplier.genericOrders t m 2 n = (1, 1) := by
    rcases htype with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · change (Nat.gcd 4 (2 ^ n + 1), 1) = (1, 1)
      rw [(Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 hadd) : Nat.Coprime (2 ^ 2) _)]
    · change (Nat.gcd 2 (2 ^ n - 1), 1) = (1, 1)
      rw [Nat.coprime_two_left.2 hsub]
    all_goals rfl
  have hc := uc22p20v_center_eq_bot hN hq hodd hM₀ hg
  obtain ⟨e₁⟩ := uc22p21k_barInf_equiv_of_center_bot hq hc
  exact LieModel.of_mulEquiv e₁ hM

theorem seventeen_fifty (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V)
    (h17_31 : R17_31At D V₀ V) (h17_32 : R17_32At D V₀ V)
    (h17_43 : R17_43At D V₀ V) (h17_46 : R17_46At D V₀ V)
    (h17_47 : R17_47At D V₀ V) (h17_48 : R17_48At D V₀ V)
    (h17_49 : R17_49At D V₀ V) (hN : uc22p20rNativeGriess) :
    R17_50At D V₀ V := by
  intro L X p n l C Dc Gamma hctx
  have hq : 2 < 2 ^ n := h17_43 L X p n l C Dc Gamma hctx
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp at hq
    · exact h
  have hl : l = 2 := h17_46 L X p n l C Dc Gamma hctx
  have hLX : L = X := h17_49 L X p n l C Dc Gamma hctx
  obtain ⟨t, m, hadm, hM, hrank⟩ := hctx.rank
  rw [hl] at hrank
  have hcases :
      (t = .PSL ∧ m = 3) ∨ (t = .PSU ∧ (m = 4 ∨ m = 5)) ∨
      (t = .PSp ∧ m = 2) ∨ (t = .G2 ∧ m = 0) ∨ (t = .trialityD4 ∧ m = 0) ∨
      (t = .twistedF4 ∧ m = 0) ∨ (t = .Tits ∧ m = 0) := by
    rcases t <;> simp [CS17LieRank, StatedLieAdmissible] at hadm hrank ⊢ <;> omega
  subst hLX
  refine ⟨?_, hq⟩
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, hm | hm⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact absurd hM (h17_47 L L p n l C Dc Gamma hctx)
  · subst hm
    have hM' : LieModel (Bar2 L) .PSU 4 2 n :=
      lieModel_bar2_of_barInf_native hN hctx.mem_calC hM hn (Or.inl ⟨rfl, rfl⟩)
    exact Or.inl (by simpa [IsU4] using hM')
  · subst hm
    exact absurd hM (h17_48 L L p n l C Dc Gamma hctx)
  · have hM' : LieModel (Bar2 L) .PSp 2 2 n :=
      lieModel_bar2_of_barInf_native hN hctx.mem_calC hM hn (Or.inr (Or.inl ⟨rfl, rfl⟩))
    exact Or.inr (Or.inl (by simpa [IsSp4] using hM'))
  · have hM' : LieModel (Bar2 L) .G2 0 2 n :=
      lieModel_bar2_of_barInf_native hN hctx.mem_calC hM hn
        (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    exact Or.inr (Or.inr (by simpa [IsG2] using hM'))
  · have hM' : LieModel (Bar2 L) .trialityD4 0 2 n :=
      lieModel_bar2_of_barInf_native hN hctx.mem_calC hM hn
        (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
    exact absurd hM' (h17_32 L hctx.mem_calC n)
  · have hM' : LieModel (Bar2 L) .twistedF4 0 2 n :=
      lieModel_bar2_of_barInf_native hN hctx.mem_calC hM hn
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
    obtain ⟨-, hree⟩ := LieModel.reeTitsModel hM' (t := .twistedF4) (n := 0) (p := 2) (f := n)
      (by decide)
    exact absurd hree (by simpa [CFSG.Quasithin.Is2F4] using (h17_31 L hctx.mem_calC).1 n)
  · have hM' : LieModel (Bar2 L) .Tits 0 2 n :=
      lieModel_bar2_of_barInf_native hN hctx.mem_calC hM hn
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))
    have hn1 : n = 1 := by
      rcases hadm with ⟨-, -, h⟩
      exact h.2.2
    rw [hn1] at hM'
    exact absurd hM' (h17_31 L hctx.mem_calC).2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
