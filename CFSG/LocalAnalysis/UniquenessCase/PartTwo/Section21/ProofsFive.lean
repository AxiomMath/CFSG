module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsNineFifteen
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UC22S215KF7Use
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2115Two
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsFiveOrbit
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsFiveNonthin
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsFiveThin
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsFiveStrong
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsFiveOrbitEnd
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsFiveFinal
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214a
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21b
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G]

private theorem Ctx215.thin_data_of_inputs {D : Data G} {Ch : Choice2011 G}
    (e : Ctx215 D Ch) (h1930 : H1930 D) (hσ : UC6S846.SigmaStd D) (hU : KF7Use D)
    (hstep3 : 3 ≤ (conjSetOf D.M e.L).ncard → ∀ {n : ℕ},
      IsL2 (Bar2 e.L) n ∨ IsSz (Bar2 e.L) n → ∀ {s : ℕ}, Odd s → 1 < s → s ∣ n → False)
    (hKThin : KThinSimple) (hr3 : 3 ≤ orderOf e.a) :
    Subgroup.center (Bar2 e.L) = ⊥ ∧
      ((∃ k : ℕ, 1 ≤ k ∧ IsL2 (Bar2 e.L) (2 ^ k)) ∨
        (∃ q : ℕ, q.Prime ∧ 5 ≤ q ∧ IsL2Odd (Bar2 e.L) q) ∨ IsJ1 (Bar2 e.L)) ∧
      3 ∣ Nat.card (Bar2 e.L) := by
  have hcyc : ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ P : Sylow p (Bar2 e.L),
      IsCyclic ↥(P : Subgroup (Bar2 e.L)) :=
    fun p hp hp2 P => e.isCyclic_sylow h1930 hσ hU hp hp2 P
  have hZ := center_bar2_eq_bot_of_isCyclic_sylow e.hL hcyc
  have hshape := bar2_shape_of_isCyclic_sylow D e.hL hKThin hcyc
  have h3ncard : 3 ≤ (conjSetOf D.M e.L).ncard :=
    hr3.trans (Ctx215.le_ncard_conjSetOf e)
  have hshape' := exists_eq_two_pow_of_shape (X := Bar2 e.L)
    (fun n hn s hsOdd hs1 hsdvd => hstep3 h3ncard hn hsOdd hs1 hsdvd)
    hshape
  have hthree : (∃ n : ℕ, IsL2 (Bar2 e.L) n) ∨
      (∃ q : ℕ, q.Prime ∧ 5 ≤ q ∧ IsL2Odd (Bar2 e.L) q) ∨ IsJ1 (Bar2 e.L) := by
    rcases hshape' with ⟨k, -, hk⟩ | h | h
    · exact Or.inl ⟨2 ^ k, hk⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  exact ⟨hZ, hshape', three_dvd_card_of_shape hthree⟩

private theorem orderOf_ne_three_of_inputs {D : Data G} {Ch : Choice2011 G}
    (e : Ctx215 D Ch) (h1930 : H1930 D) (hσ : UC6S846.SigmaStd D) (hU : KF7Use D)
    (h82 : F08.R82 D) (h3 : 3 ∣ Nat.card (Bar2 e.L)) :
    orderOf e.a ≠ 3 := by
  have hcyc3 : ∀ P : Sylow 3 (Bar2 e.L), IsCyclic ↥(P : Subgroup (Bar2 e.L)) :=
    fun P => e.isCyclic_sylow h1930 hσ hU Nat.prime_three (by norm_num) P
  exact e.orderOf_ne_three (e.not_normalizer_le h1930) h82 hcyc3 h3

private theorem Ctx215.false_of_kf7Use {D : Data G} {Ch : Choice2011 G} (e : Ctx215 D Ch)
    (h1930 : H1930 D) (hσ : UC6S846.SigmaStd D) (hU : KF7Use D) (h82 : F08.R82 D)
    (hstep3 : 3 ≤ (conjSetOf D.M e.L).ncard → ∀ {n : ℕ},
      IsL2 (Bar2 e.L) n ∨ IsSz (Bar2 e.L) n → ∀ {s : ℕ}, Odd s → 1 < s → s ∣ n → False)
    (hKThin : KThinSimple) (hKOut : KOddOutInner) : False := by
  have hr3 : 3 ≤ orderOf e.a := by
    have h2 : 2 ≤ orderOf e.a := e.ha_prime.two_le
    have h2ne : orderOf e.a ≠ 2 := e.ha_ne_two
    omega
  obtain ⟨hZ, hshape, h3⟩ :=
    e.thin_data_of_inputs h1930 hσ hU hstep3 hKThin hr3
  have hrne3 := orderOf_ne_three_of_inputs e h1930 hσ hU h82 h3
  have hr5 : 5 ≤ orderOf e.a :=
    Nat.Prime.five_le_of_ne_two_of_ne_three e.ha_prime e.ha_ne_two hrne3
  have hNM := e.not_normalizer_le h1930
  have hrdvd := e.not_dvd_card_bar2 hσ hNM hZ hr5
  have hM3 := e.isStronglyPEmbedded_three hσ hZ hr5 h3
  have h3σ : 3 ∈ D.sig := by
    have h5 := e.five_le_pRank_of_dvd hZ hr5 Nat.prime_three (by norm_num) h3
    exact hσ.four_mem 3 Nat.prime_three (by norm_num) (by omega)
  have hodd := e.odd_n h1930 hM3
  have haT := e.a_mem_normalizer hodd
  have h3S : 3 ∣ Nat.card (Bar2 e.L ⧸ Subgroup.center (Bar2 e.L)) := by
    rw [hZ, Nat.card_congr (QuotientGroup.quotientBot (G := Bar2 e.L)).toEquiv]
    exact h3
  have hrank3 := e.pRank_three_le_one h1930 hU h3σ hM3 h3S
  have hconj := e.conjSetOf_eq hKOut hZ hshape h3 hrdvd hrank3
  exact e.false_of_conjSetOf_eq h1930 hM3 haT hconj hZ h3

theorem Ctx215.false_of_inputs {D : Data G} {Ch : Choice2011 G} (e : Ctx215 D Ch)
    (h1930 : H1930 D) (hσ : UC6S846.SigmaStd D) (h211 : S21_1 D Ch) (h72 : F07.R72 D)
    (h82 : F08.R82 D) (h899 : F08.R899 D) (htor : S21_15Torus D Ch)
    (hKF7 : KStrongEmbedded72) (hKThin : KThinSimple) (hKOut : KOddOutInner) : False :=
  e.false_of_kf7Use h1930 hσ (kf7Use_of_r72 h72 hKF7) h82
    (e.false_of_odd_dvd h1930 hσ h211 h899 htor) hKThin hKOut

private theorem Ctx215.false_of_odd_dvd_of_s21_15Two {D : Data G} {Ch : Choice2011 G}
    (e : Ctx215 D Ch) (h1930 : H1930 D) (h15 : S21_15Two D Ch)
    (h3 : 3 ≤ (conjSetOf D.M e.L).ncard) {n : ℕ}
    (hshape : IsL2 (Bar2 e.L) n ∨ IsSz (Bar2 e.L) n)
    {s : ℕ} (hsOdd : Odd s) (hs1 : 1 < s) (hsdvd : s ∣ n) : False := by
  have hne : conjClosure D.M e.L ≠ e.L := fun hcl => by
    have := uc22p2214_ncard_eq_one_of_eq hcl.symm
    omega
  have hpow : ¬ IsPowTwo n := by
    rintro ⟨k, rfl⟩
    have := Nat.Coprime.eq_one_of_dvd (hsOdd.coprime_two_right.pow_right k) hsdvd
    omega
  have h2 := h15 h1930 e.toCtx21 e.L e.hL n
    (hshape.elim (fun h => Or.inr ⟨h, hpow⟩) Or.inl) hne
  omega

private theorem s21_5_of_false (D : Data G) (Ch : Choice2011 G)
    (hF : ∀ e : Ctx215 D Ch, H1930 D → False) : S21_5 D Ch := by
  intro h1930 c L hL
  by_contra h
  obtain ⟨a, haB, haP, ha2, haN⟩ :=
    exists_prime_orderOf_not_mem_normalizer c.hB h
  let e : Ctx215 D Ch :=
    { toCtx21 := c, L := L, hL := hL, a := a, haB := haB, ha_prime := haP,
      ha_ne_two := ha2, ha_not_mem := haN }
  exact hF e h1930

theorem s21_5_of (D : Data G) (Ch : Choice2011 G) (hσ : UC6S846.SigmaStd D)
    (h211 : S21_1 D Ch) (h72 : F07.R72 D) (h82 : F08.R82 D) (h899 : F08.R899 D)
    (htor : S21_15Torus D Ch) (hKF7 : KStrongEmbedded72) (hKThin : KThinSimple)
    (hKOut : KOddOutInner) : S21_5 D Ch :=
  s21_5_of_false D Ch fun e h1930 =>
    e.false_of_inputs h1930 hσ h211 h72 h82 h899 htor hKF7 hKThin hKOut

theorem s21_5_of' (D : Data G) (Ch : Choice2011 G) (hσ : UC6S846.SigmaStd D)
    (hU : KF7Use D) (h82 : F08.R82 D) (h15 : S21_15Two D Ch) (hKThin : KThinSimple)
    (hKOut : KOddOutInner) : S21_5 D Ch :=
  s21_5_of_false D Ch fun e h1930 =>
    e.false_of_kf7Use h1930 hσ hU h82 (e.false_of_odd_dvd_of_s21_15Two h1930 h15) hKThin hKOut

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
