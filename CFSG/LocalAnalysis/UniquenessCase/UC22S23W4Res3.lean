module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8100Res3
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2115Two
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2115N
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214Sz
public import CFSG.Quasithin.Vol2.Ch11SecAKE8
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

variable {G : Type} [Group G] [Finite G]

theorem s21_15N_of_r8100Res3
    (D : Data G) (Ch : Choice2011 G) (h211 : S21_1 D Ch) (h15T : S21_15Two D Ch)
    (hSg : UC6S846.SigmaStd D) (he : 3 < CFSG.Open.evenRank G)
    (hfour : 3 < CFSG.Open.evenRank G → ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M)
    (h614 : UC6.R6_14 D)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p)
    (hres : R8100Res3 D) (h847 : F08.R847 D) (h869 : F08.R869NS5 D)
    (hGL : GL3Excl.GL3Excl) : S21_15N D Ch := by
  intro h1930 c L hL n hshape hne s hsOdd hsdvd r hr hrdvd p hp A hAcard hAL
  have hr2 : 2 ≤ r := hr.two_le
  have hs1 : 1 < s := by
    rcases Nat.lt_or_ge 1 s with h | h
    · exact h
    · have hs0 : s = 1 := by obtain ⟨k, hk⟩ := hsOdd; omega
      subst hs0
      exact absurd (Nat.le_of_dvd (by norm_num) hrdvd) (by omega)
  have hpow : ¬ IsPowTwo n := by
    rintro ⟨k, rfl⟩
    have := Nat.Coprime.eq_one_of_dvd (hsOdd.coprime_two_right.pow_right k) hsdvd
    omega
  have hLS : IsSz (Bar2 L) n ∨ (IsL2 (Bar2 L) n ∧ ¬ IsPowTwo n) :=
    hshape.elim (fun h => Or.inr ⟨h, hpow⟩) Or.inl
  have hk2 : (conjSetOf D.M L).ncard = 2 := h15T h1930 c L hL n hLS hne
  have hnotStrong : ¬ IsStronglyPEmbedded r D.M :=
    uc22r8100r3_not_sp h211 h1930 c hL hk2 hshape hsOdd hsdvd hr hrdvd
  rcases uc22s21r8100Res3_outcome h211 hSg hfour h76 h614 hres h1930 c he hL hk2 hLS hp with
    ⟨hL8, rfl⟩ | ⟨hSz5, rfl⟩
  · have hsig : D.sig = {3} := Set.eq_singleton_iff_unique_mem.2 ⟨hp, fun q hq => by
      rcases uc22s21r8100Res3_outcome h211 hSg hfour h76 h614 hres h1930 c he hL hk2 hLS hq with
        ⟨-, hq3⟩ | ⟨hSz, -⟩
      · exact hq3
      · exact (P2214S.false_of_isSz_of_isL2 hSz hL8).elim⟩
    have hn : n = 3 := by
      rcases hshape with hL2 | hSz
      · exact CFSG.Quasithin.Vol2.Ch11.SecA.C10KH.eq_of_isPSL_two_two
          (CFSG.Blueprint.LieModel.statedClassicalModel hL2 (by decide))
          (CFSG.Blueprint.LieModel.statedClassicalModel hL8 (by decide))
      · exact (P2214S.false_of_isSz_of_isL2 hSz hL8).elim
    subst hn
    have hs3 : s = 3 := ((Nat.dvd_prime Nat.prime_three).1 hsdvd).resolve_left (by omega)
    subst hs3
    have hr7 : r = 7 :=
      (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 (by simpa using hrdvd)
    have hAu := r8101U_gt_of_inputs h211 hSg hfour h614 h76 h847 h869 hGL h1930 c he L hL hk2
      A hAL (Or.inl ⟨hL8, hsig, hAcard.trans hr7⟩)
    exact ⟨⟨hnotStrong, hAu⟩, hk2, Or.inr (Or.inl ⟨hL8, rfl⟩)⟩
  · have hsig : D.sig = {5} := Set.eq_singleton_iff_unique_mem.2 ⟨hp, fun q hq => by
      rcases uc22s21r8100Res3_outcome h211 hSg hfour h76 h614 hres h1930 c he hL hk2 hLS hq with
        ⟨hL8, -⟩ | ⟨-, hq5⟩
      · exact (P2214S.false_of_isSz_of_isL2 hSz5 hL8).elim
      · exact hq5⟩
    have hn : n = 5 := by
      rcases hshape with hL2 | hSz
      · exact (P2214S.false_of_isSz_of_isL2 hSz5 hL2).elim
      · have h5 :=
          CFSG.LocalAnalysis.EvenBN.GMSK.factorization_two_card_of_lieModel_twistedB2 hSz5
        have hfn :=
          CFSG.LocalAnalysis.EvenBN.GMSK.factorization_two_card_of_lieModel_twistedB2 hSz
        omega
    subst hn
    have hs5 : s = 5 :=
      ((Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 hsdvd).resolve_left (by omega)
    subst hs5
    have hr31 : r = 31 :=
      (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 (by simpa using hrdvd)
    have hAu := r8101U_gt_of_inputs h211 hSg hfour h614 h76 h847 h869 hGL h1930 c he L hL hk2
      A hAL (Or.inr ⟨hSz5, hsig, hAcard.trans hr31⟩)
    exact ⟨⟨hnotStrong, hAu⟩, hk2, Or.inr (Or.inr ⟨hSz5, rfl⟩)⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
