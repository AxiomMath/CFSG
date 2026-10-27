module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight99NormalFour
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight99SwapSpFour
public import CFSG.LocalAnalysis.UniquenessCase.UC7R76Four
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
public import CFSG.LocalAnalysis.UniquenessCase.UC6R77Three
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
public import CFSG.LocalAnalysis.UniquenessCase.UC22R82Four
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r899Three
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r899Odd
public import CFSG.LocalAnalysis.UniquenessCase.UC22R899C4Shape
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight99FourSz

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)

variable {G : Type} [Group G] [Finite G]


theorem r899_sp_of_orbit {D : Data G}
    (hSg : UC6S846.SigmaStd D) (hfour : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M)
    (h614 : UC6.R6_14 D) (h76 : F07.R76 D) (h82 : F08.R82 D)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hc3 : (conjSetOf D.M L).ncard = 3) {n : ℕ}
    (hLS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) {s r : ℕ} (hs : Odd s) (hsn : s ∣ n)
    (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1) : IsStronglyPEmbedded r D.M := by
  by_contra hnot
  have h76s : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p :=
    fun p hp hsp => F07.R76Sig_of_R76 D h76 p hp (D.sig_prime p hp).2 hsp
  have h77 : F07.R77E2 D := UC6.r77E2_of_conclusion76 D h76s
  have hres : ∀ p ∈ D.sig, p % 3 = 1 ∧ p ∣ n ∧ ¬ r ∣ 2 ^ (n / p) - 1 ∧
      ((IsL2 (Bar2 L) n ∧ p ∣ 2 ^ n + 1) ∨ (IsSz (Bar2 L) n ∧ p ∣ 2 ^ (2 * n) + 1)) := by
    intro p hp
    have hcong :=
      uc22r899_cong_of_ncard_three hSg hfour h77 h614 hL hc3 hLS hs hsn hr hrs hnot hp
    have hp3 : p % 3 = 1 := by
      by_contra h3
      rcases hcong with ⟨hL2, hpn⟩ | ⟨hSz, hpn⟩
      · exact hnot (uc22r899c4_sp_L2 hSg hfour h614 h76s hL hc3 hL2 hs hsn hr hrs hp h3 hpn)
      · exact hnot (uc22r899c4_sp_Sz hSg hfour h614 h76s hL hc3 hSz hs hsn hr hrs hp h3 hpn)
    have hp3' : p ≠ 3 := by
      rintro rfl
      norm_num at hp3
    have hpn : p ∣ n := by
      by_contra h
      exact hnot
        (uc22s21r899_sp_of_not_dvd hSg hfour h614 h76s hL hc3 hLS hs hsn hr hrs hp hp3' h)
    have hn : n = p * (n / p) := (Nat.mul_div_cancel' hpn).symm
    have hrm : ¬ r ∣ 2 ^ (n / p) - 1 := by
      intro hrm
      rcases hcong with ⟨hL2, hpn'⟩ | ⟨hSz, hpn'⟩
      · exact hnot (uc22s21r899_sp_of_odd_factor hSg hfour h614 h76s hL hc3 hL2 hs hsn hr hrs
          hp hp3' hn hpn' hrm)
      · exact hnot (uc22r899c3_sp_of_odd_factor_Sz hSg hfour h614 h76s hL hc3 hSz hs hsn hr hrs
          hp hn hpn' hrm)
    exact ⟨hp3, hpn, hrm, hcong⟩
  have hswap_sp : ¬ ∃ τ ∈ D.M, ∃ K ∈ conjSetOf D.M L, K.map (MulAut.conj τ).toMonoidHom = K ∧
      ∃ K' ∈ conjSetOf D.M L, K'.map (MulAut.conj τ).toMonoidHom ≠ K' := by
    intro hτ
    obtain ⟨p, hp⟩ := hSg.nonempty
    obtain ⟨hp3, -, -, hpn⟩ := hres p hp
    have hp3' : p ≠ 3 := by
      rintro rfl
      norm_num at hp3
    exact hnot (r899_sp_of_swap hSg hfour h614 h76s hL hc3 hs hsn hr hrs hp hp3' hpn hτ)
  rcases hLS with hL2 | hSz
  ·
    have h3 := r899_sp_three_of_isL2 h82 hL hc3 hL2
    have hOp := UC6.opRes_eq_of_stronglyEmbedded_uc6 D.standing.simple D.standing.nonab
      Nat.prime_three h3
    exact hswap_sp (r899_exists_swap_of_opRes_three hc3 hOp)
  ·
    obtain ⟨p, hp⟩ := hSg.nonempty
    obtain ⟨hp3, hpn, -, h4⟩ := hres p hp
    have hp2n : p ∣ 2 ^ (2 * n) + 1 := by
      rcases h4 with ⟨hL2, -⟩ | ⟨-, hp2n⟩
      · exact (uc22p22g_isSz_isL2_false hSz hL2).elim
      · exact hp2n
    exact hnot (sp_of_isSz_cyclic hSg hfour h614 h76 hL hc3 hSz hs hsn hr hrs hp hp3 hpn hp2n)

theorem r899_of_inputs {D : Data G} (hSg : UC6S846.SigmaStd D)
    (hfour : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M) (h614 : UC6.R6_14 D) (h76 : F07.R76 D)
    (h82 : F08.R82 D) : F08.R899 D := by
  intro L n s r hinj hL hshape hs hsn hr hrs halt
  have hr2 : r ≠ 2 := uc22ine229_ne_two hs hrs
  have h76s : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p :=
    fun p hp hsp => F07.R76Sig_of_R76 D h76 p hp (D.sig_prime p hp).2 hsp
  rcases halt with hrange | hnorm
  · have hc3 : (conjSetOf D.M (L 0)).ncard = 3 := by
      have he : conjSetOf D.M (L 0) = Set.range L := hrange.symm
      rw [he, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]
    exact r899_sp_of_orbit hSg hfour h614 h76 h82 (hL 0) hc3 (hshape 0).symm hs (hsn 0) hr
      hrs
  · exact r899_sp_of_normal hSg hfour h614 h76s
      (hL 0) (hL 1) (hinj.ne (by decide)) (hnorm 0) (hnorm 1) (hshape 0).symm (hshape 1).symm
      (hsn 0) (hsn 1) hr hr2 hrs

theorem r8_99_dataOfSetup4
    (hSE : PartOne.Section7.StronglyEmbeddedFive) (hSE3 : PartOne.Section7.StronglyEmbeddedThree)
    (hB : PartOne.Section7.BadNoStrongThree) (hS : Standing4 G)
    (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G) (hMS : S.InMSigma) (hPart : PartIAt S.M) :
    F08.R899 (UC6.dataOfSetup4 hS hU S) :=
  r899_of_inputs (UC6S846.sigmaStd_dataOfSetup4 hS hU S)
    ((dataExt_ofSetup4 hS hU S).four_le hS.rank) ((UC6.r6_14_dataOfSetup4_iff hS hU S).2 hPart.2.1)
    (UC6.r76_dataOfSetup4 hSE hSE3 hB hS hU S hMS hPart) (UC22.r82_dataOfSetup4 hS hU S hPart.2.2)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
