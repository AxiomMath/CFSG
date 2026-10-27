module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R899C4Res
import CFSG.LocalAnalysis.UniquenessCase.UC22R899C5Out
import CFSG.LocalAnalysis.UniquenessCase.UC22R899C5In
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsNine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightPrelim

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

variable {G : Type} [Group G] [Finite G]

theorem r899C4_of_sig_normalizer {D : Data G}
    (hNT : ∀ p ∈ D.sig, ∀ x ∈ normalizer (D.T : Set G), orderOf x ≠ p)
    (hfour : 3 < evenRank G → ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M) (h614 : UC6.R6_14 D)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p) : R899C4 D := by
  intro he hSg L n hL _ hc3 hnot hopen
  obtain ⟨p, hp⟩ := hSg.nonempty
  obtain ⟨hL2, ⟨k, hn, -⟩, hp1⟩ := hopen p hp
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hp3 : p ≠ 3 := by
    rintro rfl
    norm_num at hp1
  have hpo : Odd p := hpp.odd_of_ne_two hp2
  have hsn : p ∣ n := Dvd.intro_left (2 ^ k) hn.symm
  obtain ⟨r, hr, -, hrp⟩ := uc22r899c_exists_prime hpo hpp.one_lt
  by_cases hinn : ∀ K ∈ conjSetOf D.M L, ∀ a ∈ D.M, ∀ haK : a ∈ normalizer (K : Set G),
      a ^ p = 1 → UC6S846.rhoL K ⟨a, haK⟩ ∈ (MulAut.conj : Bar2 K →* MulAut (Bar2 K)).range
  ·
    exact hnot p r hpo hsn hr hrp
      (uc22r899c5_sp_of_inner hSg (hfour he) h614 h76 hL hc3 hL2 hpo hsn hr hrp hp hp3 hinn)
  ·
    push Not at hinn
    obtain ⟨K, hK, a, haM, haK, hap, hout⟩ := hinn
    obtain ⟨x, hxT, hxo⟩ := uc22r899c5_exists_mem_normalizer_T (by rw [hc3]; decide) hK
      (uc22s21r899_isL2_of_mem hK hL2) hpp hp2 haM haK hap hout
    exact hNT p hp x hxT hxo

theorem s21_15Two_four_certificate113 (D : Data G)
    (Ch : Choice2011 G) (h211 : S21_1 D Ch) (hSg : UC6S846.SigmaStd D) (he : 3 < evenRank G)
    (hfour : 3 < evenRank G → ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M) (h77 : F07.R77E2 D)
    (h614 : UC6.R6_14 D) (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p) :
    S21_15Two D Ch := by
  intro h1930 c L hL n hLS hne
  have hNT : ∀ p ∈ D.sig, ∀ x ∈ normalizer (D.T : Set G), orderOf x ≠ p := by
    intro p hp x hxT hxo
    obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
    have hcard : Nat.card (zpowers x) = p := by rw [Nat.card_zpowers, hxo]
    have hXN : zpowers x ≤ normalizer (D.T : Set G) := zpowers_le.2 hxT
    have hXM : zpowers x ≤ D.M := hXN.trans D.normalizer_le
    have hbot : zpowers x ≠ ⊥ := fun h => by
      rw [h, Subgroup.card_bot] at hcard
      exact hpp.one_lt.ne hcard
    have hXp : IsPGroup p ↥(zpowers x) := IsPGroup.of_card (n := 1) (by rw [pow_one, hcard])
    exact not_mem_uniqueSet_of_le_normalizer D Ch h211 h1930 c (hcard ▸ hpp)
      (hcard ▸ hpp.odd_of_ne_two hp2) hXM hXN (mem_uniqueSet_of_isStronglyPEmbedded hpp
        (UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL) hp) hXM hbot hXp)
  exact s21_15Two_of_r899C4_certificate113 D Ch h211 hSg he hfour h77 h614 h76
    (r899C4_of_sig_normalizer hNT hfour h614 h76) h1930 c L hL n hLS hne

end CFSG.LocalAnalysis.UniquenessCase.UC22
