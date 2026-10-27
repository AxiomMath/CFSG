module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3NoPairR
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3NB
import CFSG.LocalAnalysis.EvenBN.GMSK.U3Facts
import CFSG.LocalAnalysis.UniquenessCase.UC22S13xl
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3NA
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3NC
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rS2
import CFSG.LocalAnalysis.UniquenessCase.UC22U3Loss0
import CFSG.LocalAnalysis.UniquenessCase.UC6S898b
import CFSG.LocalAnalysis.UniquenessCase.UCKU3Key
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3Res
public import CFSG.LocalAnalysis.UniquenessCase.UC22Standing22

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem s21_22R3NoPair_of_s21_22R3NoPairR {D : Data G} {Ch : Choice2011 G} (st : Standing22 D)
    (hCen : UCK.U3Center) (h211 : S21_1 D Ch) (h846 : F08.R846 D) (h219 : S21_9Sig3 D Ch)
    (h217 : S21_17 D Ch) (h21U3 : S21_21U3 D Ch) (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n)
    (h : S21_22R3NoPairR D Ch) : S21_22R3NoPair D Ch := by
  intro h1930 c H₁ hH₁ H₂ hH₂ hL0 hfX hS1 hU3 hs he hno
  refine h h1930 c H₁ hH₁ H₂ hH₂ hL0 hfX hS1 hU3 hs he hno ?_
  by_contra hres
  have hnorm : ∀ L ∈ calC D.M, (L.subgroupOf D.M).Normal := fun L hL => by
    rcases h217 h1930 c L hL with h1 | ⟨h2, n, hn, hLS⟩ | ⟨h2, hJ, hcn, hcl, -, hA⟩
    · exact uc22p21j_normal_of_conjClosure_eq hL.1.le h1
    · exact absurd hLS (hno L hL h2 n hn)
    · exact absurd ⟨L, hL, Or.inr ⟨h2, hJ, hcn, hcl, hA⟩⟩ hres
  have hML : ∀ L ∈ calC D.M, D.M ≤ normalizer (L : Set G) := fun L hL =>
    (normal_subgroupOf_iff_le_normalizer hL.1.le).1 (hnorm L hL)
  have hsp : ∀ L ∈ calC D.M, ∀ p ∈ D.sig, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M :=
    fun L hL p hp => UC6S846.sp_of_mem_sig st.sigmaStd (UC6S846.not_solvable_of_mem_calC hL) hp
  have hsu3 : ∀ L ∈ calC D.M, ∀ n : ℕ, Odd n → ¬ IsSU3 (Bar2 L) n := by
    intro L hL n hn hX
    have hn2 := CFSG.LocalAnalysis.EvenBN.GMSK.two_le_of_lieModel_PSU3 hX.2
    by_cases h3n : 3 ∣ n
    · have hnp : ¬ IsPowTwo n := by
        rintro ⟨k, rfl⟩
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · norm_num at hn2
        · exact Nat.not_even_iff_odd.2 hn (Nat.even_pow.2 ⟨even_two, hk.ne'⟩)
      have h3σ := (h219 h1930 c L hL (hnorm L hL) n hX hnp he).2
      have h9 := UCK.nine_dvd_two_pow_add_one n hn h3n
      obtain ⟨Y, hTY, hYM, hsol, hdvd, -⟩ := uc22r3n_exists_solvable D.sylowM hL.1.le (hML L hL)
        hX Nat.prime_three ((by norm_num : (3 : ℕ) ∣ 9).trans h9) (Or.inr h9)
      exact uc22s21ru3b_not_dvd_card D Ch st h211 h1930 c hH₁ hH₂
        (fun X h1 h2 hF => hfX X h1 h2 (Or.inl hF)) h3σ (hsp L hL 3 h3σ) hTY hYM hsol hdvd
    · obtain ⟨q, hq, hq3, hqn⟩ := UC6S898.exists_prime_gt_three_dvd hn2 (by
        rintro rfl
        exact h3n (dvd_refl 3))
      have hZ : ¬ q ∣ Nat.card ↥(center (Bar2 L)) := fun hqZ =>
        absurd (Nat.le_of_dvd (by norm_num) (hqZ.trans (hCen (Bar2 L) n hX))) (by omega)
      obtain ⟨Y, hTY, hYM, hsol, hdvd, hcyc⟩ := uc22r3n_exists_solvable D.sylowM hL.1.le
        (hML L hL) hX hq hqn (Or.inl (by omega))
      exact uc22r3n_not_dvd_card_of_cyclic D Ch h211 h1930 c hH₁ hH₂
        (fun X h1 h2 hF => hfX X h1 h2 (Or.inl hF)) hq (by omega)
        (h846 L hL n hX q hq hq3 hqn) hTY hYM hsol (hcyc hZ) hdvd
  let c₀ : Ctx21 D Ch := { c with B := c.B0, hB := c.hB0, hle := le_rfl }
  have hH0 : Hyp2120 D c₀ := uc22s21rs2_hyp2120_of c₀ hS1 (fun L hL => ⟨hnorm L hL,
    fun ⟨n, hn, h4⟩ => h4.elim (fun h4 => hres ⟨L, hL, Or.inl ⟨hnorm L hL, n, hn, h4⟩⟩)
      (hsu3 L hL n hn)⟩) hU3
  have hB0 : c₀.B ≠ ⊥ := uc22s13xl_B0_ne_bot c (by have := hn3 h1930 c; omega)
  obtain ⟨p, hp⟩ := st.dataExt.sig_nonempty
  obtain ⟨L, hL, m, hm, hpm, hU⟩ := h21U3 h1930 c₀ hB0 hH0 hU3 p hp
  have hm2 := CFSG.LocalAnalysis.EvenBN.GMSK.two_le_of_lieModel_PSU3 hU
  have hp3 : p ≠ 3 := by
    rintro rfl
    obtain ⟨k, rfl⟩ := hm
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · norm_num at hm2
    · exact UC6S898.not_three_dvd_two_pow_add_one_of_even (Nat.even_pow.2 ⟨even_two, hk.ne'⟩)
        hpm
  obtain ⟨Y, hTY, hYM, hsol, hdvd, -⟩ := uc22r3n_exists_solvable D.sylowM hL.1.le (hML L hL)
    (U3Loss.isSU3_of_isU3 hU).1 (D.sig_prime p hp).1 hpm (Or.inl hp3)
  exact uc22s21ru3b_not_dvd_card D Ch st h211 h1930 c hH₁ hH₂
    (fun X h1 h2 hF => hfX X h1 h2 (Or.inl hF)) hp (hsp L hL p hp) hTY hYM hsol hdvd

end CFSG.LocalAnalysis.UniquenessCase.UC22
