module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.AlternatingNaturalPrimeFixer
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalOneS1
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalOneCardinality
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalOneSection15
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeTwoLn
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactAutAlt
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeSection
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeTwoCommon

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s16nt_concl163F_of_natural_alt_ten_eleven
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    {n : ℕ} (hn10 : 10 ≤ n) (hn11 : n ≤ 11)
    (hA : UC22.IsAlt ↥(lBar V₀ V hV L) n)
    (hN : AlternatingNatural (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) n) :
    Concl163F D V₀ V hV L := by
  have hcases : n = 10 ∨ n = 11 := by omega
  have hs : s15 D.M V₀ V hV L = 1 :=
    s16nt_s15_eq_one_of_alt_nine_eleven c hcomp (by omega) hn11 hA
  obtain ⟨-, -, -, hmap, -⟩ := s168e3_section_kappa_data
    (D := D) (V₀ := V₀) (V := V) (L := L) (hV := hV) c
  have hNstar := s168e3_realizes_map_of_kappa
    (D := D) (V₀ := V₀) (V := V) (L := L) (hV := hV) c
    (I := wTil V₀ V hV L) le_rfl hN
  rw [hmap] at hNstar
  have hperf : s15KNatPerf ↥(lBar V₀ V hV L)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) :=
    Or.inr (Or.inr (Or.inr (Or.inr ⟨n, by omega, hA, hNstar⟩)))
  have hEmbedCard : Nat.card ↥(Mbar D.M V₀ V hV) ∣
      Nat.card (MulAut ↥(lBar V₀ V hV L)) :=
    s168e3_card_mbar_dvd_card_mulAut_of_natural c hs hperf
  have hcardB : Nat.card ↥(lBar V₀ V hV L) = n.factorial / 2 :=
    s15k_six_alt_card hA (by omega)
  have hA' := hA
  obtain ⟨eA⟩ := hA'
  have hcardAut : Nat.card (MulAut ↥(lBar V₀ V hV L)) = n.factorial := by
    calc Nat.card (MulAut ↥(lBar V₀ V hV L)) =
          Nat.card (MulAut (alternatingGroup (Fin n))) :=
          Nat.card_congr (MulAut.congr eA).toEquiv
      _ = n.factorial :=
          CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.card_mulAut_alternatingGroup_eq_factorial
            n (by omega) (by omega)
  have hMfac : Nat.card ↥(Mbar D.M V₀ V hV) ∣ n.factorial := by
    rwa [hcardAut] at hEmbedCard
  have hsig : D.sig ⊆ ({3, 5} : Set ℕ) := by
    intro p hp
    obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
    have hpM : p ^ 2 ∣ Nat.card ↥(Mbar D.M V₀ V hV) := by
      have h := s168e3_two_pow_dvd_card c hp
      rwa [c23_card_mbar_v1Sub_eq D c.std.h1217 c.setting.hyp151 hV] at h
    change p = 3 ∨ p = 5
    by_cases hp3 : p = 3
    · exact Or.inl hp3
    · have hp5 : 5 ≤ p := by
        by_contra h
        have hp2le : 2 ≤ p := hpp.two_le
        have hle : p ≤ 4 := by omega
        have hp4 : p = 2 ∨ p = 3 ∨ p = 4 := by omega
        rcases hp4 with rfl | rfl | rfl
        · exact hp2 rfl
        · exact hp3 rfl
        · norm_num at hpp
      exact Or.inr (CFSG.RankThree.PartOne.CTP.Alt.prime_sq_dvd_factorial
        hpp hp5 (by omega) (hpM.trans hMfac)).1
  have hcube : ¬ 5 ^ 3 ∣ Nat.card ↥(Mbar D.M V₀ V hV) := by
    intro h
    have hdvd : 5 ^ 3 ∣ n.factorial := h.trans hMfac
    rcases hcases with rfl | rfl <;> norm_num at hdvd
  have hdiv5 : 5 ∣ Nat.card ↥(lBar V₀ V hV L) := by
    rw [hcardB]
    rcases hcases with rfl | rfl <;> norm_num
  have htop : wStar D.M V₀ V hV L = ⊤ :=
    s15_Three_wStar_eq_top D c.std.h1217 c.setting.hyp151 hV c.ne hs
  have hNtop : AlternatingNatural (lStar D.M V₀ V hV L)
      (⊤ : Subgroup (vStar D.M V₀ V hV L)) ⊥ n := by
    change (FFModel.altDn n).Realizes (lStar D.M V₀ V hV L)
      (⊤ : Subgroup (vStar D.M V₀ V hV L)) ⊥
    simpa only [htop] using hNstar
  have hfixStar : ∀ x : vStar D.M V₀ V hV L, x ≠ 1 →
      ∃ b ∈ lStar D.M V₀ V hV L, orderOf b = 5 ∧ b x = x :=
    fun x _ => exists_prime_order_fixer_of_alternatingNatural
      Nat.prime_five (by decide : Odd 5) (by omega) hNtop x
  have hfixTil : ∀ x : Vtil V₀ V hV, x ≠ 1 →
      ∃ b ∈ Mbar D.M V₀ V hV, orderOf b = 5 ∧ b x = x :=
    s168e3_pointFix_of_star c hs Nat.prime_five (by norm_num) hdiv5 hfixStar
  have hKernel : S168e3Kernel (Mbar D.M V₀ V hV) 5 :=
    s168e3_kernel_of_cube Nat.prime_five (Mbar D.M V₀ V hV) hcube hfixTil
  have h5not : 5 ∉ D.sig := fun h5 =>
    s168e3_false_of_kernel c Nat.prime_five h5 hKernel
  obtain ⟨p, hp⟩ := c.std.hx.sig_nonempty
  have h3 : 3 ∈ D.sig := by
    rcases hsig hp with hp3 | hp5
    · exact hp3 ▸ hp
    · exact absurd (hp5 ▸ hp) h5not
  have hnot : ¬ s15ExcList ↥(lBar V₀ V hV L) := by
    intro hexc
    have hle := s15ExcList_card_le hexc
    rw [hcardB] at hle
    rcases hcases with rfl | rfl <;> norm_num at hle
  exact s168e3_concl163F_of_natural_perfect c hcomp hs hperf hnot h3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
