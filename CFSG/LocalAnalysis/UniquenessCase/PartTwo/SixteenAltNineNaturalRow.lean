module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalOneS1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalOneSection15
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeSection
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKOuterSix
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactAutAlt
public import CFSG.GroupTheory.PRankBound

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private lemma not_dvd_sq_362880 {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) : ¬ p ^ 2 ∣ 362880 := by
  intro h
  have hpN : p ∣ 362880 := (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans h
  have hfac : 362880 = 2 ^ 7 * (3 ^ 4 * (5 * 7)) := by norm_num
  rw [hfac] at hpN
  rcases hp.dvd_mul.mp hpN with h2 | hrest
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))
  rcases hp.dvd_mul.mp hrest with h3 | hrest
  · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h3))
  rcases hp.dvd_mul.mp hrest with h5 | h7
  · have hp5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h5
    rw [hp5] at h
    norm_num at h
  · have hp7 : p = 7 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h7
    rw [hp7] at h
    norm_num at h

theorem s16nt_concl163F_of_natural_alt_nine
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hA : UC22.IsAlt ↥(lBar V₀ V hV L) 9)
    (hN : AlternatingNatural (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 9) :
    Concl163F D V₀ V hV L := by
  have hs : s15 D.M V₀ V hV L = 1 :=
    s16nt_s15_eq_one_of_alt_nine_eleven c hcomp (le_refl 9) (by norm_num) hA
  obtain ⟨-, -, -, hmap, -⟩ := s168e3_section_kappa_data (D := D) (V₀ := V₀) (V := V)
    (L := L) (hV := hV) c
  have hNStar := s168e3_realizes_map_of_kappa (D := D) (V₀ := V₀) (V := V) (L := L)
    (hV := hV) c (I := wTil V₀ V hV L) le_rfl hN
  rw [hmap] at hNStar
  have hperf : s15KNatPerf ↥(lBar V₀ V hV L)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) :=
    Or.inr (Or.inr (Or.inr (Or.inr ⟨9, by norm_num, hA, hNStar⟩)))
  have hcardB : Nat.card ↥(lBar V₀ V hV L) = 181440 := by
    rw [s15k_six_alt_card (n := 9) hA (by norm_num)]
    norm_num
  have hA' := hA
  obtain ⟨eA⟩ := hA'
  have hcardAut : Nat.card (MulAut ↥(lBar V₀ V hV L)) = 362880 := by
    calc Nat.card (MulAut ↥(lBar V₀ V hV L)) =
          Nat.card (MulAut (alternatingGroup (Fin 9))) :=
          Nat.card_congr (MulAut.congr eA).toEquiv
      _ = Nat.factorial 9 :=
          CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.card_mulAut_alternatingGroup_eq_factorial
            9 (by norm_num) (by norm_num)
      _ = 362880 := by norm_num
  have hAut : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 →
      CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥(lBar V₀ V hV L))) ≤ 1 := by
    intro p hp hp2 hp3
    refine CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ (H := ⊤) (k := 1) hp ?_
    rw [Subgroup.card_top]
    intro h
    exact not_dvd_sq_362880 hp hp2 hp3 (hcardAut ▸ h)
  have h3 : 3 ∈ D.sig :=
    s168e3_three_mem_sig_of_natural_aut_rank c hs hperf hAut
  have hnot : ¬ s15ExcList ↥(lBar V₀ V hV L) := by
    intro h
    have hle := s15ExcList_card_le h
    rw [hcardB] at hle
    norm_num at hle
  exact s168e3_concl163F_of_natural_perfect c hcomp hs hperf hnot h3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
