module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCFourteenEight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.R920Slices
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtySixShape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtySixAlt3
public import CFSG.LocalAnalysis.UniquenessCase.UCFront78Nar
public import CFSG.Quasithin.EmptyFaithful.S146zQArith

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

theorem seventeen_sixtysix_one
    (D : Data G) {V₀ V : Subgroup G} (h869 : F08.R869 D) (h3 : R17_3At D V₀ V)
    (h8107 : F08.R8107 D)
    (h920 : R920L2E D) (h148 : Inputs1719.R14_8 D)
    (h42 : R17_42At D V₀ V) (h641 : R17_64_1At D V₀ V)
    (h642 : R17_64_2At D V₀ V) (h643 : R17_64_3At D V₀ V) :
    R17_66_1At D V₀ V := by
  intro p hp L hL X hXeq hX0
  by_cases hU : UniqueMax D.M L
  · exact Or.inl hU
  · have hthin : F08.Thin8 L := by
      by_contra hnt
      exact hU (CFSG.LocalAnalysis.UniquenessCase.UC22.F08.R869M_of_R869 D h869 L
        (Or.inl hL.1) hnt)
    have hN : ∀ A : Subgroup G, A ≤ L → (Nat.card A).Prime → Nat.card A ≠ 2 →
        normalizer (A : Set G) ≤ D.M :=
      fun A hAL hAp hA2 => h3 L hL.1 hthin A ⟨Nat.card A, hAp, hA2, rfl, hAL⟩
    by_cases hLX : L = X
    ·
      obtain ⟨m, hHinf, hm, hpow, hL2m⟩ :=
        exists_p1642_isL2_of_self h42 h641 h642 h643 hp hL (by rw [hLX]; exact hX0) hthin
      obtain ⟨D₃, hD₃L, hD₃card, hD₃U⟩ :=
        exists_D3_of_self h8107 hL.1 hHinf hm hpow hL2m
      have hm2 : 2 ≤ m := uc22p20g_two_le_of_isL2 hL2m
      have heven : Even m := by
        obtain ⟨k, hk⟩ := hpow
        cases k with
        | zero =>
          rw [hk] at hm2
          norm_num at hm2
        | succ k =>
          exact ⟨2 ^ k, by rw [hk, pow_succ]; ring⟩
      rcases h920 L D₃ m hL.1 hD₃L hD₃card hD₃U hL2m hN ⟨p, hp, hL.2.2⟩ (Or.inl heven) with
          h | h
      · exact Or.inl h
      · exact Or.inr h
    ·
      have hne' : conjClosure D.M L ≠ L := by
        intro h
        exact hLX (hXeq.trans h).symm
      obtain ⟨n, x, hxM, hXsup, -, hshape, hmore⟩ :=
        p42_alt2_of_ne h42 hp hL.1 hne'
      rcases hshape with ⟨hL2n, hcong⟩ | ⟨hSzn, -⟩
      ·
        let L' : Subgroup G := CFSG.Quasithin.conjSubgroup L x
        have hXsupX : X = L ⊔ L' := hXeq.trans hXsup
        obtain ⟨hL'calM, hL'ne⟩ := conjSubgroup_mem_calC_and_ne hL.1 hxM hXsup hne'
        have hL2L' : IsL2 (Bar2 L') n := by
          obtain ⟨e⟩ := uc22p20d_bar2_conj x⁻¹ L
          exact LieModel.of_mulEquiv e hL2n
        obtain ⟨D₃, hD₃L, hD₃card, hD₃U⟩ :=
          exists_D3_of_p42 h8107 hL.1 hxM hXsup hne' hL2n
        have hcond : Even n ∨ ((∃ A : Subgroup G,
            A ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M ∧ A ≤ L ∧
            (Nat.card A).Prime ∧ Nat.card A ∣ 2 ^ n - 1) ∧ ∃ p ∈ D.sig, p ∣ 2 ^ n + 1) := by
          by_cases hn : Even n
          · exact Or.inl hn
          · right
            have hnodd : Odd n := Nat.not_even_iff_odd.mp hn
            have hn3 : 3 ≤ n := by
              obtain ⟨k, rfl⟩ := hnodd
              have hn2 := uc22p20g_two_le_of_isL2 hL2n
              omega
            obtain ⟨r, hr, -, hrdvd⟩ :=
              CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22c_exists_prime_ge_five hn3
            have hr7 : 7 ≤ r :=
              CFSG.Quasithin.prime_dvd_two_pow_sub_one_ge_seven hnodd (by omega) hr hrdvd
            have hr5 : 5 < r := by omega
            obtain ⟨A, hAL, hAcard, hAU⟩ :=
              exists_mem_uniqueSet_of_isL2_ne h3 hL.1 hXeq hXsupX hL'calM hL'ne hthin
                hL2n hL2L' (by rwa [hXeq]) hr hr5 hrdvd
            exact ⟨⟨A, hAU, hAL, hAcard ▸ hr, hAcard ▸ hrdvd⟩, p, hp,
              uc22p22r_dvd_succ (n := n) hcong⟩
        rcases h920 L D₃ n hL.1 hD₃L hD₃card hD₃U hL2n hN ⟨p, hp, hL.2.2⟩ hcond with h | h
        · exact Or.inl h
        · exact Or.inr h
      ·
        have hcard : (conjSetOf D.M L).ncard = 2 :=
          ncard_eq_two_of_p42 hL.1 hxM hXsup hne'
        have heM : eM D.M ≤ 3 := (eM_le_evenRank D).trans (le_of_eq hmore.1)
        exact Or.inl (h148 L hL.1 hcard ⟨n, hSzn⟩ heM)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
