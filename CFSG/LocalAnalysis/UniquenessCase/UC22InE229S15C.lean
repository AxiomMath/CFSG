module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229N
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07Use
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229CongD
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Diag2
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229NSE
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)

variable {G : Type} [Group G] [Finite G]

theorem uc22ine229_exists_odd {X : Type} [Group X] {n : ℕ}
    (hX : IsSz X n ∨ (IsL2 X n ∧ ¬ IsPowTwo n)) : ∃ s : ℕ, Odd s ∧ 1 < s ∧ s ∣ n := by
  rcases hX with hS | ⟨hL2, hpow⟩
  · have h3 := CFSG.LocalAnalysis.EvenBN.GMSK.three_le_of_lieModel_twistedB2 hS
    exact ⟨n, CFSG.LocalAnalysis.EvenBN.GMSK.odd_of_lieModel_twistedB2 hS, by omega, dvd_rfl⟩
  · have hn0 : n ≠ 0 := by
      have := (CFSG.Blueprint.LieModel.admissible hL2).2.1
      omega
    obtain ⟨k, m, hmo, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn0
    refine ⟨m, hmo, ?_, Dvd.intro_left _ rfl⟩
    by_contra h1
    have hm1 : m = 1 := by have := hmo.pos; omega
    exact hpow ⟨k, by rw [hm1, mul_one]⟩

theorem s21_15C_of {D : Data G} {Ch : Choice2011 G}
    (h211 : S21_1 D Ch) (hSg : UC6S846.SigmaStd D) (h77 : F07.R77E2 D) (h614 : UC6.R6_14 D) :
    S21_15C D Ch := by
  intro h1930 c L hL hc2 n hLS p hp
  obtain ⟨s, hs, hs1, hsn⟩ := uc22ine229_exists_odd hLS
  have hs3 : 3 ≤ s := by obtain ⟨j, rfl⟩ := hs; omega
  obtain ⟨r, hr, hrs⟩ := Nat.exists_prime_and_dvd (n := 2 ^ s - 1) (by
    have : 2 ^ 3 ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs3
    omega)
  have hr2 := uc22ine229_ne_two hs hrs
  obtain ⟨x, -, hxo, hxT⟩ : ∃ x ∈ conjClosure D.M L, orderOf x = r ∧
      x ∈ normalizer (D.T : Set G) := by
    rcases hLS with hS | ⟨hL2, -⟩
    · exact uc22ine229_exists_mem_conjClosure_normalizer_of_isSz D.sylowM hL hc2.le hS hs hsn hr
        hrs
    · exact uc22ine229_exists_mem_conjClosure_normalizer_of_isL2 D.sylowM hL hc2.le hL2 hs hsn hr
        hrs
  exact uc22ine229_cong_of_ncard_two hSg h77 h614 hL hc2 (hLS.elim Or.inr fun h => Or.inl h.1) hr
    hr2 (hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn))
    (uc22ine229_not_sp_of_mem_normalizer h211 h1930 c hr hr2 hxT hxo) hp

theorem s21_15C_dataOfSetup4 {Ch : Choice2011 G} (hS : Standing4 G)
    (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G) (hPart : PartIAt S.M)
    (h211 : S21_1 (UC6.dataOfSetup4 hS hU S) Ch) (h77 : F07.R77E2 (UC6.dataOfSetup4 hS hU S)) :
    S21_15C (UC6.dataOfSetup4 hS hU S) Ch :=
  s21_15C_of h211 (UC6S846.sigmaStd_dataOfSetup4 hS hU S) h77
    ((UC6.r6_14_dataOfSetup4_iff hS hU S).2 hPart.2.1)

end CFSG.LocalAnalysis.UniquenessCase.UC22
