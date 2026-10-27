module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R8100PairTransfer
public import CFSG.LocalAnalysis.UniquenessCase.UC7R76Four
public import CFSG.LocalAnalysis.UniquenessCase.UC22R8100R
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight99NormalFour
import CFSG.LocalAnalysis.UniquenessCase.UC22R8100Dihedral
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.UniquenessCase.UC22P20g
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Facts13
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846g

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem r8100_core {D : Data G}
    (hSg : UC6S846.SigmaStd D) (hfour : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M)
    (h614 : UC6.R6_14 D) (h76 : F07.R76 D) {L : Fin 2 → Subgroup G} {n : Fin 2 → ℕ} {r p : ℕ}
    {A X : Subgroup G} (hH : F08.Hyp8100 D L n r p A X) :
    IsStronglyPEmbedded r D.M ∨
      (({L 0, L 1} : Set (Subgroup G)) =
          {N | ∃ m ∈ D.M, N = (L 0).map (MulAut.conj m).toMonoidHom} ∧ n 0 = p ∧
        ((IsL2 (Bar2 (L 0)) 3 ∧ p = 3 ∧ r = 7) ∨ (IsSz (Bar2 (L 0)) 5 ∧ p = 5 ∧ r = 31)) ∧
        ¬ IsStronglyPEmbedded r D.M ∧
        ∃ φ : ↥D.M →* DihedralGroup p, Function.Surjective φ ∧
          φ.ker = (X ⊔ F08.CentOverO2 D.M X).subgroupOf D.M) := by
  have hperm := permutesPair_of_hyp8100 hH
  obtain ⟨hLC, hne, hshape, hr, hrg, hp, -⟩ := id hH
  by_cases hsp : IsStronglyPEmbedded r D.M
  · exact Or.inl hsp
  have hn0 : 2 ≤ n 0 := by
    rcases hshape 0 with hX | hX
    · exact uc22p20g_two_le_of_isL2 hX
    · have := (PartTwo.s13_odd_three_le_of_isSz hX).2
      omega
  have hr2 : r ≠ 2 := by
    rintro rfl
    have hg : Nat.gcd (n 0) (n 1) ≠ 0 := Nat.gcd_ne_zero_left (by omega)
    have h2 : 2 ∣ 2 ^ Nat.gcd (n 0) (n 1) := dvd_pow_self 2 hg
    have h1 : 1 ≤ 2 ^ Nat.gcd (n 0) (n 1) := Nat.one_le_two_pow
    omega
  have hrn0 : r ∣ 2 ^ n 0 - 1 :=
    hrg.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 (Nat.gcd_dvd_left _ _))
  by_cases hsw : ∃ m ∈ D.M, (L 0).map (MulAut.conj m).toMonoidHom = L 1
  ·
    obtain ⟨g, hg, hgL⟩ := hsw
    have hset : conjSetOf D.M (L 0) = {L 0, L 1} := by
      ext K
      constructor
      · rintro ⟨m, hm, rfl⟩
        rcases hperm m hm with ⟨h0, -⟩ | ⟨h0, -⟩
        · rw [h0]
          exact Set.mem_insert _ _
        · rw [h0]
          exact Set.mem_insert_of_mem _ rfl
      · rintro (rfl | rfl)
        · refine ⟨1, D.M.one_mem, ?_⟩
          rw [map_one]
          exact (Subgroup.map_id _).symm
        · exact ⟨g, hg, hgL.symm⟩
    have hc2 : (conjSetOf D.M (L 0)).ncard = 2 := by
      rw [hset]
      exact Set.ncard_pair hne
    obtain ⟨hnp, hsh⟩ :=
      r8100_eq_of_not_sp hSg hfour h614 h76 (hLC 0) hc2 (hshape 0) hr hr2 hrn0 hp hsp
    have hsh' : (IsL2 (Bar2 (L 0)) 3 ∧ p = 3 ∧ r = 7) ∨
        (IsSz (Bar2 (L 0)) 5 ∧ p = 5 ∧ r = 31) := by
      rcases hsh with ⟨hX, rfl⟩ | ⟨hX, rfl⟩
      · rw [hnp] at hrn0
        exact Or.inl ⟨hX, rfl, (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 hrn0⟩
      · rw [hnp] at hrn0
        exact Or.inr ⟨hX, rfl, (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 hrn0⟩
    rcases r8100_sp_or_dihedral hSg hfour h614 h76 hH hset.symm hnp with h1 | hφ
    · exact Or.inl h1
    exact Or.inr ⟨hset.symm, hnp, hsh', hsp, hφ⟩
  ·
    push Not at hsw
    have hN : ∀ i, D.M ≤ normalizer (L i : Set G) := by
      intro i m hm
      rw [UC6S846.mem_normalizer_iff_map_conj]
      rcases hperm m hm with ⟨h0, h1⟩ | ⟨h0, -⟩
      · fin_cases i
        · exact h0
        · exact h1
      · exact absurd h0 (hsw m hm)
    have h76s : ∀ q ∈ D.sig, IsStronglyPEmbedded q D.M → Conclusion76 D.M q :=
      fun q hq hsq => F07.R76Sig_of_R76 D h76 q hq (D.sig_prime q hq).2 hsq
    exact Or.inl (PartOne.Section8.r899_sp_of_normal hSg hfour h614 h76s (hLC 0) (hLC 1) hne
      (hN 0) (hN 1) (hshape 0) (hshape 1) (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _) hr hr2
      hrg)

theorem r8100R_of_conditions {D : Data G}
    (hSg : UC6S846.SigmaStd D) (hfour : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M)
    (h614 : UC6.R6_14 D) (h76 : F07.R76 D) (he : 3 < evenRank G) : F08.R8100R D := by
  intro L n r p A X hH
  rcases r8100_core hSg hfour h614 h76 hH with h1 | ⟨hset, -, hsh, -, hφ⟩
  · exact Or.inl h1
  rcases hsh with ⟨hX, rfl, -⟩ | ⟨hX, rfl, -⟩
  · exact Or.inr (Or.inr (Or.inl ⟨hset, hX, rfl, he, hφ⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hset, hX, rfl, he, hφ⟩))

theorem r8100R_dataOfSetup4
    (hSE : PartOne.Section7.StronglyEmbeddedFive) (hSE3 : PartOne.Section7.StronglyEmbeddedThree)
    (hB : PartOne.Section7.BadNoStrongThree) (hS : Standing4 G)
    (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G) (hMS : S.InMSigma) (hPart : PartIAt S.M) :
    F08.R8100R (UC6.dataOfSetup4 hS hU S) :=
  r8100R_of_conditions (UC6S846.sigmaStd_dataOfSetup4 hS hU S)
    ((dataExt_ofSetup4 hS hU S).four_le hS.rank) ((UC6.r6_14_dataOfSetup4_iff hS hU S).2 hPart.2.1)
    (UC6.r76_dataOfSetup4 hSE hSE3 hB hS hU S hMS hPart) hS.rank

end CFSG.LocalAnalysis.UniquenessCase.UC22
