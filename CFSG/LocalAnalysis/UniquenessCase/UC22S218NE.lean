module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S218NNormal
public import CFSG.LocalAnalysis.UniquenessCase.UC22S218NTorus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Facts13

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

variable {G : Type} [Group G] [Finite G]

theorem uc22s218n_pRank_le_three (D : Data G) (Ch : Choice2011 G) (hSg : UC6S846.SigmaStd D)
    (h614 : UC6.R6_14 D) (h211 : S21_1 D Ch)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p) (hH : H1930 D)
    (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M) {n : ℕ} (hX : IsSp4 (Bar2 L) n)
    (hn : ¬ IsPowTwo n) {p : ℕ} (hp : p ∈ D.sig) : CFSG.Open.pRank p D.M ≤ 3 := by
  by_contra h4
  have hns := UC6S846.not_solvable_of_mem_calC hL
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hsp := UC6S846.sp_of_mem_sig hSg hns hp
  have hLM : L ≤ D.M := hL.1.le
  haveI : (L.subgroupOf D.M).Normal := uc22s218n_normal D Ch hSg h211 hH c hL hX hn
  have hML : D.M ≤ normalizer (L : Set G) := le_normalizer_of_normal_subgroupOf hLM
  obtain ⟨s, hs, hs1, hsn⟩ := PartTwo.s13_exists_odd_divisor hn
  have hCL : ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ 2 ^ s - 1 → ¬ IsStronglyPEmbedded q D.M :=
    fun q hq hq2 hqs => uc22s218n_not_stronglyEmbedded D Ch h211 hH c hLM hML hX hs hsn hq hq2 hqs
  by_cases hps : p ∣ 2 ^ s - 1
  · exact hCL p hpp hp2 hps hsp
  have hs3 : 3 ≤ s := by
    obtain ⟨k, rfl⟩ := hs
    omega
  have h8 : 8 ≤ 2 ^ s :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs3
  obtain ⟨r, hr, hrs⟩ := Nat.exists_prime_and_dvd (show 2 ^ s - 1 ≠ 1 by omega)
  have hr2 : r ≠ 2 := uc22p218c_ne_two_of_dvd (by omega) hrs
  have hrn : r ∣ 2 ^ n - 1 := hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn)
  have hrσ : r ∉ D.sig := fun hrσ => hCL r hr hr2 hrs (UC6S846.sp_of_mem_sig hSg hns hrσ)
  have hpr : p ≠ r := by
    rintro rfl
    exact hps hrs
  obtain ⟨E, Q, hEL, hEel, hEc, hQM, hQel, hQc, hpow⟩ : ∃ E Q : Subgroup G, E ≤ L ∧
      IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧ Q ≤ D.M ∧ IsElemAbelian p Q ∧
        Nat.card Q = p ^ 2 ∧ ∀ x ∈ Q, ∃ k : ℕ, ∀ e ∈ E, x * e * x⁻¹ = e ^ k := by
    by_cases hpn : p ∣ 2 ^ n - 1
    · obtain ⟨E, Q, hEL, hEel, hEc, hQL, hQel, hQc, hpow⟩ :=
        uc22s218n_exists_pow_torus_inner hX hpp hp2 hpn hr hr2 hrn hpr
      exact ⟨E, Q, hEL, hEel, hEc, hQL.trans hLM, hQel, hQc, hpow⟩
    · have hrank : CFSG.Open.pRank p L + 2 ≤ CFSG.Open.pRank p D.M := by
        have := uc22p218d_pRank_le_two_of_bar2 hX hpp hp2
        omega
      exact uc22p218s_exists_pow_torus hLM hX hpp hp2 hpn hr hr2 hrn hrank
  exact hCL r hr hr2 hrs (uc22s218n_stronglyEmbedded_of_torus D hSg h614 hL hML hX hpp
    (h76 p hp hsp) hr hr2 hrn hrσ hEL hEel hEc hQM hQel hQc hpow)

end CFSG.LocalAnalysis.UniquenessCase.UC22
