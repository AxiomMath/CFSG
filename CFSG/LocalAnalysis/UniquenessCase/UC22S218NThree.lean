module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S218N
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Conclusion76Three
public import CFSG.LocalAnalysis.UniquenessCase.UC22S218UR
import CFSG.LocalAnalysis.UniquenessCase.UC22S218NFour
import CFSG.LocalAnalysis.UniquenessCase.UC22S218P
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Facts13
import CFSG.LocalAnalysis.UniquenessCase.UC22S218NNormal
import CFSG.LocalAnalysis.UniquenessCase.UC22S218NTorus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76 StronglyEmbeddedThree)

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_8K (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx21 D Ch, ∀ L ∈ calC D.M, ∀ n : ℕ, IsSp4 (Bar2 L) n → ¬ IsPowTwo n →
    (L.subgroupOf D.M).Normal → 3 ∉ D.sig → (∀ p ∈ D.sig, p ∣ 2 ^ n + 1) → D.k = 1

theorem uc22s218n_dvd_two_pow_add_one (D : Data G) (Ch : Choice2011 G)
    (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h211 : S21_1 D Ch) (h76 : F07.R76Sig D)
    (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M) {n : ℕ}
    (hX : IsSp4 (Bar2 L) n) (hn : ¬ IsPowTwo n) {p : ℕ} (hp : p ∈ D.sig) : p ∣ 2 ^ n + 1 := by
  by_contra hpd
  have hns := UC6S846.not_solvable_of_mem_calC hL
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hsp := UC6S846.sp_of_mem_sig hSg hns hp
  have hLM : L ≤ D.M := hL.1.le
  have : (L.subgroupOf D.M).Normal := uc22s218n_normal D Ch hSg h211 hH c hL hX hn
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
    ·
      have hpd2 : ¬ p ∣ (2 ^ n) ^ 2 - 1 := by
        obtain ⟨k, hk⟩ : ∃ k, 2 ^ n = k + 1 :=
          ⟨2 ^ n - 1, by have := Nat.one_le_two_pow (n := n); omega⟩
        have e1 : (k + 1) ^ 2 - 1 = k * (k + 2) := Nat.sub_eq_of_eq_add (by ring)
        rw [hk, e1]
        intro h
        rcases (Nat.Prime.dvd_mul hpp).1 h with h | h
        · exact hpn (by rw [hk, Nat.add_sub_cancel]; exact h)
        · exact hpd (by rw [hk]; exact h)
      have hrank : CFSG.Open.pRank p L + 2 ≤ CFSG.Open.pRank p D.M := by
        have h1 := uc22s218p_pRank_le_one_of_bar2 hX hpp hp2 hpd2
        have h3 := hSg.three_le p hp
        omega
      exact uc22p218s_exists_pow_torus hLM hX hpp hp2 hpn hr hr2 hrn hrank
  exact hCL r hr hr2 hrs (uc22s218n_stronglyEmbedded_of_torus D hSg h614 hL hML hX hpp
    (h76 p hp hp2 hsp) hr hr2 hrn hrσ hEL hEel hEc hQM hQel hQc hpow)

theorem uc22s218n_odd_of_conclusion76_three (D : Data G) (Ch : Choice2011 G)
    (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h211 : S21_1 D Ch)
    (h763 : Conclusion76 D.M 3) (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G}
    (hL : L ∈ calC D.M) {n : ℕ} (hX : IsSp4 (Bar2 L) n) (hn : ¬ IsPowTwo n) : Odd n := by
  by_contra hodd
  have hns := UC6S846.not_solvable_of_mem_calC hL
  have hLM : L ≤ D.M := hL.1.le
  have : (L.subgroupOf D.M).Normal := uc22s218n_normal D Ch hSg h211 hH c hL hX hn
  have hML : D.M ≤ normalizer (L : Set G) := le_normalizer_of_normal_subgroupOf hLM
  obtain ⟨s, hs, hs1, hsn⟩ := PartTwo.s13_exists_odd_divisor hn
  have hCL : ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ 2 ^ s - 1 → ¬ IsStronglyPEmbedded q D.M :=
    fun q hq hq2 hqs => uc22s218n_not_stronglyEmbedded D Ch h211 hH c hLM hML hX hs hsn hq hq2 hqs
  have hs3 : 3 ≤ s := by
    obtain ⟨k, rfl⟩ := hs
    omega
  have h8 : 8 ≤ 2 ^ s :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs3
  obtain ⟨r, hr, hrs⟩ := Nat.exists_prime_and_dvd (show 2 ^ s - 1 ≠ 1 by omega)
  have hr2 : r ≠ 2 := uc22p218c_ne_two_of_dvd (by omega) hrs
  have hr3 : (3 : ℕ) ≠ r := by
    have := uc22s218u_seven_le hs hr hrs
    omega
  have hrn : r ∣ 2 ^ n - 1 := hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn)
  have hrσ : r ∉ D.sig := fun hrσ => hCL r hr hr2 hrs (UC6S846.sp_of_mem_sig hSg hns hrσ)
  have h3n : 3 ∣ 2 ^ n - 1 :=
    Nat.pow_sub_one_dvd_pow_sub_one 2 (even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hodd))
  obtain ⟨E, Q, hEL, hEel, hEc, hQL, hQel, hQc, hpow⟩ :=
    uc22s218n_exists_pow_torus_inner hX Nat.prime_three (by norm_num) h3n hr hr2 hrn hr3
  exact hCL r hr hr2 hrs (uc22s218n_stronglyEmbedded_of_torus D hSg h614 hL hML hX
    Nat.prime_three h763 hr hr2 hrn hrσ hEL hEel hEc (hQL.trans hLM) hQel hQc hpow)

theorem s21_8N_of_s21_8K {D : Data G} {Ch : Choice2011 G} (hGA : GriessAllModelsStatement)
    (hSg : UC6S846.SigmaStd D) (h211 : S21_1 D Ch) (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D)
    (h763 : IsStronglyPEmbedded 3 D.M → Conclusion76 D.M 3) (hUR : S21_8UR D Ch)
    (hK : S21_8K D Ch) : S21_8N D Ch := by
  intro hH c L hL n hX hn r hr hrn
  have hX2 : IsSp4 (Bar2 L) n := uc22s218n_isSp4_bar2 hGA hL hX
  have hns := UC6S846.not_solvable_of_mem_calC hL
  have hN : (L.subgroupOf D.M).Normal := uc22s218n_normal D Ch hSg h211 hH c hL hX2 hn
  have hsp3 : IsStronglyPEmbedded 3 D.M := by
    by_cases h3 : 3 ∈ D.sig
    · exact UC6S846.sp_of_mem_sig hSg hns h3
    · have hk := hK hH c L hL n hX2 hn hN h3 fun p hp =>
        uc22s218n_dvd_two_pow_add_one D Ch hSg h614 h211 h76 hH c hL hX2 hn hp
      unfold Data.k kParam at hk
      split_ifs at hk with h
      · exact h
      · omega
  have hk : D.k = 1 := by
    unfold Data.k kParam
    rw [if_pos hsp3]
  have hodd : Odd n :=
    uc22s218n_odd_of_conclusion76_three D Ch hSg h614 h211 (h763 hsp3) hH c hL hX2 hn
  obtain ⟨X, hXc, hXle, hXU⟩ := hUR hH c L hL n hodd hX2 r hr hrn
  exact ⟨⟨hX2, hN, s21_8Sp4_of_s21_8U hSg h211 (s21_8U_of_s21_8UR hUR) hH c L hL n hodd hX2⟩,
    ⟨hodd, hk⟩, X, hXc, hXle.trans inf_le_left, hXU⟩

theorem s21_8N_dataOfSetup (hSE3 : StronglyEmbeddedThree) (hGA : GriessAllModelsStatement)
    (hKf : PartTwo.S19.K_19_25_noL2SzSection) (hS : RankThreeUC.Standing G)
    (hUC : CFSG.Open.rankThreeUC G) (hC : RankThreeUC.AGL81TheoremC G) (S : RankThreeUC.Setup G)
    {Ch : Choice2011 G} (h211 : S21_1 (PartTwo.Three.dataOfSetup hS S) Ch)
    (h614 : UC6.R6_14 (PartTwo.Three.dataOfSetup hS S))
    (h76 : F07.R76Sig (PartTwo.Three.dataOfSetup hS S))
    (h72 : F07.R72 (PartTwo.Three.dataOfSetup hS S))
    (hK : S21_8K (PartTwo.Three.dataOfSetup hS S) Ch) :
    S21_8N (PartTwo.Three.dataOfSetup hS S) Ch :=
  s21_8N_of_s21_8K hGA (UC6S846.sigmaStd_dataOfSetup hS S) h211 h614 h76
    (PartTwo.Three.conclusion76_three_dataOfSetup hSE3 hS hUC hC S)
    (s21_8UR_dataOfSetup hS hUC hC S h211 h614 h76 h72 hKf) hK

end CFSG.LocalAnalysis.UniquenessCase.UC22
