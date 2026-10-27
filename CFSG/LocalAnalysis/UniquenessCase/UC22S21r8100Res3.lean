module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8100Res2
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4Exc
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08UseS5
public import CFSG.LocalAnalysis.UniquenessCase.GL3Excl.GL3ExclBasic
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8100SzPair
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101UProof
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101UCheap
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4XI
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214Sz
import CFSG.LocalAnalysis.UniquenessCase.UC22P2213c
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229CongD
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Diag2
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229NSE
import CFSG.LocalAnalysis.UniquenessCase.UC6R77Three
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
public import CFSG.LocalAnalysis.UniquenessCase.UC22R8100BSp
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8100Sp
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4BC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def R8100Res3 (D : Data G) : Prop :=
  3 < evenRank G → ∀ (L : Subgroup G) (n s r p k : ℕ), L ∈ calC D.M →
    (conjSetOf D.M L).ncard = 2 → IsL2 (Bar2 L) n → Odd s → s ∣ n → r.Prime →
    r ∣ 2 ^ s - 1 → p ∈ D.sig → 0 < k → n = 2 ^ k * p →
    (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)] → IsStronglyPEmbedded r D.M

theorem uc22r8100r3_shape_of_eq {L : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hcong : (IsL2 (Bar2 L) p ∧ (2 : ℤ) ^ p ≡ -1 [ZMOD (p : ℤ)]) ∨
      (IsSz (Bar2 L) p ∧ (2 : ℤ) ^ (2 * p) ≡ -1 [ZMOD (p : ℤ)])) :
    (IsL2 (Bar2 L) 3 ∧ p = 3) ∨ (IsSz (Bar2 L) 5 ∧ p = 5) := by
  have hF : (2 : ℤ) ^ p ≡ 2 [ZMOD (p : ℤ)] := Int.ModEq.pow_prime_eq_self hp 2
  rcases hcong with ⟨hL2, hc⟩ | ⟨hSz, hc⟩
  · have h3 : (p : ℤ) ∣ ((3 : ℕ) : ℤ) := by
      have h1 := Int.modEq_iff_dvd.1 (hF.symm.trans hc)
      rw [show (-1 : ℤ) - 2 = -((3 : ℕ) : ℤ) by norm_num, dvd_neg] at h1
      exact h1
    have hp3 : p = 3 :=
      (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (Int.natCast_dvd_natCast.1 h3)
    subst hp3
    exact Or.inl ⟨hL2, rfl⟩
  · have h4 : (2 : ℤ) ^ (2 * p) ≡ 2 ^ 2 [ZMOD (p : ℤ)] := by
      rw [pow_mul']
      exact hF.pow 2
    have h5 : (p : ℤ) ∣ ((5 : ℕ) : ℤ) := by
      have h1 := Int.modEq_iff_dvd.1 (h4.symm.trans hc)
      rw [show (-1 : ℤ) - 2 ^ 2 = -((5 : ℕ) : ℤ) by norm_num, dvd_neg] at h1
      exact h1
    have hp5 : p = 5 :=
      (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 (Int.natCast_dvd_natCast.1 h5)
    subst hp5
    exact Or.inr ⟨hSz, rfl⟩

theorem uc22r8100r3_not_sp {D : Data G} {Ch : Choice2011 G}
    (h211 : S21_1 D Ch) (h1930 : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hc2 : (conjSetOf D.M L).ncard = 2) {n : ℕ} (hLS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n)
    {s q : ℕ} (hs : Odd s) (hsn : s ∣ n) (hq : q.Prime) (hqs : q ∣ 2 ^ s - 1) :
    ¬ IsStronglyPEmbedded q D.M := by
  rcases hLS with hL2 | hS
  · exact uc22s21r8100_hNS h211 h1930 c L n s q hL hc2 hL2 hs hsn hq hqs
  obtain ⟨x, -, hxo, hxT⟩ :=
    uc22ine229_exists_mem_conjClosure_normalizer_of_isSz D.sylowM hL hc2.le hS hs hsn hq hqs
  exact uc22ine229_not_sp_of_mem_normalizer h211 h1930 c hq (uc22ine229_ne_two hs hqs) hxT hxo

theorem uc22s21r8100Res3_outcome {D : Data G} {Ch : Choice2011 G}
    (h211 : S21_1 D Ch) (hSg : UC6S846.SigmaStd D)
    (hfour : 3 < evenRank G → ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p)
    (h614 : UC6.R6_14 D) (hres : R8100Res3 D) (h1930 : H1930 D) (c : Ctx21 D Ch)
    (he : 3 < evenRank G) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hc2 : (conjSetOf D.M L).ncard = 2) {n : ℕ}
    (hLS : IsSz (Bar2 L) n ∨ (IsL2 (Bar2 L) n ∧ ¬ IsPowTwo n)) {p : ℕ} (hp : p ∈ D.sig) :
    (IsL2 (Bar2 L) 3 ∧ p = 3) ∨ (IsSz (Bar2 L) 5 ∧ p = 5) := by
  have hLS' : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n := hLS.elim Or.inr fun h => Or.inl h.1
  have hprime : ∀ s' : ℕ, Odd s' → 1 < s' → ∃ q : ℕ, q.Prime ∧ q ∣ 2 ^ s' - 1 := by
    intro s' hs' hs'1
    have hs'3 : 3 ≤ s' := by
      obtain ⟨j, rfl⟩ := hs'
      omega
    exact Nat.exists_prime_and_dvd (n := 2 ^ s' - 1) (by
      have : 2 ^ 3 ≤ 2 ^ s' := Nat.pow_le_pow_right (by norm_num) hs'3
      omega)
  obtain ⟨s, hs, hs1, hsn⟩ := uc22p2213c_exists_odd hLS
  obtain ⟨r, hr, hrs⟩ := hprime s hs hs1
  have hr2 := uc22ine229_ne_two hs hrs
  have hnot := uc22r8100r3_not_sp h211 h1930 c hL hc2 hLS' hs hsn hr hrs
  have hrn : r ∣ 2 ^ n - 1 := hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn)
  have hcong := uc22ine229_cong_of_ncard_two hSg (UC6.r77E2_of_conclusion76 D h76) h614 hL hc2
    hLS' hr hr2 hrn hnot hp
  have hpn : p ∣ n := by
    by_contra hpn
    exact hnot (uc22s21r8100_sp_of_not_dvd hSg (hfour he) h614 h76 hL hc2 hLS' hsn hr hr2 hrs hp
      hpn)
  obtain ⟨hpp, -⟩ := D.sig_prime p hp
  obtain ⟨m, hm⟩ := hpn
  have hn0 : n ≠ 0 := by
    rcases hLS' with hL2 | hS
    · exact Nat.one_le_iff_ne_zero.1 (CFSG.Blueprint.LieModel.admissible hL2).2.1
    · exact (CFSG.LocalAnalysis.EvenBN.GMSK.odd_of_lieModel_twistedB2 hS).pos.ne'
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    exact hn0 hm
  by_cases hm1 : m = 1
  · subst hm1
    rw [mul_one] at hm
    rw [hm] at hcong
    exact uc22r8100r3_shape_of_eq hpp hcong
  exfalso
  obtain ⟨k, m', hm'o, hmk⟩ := Nat.exists_eq_two_pow_mul_odd hm0
  by_cases hm'1 : m' = 1
  ·
    subst hm'1
    rw [mul_one] at hmk
    have hk : 0 < k := Nat.pos_of_ne_zero fun hk0 => hm1 (by rw [hmk, hk0, pow_zero])
    have hn2 : n = 2 ^ k * p := by rw [hm, hmk, Nat.mul_comm]
    rcases hcong with ⟨hL2, hc⟩ | ⟨hS, -⟩
    · exact hnot (hres he L n s r p k hL hc2 hL2 hs hsn hr hrs hp hk hn2 hc)
    · have hno := CFSG.LocalAnalysis.EvenBN.GMSK.odd_of_lieModel_twistedB2 hS
      rw [hn2] at hno
      exact Nat.not_even_iff_odd.2 hno ((Nat.even_pow.2 ⟨even_two, hk.ne'⟩).mul_right p)
  ·
    obtain ⟨s', hs'p, hs'm'⟩ := Nat.exists_prime_and_dvd hm'1
    have hs'o : Odd s' := hm'o.of_dvd_nat hs'm'
    have hs'm : s' ∣ m := hs'm'.trans (Dvd.intro_left (2 ^ k) hmk.symm)
    have hs'n : s' ∣ n := hm ▸ Dvd.dvd.mul_left hs'm p
    obtain ⟨q, hq, hqs⟩ := hprime s' hs'o hs'p.one_lt
    have hq2 := uc22ine229_ne_two hs'o hqs
    have hqm : q ∣ 2 ^ m - 1 := hqs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hs'm)
    refine uc22r8100r3_not_sp h211 h1930 c hL hc2 hLS' hs'o hs'n hq hqs ?_
    rcases hcong with ⟨hL2, hc⟩ | ⟨hS, hc⟩
    · exact uc22s21r8100_sp_of_odd_factor hSg (hfour he) h614 h76 hL hc2 hL2 hs'n hq hq2 hqs hp hm
        (uc22r8100b_dvd_of_modEq hc) hqm
    · exact uc22s21r8100_sp_of_odd_factor_Sz hSg (hfour he) h614 h76 hL hc2 hS hs'n hq hq2 hqs hp
        hm (uc22r8100b_dvd_of_modEq hc) hqm

theorem r8101U_gt_of_inputs
    {D : Data G} {Ch : Choice2011 G} (h211 : S21_1 D Ch) (hSg : UC6S846.SigmaStd D)
    (hfour : 3 < evenRank G → ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M) (h614 : UC6.R6_14 D)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p) (h847 : F08.R847 D)
    (h869 : F08.R869NS5 D) (hGL : GL3Excl.GL3Excl) :
    H1930 D → ∀ _ : Ctx21 D Ch, 3 < evenRank G → ∀ L ∈ calC D.M,
      (conjSetOf D.M L).ncard = 2 → ∀ A : Subgroup G, A ≤ L →
        (IsL2 (Bar2 L) 3 ∧ D.sig = {3} ∧ Nat.card A = 7) ∨
          (IsSz (Bar2 L) 5 ∧ D.sig = {5} ∧ Nat.card A = 31) →
        A ∈ uniqueSet D.M := by
  intro h1930 c he L hL hc2 A hAL hcase
  obtain ⟨K, hKne, hset, hKC⟩ := uc22s21ru4e_exists_second_member hc2 hL
  obtain ⟨n, u, hAr⟩ : ∃ n, U4X D L K n ∧ Nat.card A = 2 ^ n - 1 := by
    rcases hcase with ⟨hL2, hs, hA⟩ | ⟨hSz, hs, hA⟩
    · exact ⟨3, ⟨hL, hKC, hKne, hset, hc2, Or.inl ⟨rfl, hL2⟩,
        by rw [hs]; exact Set.mem_singleton 3⟩, hA.trans (by norm_num)⟩
    · exact ⟨5, ⟨hL, hKC, hKne, hset, hc2, Or.inr ⟨rfl, hSz⟩,
        by rw [hs]; exact Set.mem_singleton 5⟩, hA.trans (by norm_num)⟩
  have hodd : Odd n := by
    rcases u.hLS with ⟨rfl, -⟩ | ⟨rfl, -⟩
    exacts [⟨1, rfl⟩, ⟨2, rfl⟩]
  have hnsp := uc22r8100r3_not_sp h211 h1930 c hL hc2 u.shape hodd dvd_rfl u.prime_r dvd_rfl
  have hsp := UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC u.hL) u.hσ
  exact u.u81_mem_uniqueSet_of_residual hSg (hfour he) h614 h76 h847 he hnsp
    (fun _ _ hR hBR hRB hBel hΩ hr3 hC1 hB0 hdvd =>
      u.u81_normalizer_le hsp (hfour he n u.hσ) h847 he h869 hGL hR hBR hRB hBel hΩ hr3 hC1 hB0
        hdvd)
    hAL hAr

theorem s21_22U4Exc_gt_of_inputs
    {D : Data G} {Ch : Choice2011 G} (h211 : S21_1 D Ch) (hSg : UC6S846.SigmaStd D)
    (hfour : 3 < evenRank G → ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M) (h614 : UC6.R6_14 D)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p) (h847 : F08.R847 D)
    (h869 : F08.R869NS5 D) (hGL : GL3Excl.GL3Excl)
    (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n) :
    H1930 D → ∀ c : Ctx21 D Ch, ∀ H₁ ∈ hSet D.T D.M, ∀ H₂ ∈ hSet D.T D.M, c.L0 ≤ H₁ ⊓ H₂ →
      (∀ X : Subgroup G, X ≤ D.M → D.T ≤ X → F12.InF 1 (⊤ : Subgroup (Bar2 X)) →
        (X : Set G) = ((H₁ ⊓ X : Subgroup G) : Set G) * ((H₂ ⊓ X : Subgroup G) : Set G)) →
      ⁅Hinf D.M, oTwoFOf D.M⁆ ≤ CFSG.Open.pCoreOf 2 D.M →
      (∀ p ∈ D.sig, CFSG.Open.pRank p (barPreimage D.M (centE D.M)) = 0) →
      3 < evenRank G → ∀ L ∈ calC D.M, (conjSetOf D.M L).ncard = 2 →
        ((IsL2 (Bar2 L) 3 ∧ D.sig = {3}) ∨ (IsSz (Bar2 L) 5 ∧ D.sig = {5})) → False := by
  intro h1930 c H₁ hH₁ H₂ hH₂ hL0 hfX _ _ he L hL hc2 hLS
  have hU := r8101U_gt_of_inputs h211 hSg hfour h614 h76 h847 h869 hGL h1930 c he
  obtain ⟨K, hKne, hset, hKC⟩ := uc22s21ru4e_exists_second_member hc2 hL
  obtain ⟨n, u, hsig⟩ : ∃ n, U4X D L K n ∧ D.sig = {n} := by
    rcases hLS with ⟨h3, hs⟩ | ⟨h5, hs⟩
    · exact ⟨3, ⟨hL, hKC, hKne, hset, hc2, Or.inl ⟨rfl, h3⟩, by rw [hs]; exact Set.mem_singleton 3⟩,
        hs⟩
    · exact ⟨5, ⟨hL, hKC, hKne, hset, hc2, Or.inr ⟨rfl, h5⟩, by rw [hs]; exact Set.mem_singleton 5⟩,
        hs⟩
  have hUX : ∀ {X Y : Subgroup G}, U4X D X Y n →
      ∀ A : Subgroup G, A ≤ X → Nat.card A = 2 ^ n - 1 → A ∈ uniqueSet D.M := by
    intro X Y v A hA hAc
    refine hU X v.hL v.hc2 A hA ?_
    rcases v.hLS with ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact Or.inl ⟨h, hsig, hAc.trans (by norm_num)⟩
    · exact Or.inr ⟨h, hsig, hAc.trans (by norm_num)⟩
  exact u.false_of_uniqueSet h211 hSg h869 h1930 c (hn3 h1930 c) hH₁ hH₂ hL0 hfX (hUX u)
    (hUX u.symm)

theorem s21_22U4BC_of_r8100Res3
    {D : Data G} {Ch : Choice2011 G} (h211 : S21_1 D Ch) (hSg : UC6S846.SigmaStd D)
    (hfour : 3 < evenRank G → ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p)
    (h614 : UC6.R6_14 D) (h847 : F08.R847 D) (h869 : F08.R869NS5 D) (hGL : GL3Excl.GL3Excl)
    (hn3H : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n) (hres : R8100Res3 D) : S21_22U4BC D Ch := by
  rintro h1930 c H₁ hH₁ H₂ hH₂ hL hfX hS1 hU3 he L hLC hc2 ⟨n, -, hLS⟩
  have hout : ∀ p ∈ D.sig, (IsL2 (Bar2 L) 3 ∧ p = 3) ∨ (IsSz (Bar2 L) 5 ∧ p = 5) :=
    fun p hp => uc22s21r8100Res3_outcome h211 hSg hfour h76 h614 hres h1930 c he hLC hc2 hLS hp
  obtain ⟨p₀, hp₀⟩ := hSg.nonempty
  refine s21_22U4Exc_gt_of_inputs h211 hSg hfour h614 h76 h847 h869 hGL hn3H h1930 c H₁ hH₁ H₂
    hH₂ hL (fun X h1 h2 hF => hfX X h1 h2 (Or.inl hF)) hS1 hU3 he L hLC hc2 ?_
  rcases hout p₀ hp₀ with ⟨hL8, rfl⟩ | ⟨hSz5, rfl⟩
  · refine Or.inl ⟨hL8, Set.eq_singleton_iff_unique_mem.2 ⟨hp₀, fun p hp => ?_⟩⟩
    exact ((hout p hp).resolve_right fun h => P2214S.false_of_isSz_of_isL2 h.1 hL8).2
  · refine Or.inr ⟨hSz5, Set.eq_singleton_iff_unique_mem.2 ⟨hp₀, fun p hp => ?_⟩⟩
    exact ((hout p hp).resolve_left fun h => P2214S.false_of_isSz_of_isL2 hSz5 h.1).2

end CFSG.LocalAnalysis.UniquenessCase.UC22
