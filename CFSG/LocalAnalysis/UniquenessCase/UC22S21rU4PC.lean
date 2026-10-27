module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4PB
public import CFSG.LocalAnalysis.UniquenessCase.UC22R8100BSp
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8100Res2
import CFSG.LocalAnalysis.UniquenessCase.UC22S217U3A
import CFSG.LocalAnalysis.UniquenessCase.UC22S217VRank
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Cong
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22i

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem u4p_sp_three {D : Data G} (hSg : UC6S846.SigmaStd D)
    (hfour : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M) (h614 : UC6.R6_14 D)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hc2 : (conjSetOf D.M L).ncard = 2) {n p k : ℕ}
    (hL2 : IsL2 (Bar2 L) n) (hp : p ∈ D.sig) (hk : 0 < k) (hn : n = 2 ^ k * p)
    (hcong : (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) : IsStronglyPEmbedded 3 D.M := by
  refine uc22s21r8100_sp_of_odd_factor (s := 2) (m := 2 ^ k) hSg hfour h614 h76 hL hc2 hL2
    (hn ▸ Dvd.dvd.mul_right (dvd_pow_self 2 hk.ne') p) Nat.prime_three (by norm_num)
    (by norm_num) hp (hn.trans (mul_comm _ _)) (uc22r8100b_dvd_of_modEq hcong) ?_
  obtain ⟨j, hj⟩ : ∃ j, 2 ^ k = 2 * j := ⟨2 ^ (k - 1), by rw [← pow_succ']; congr 1; omega⟩
  have e : (4 : ℕ) - 1 ∣ 4 ^ j - 1 := Nat.sub_one_dvd_pow_sub_one 4 j
  rw [hj, pow_mul, show (2 : ℕ) ^ 2 = 4 from rfl]
  simpa using e

theorem u4p_odd_n (D : Data G) (Ch : Choice2011 G) (h1930 : H1930 D) (c : Ctx21 D Ch)
    (h3 : IsStronglyPEmbedded 3 D.M) : Odd c.n := by
  by_contra hev
  obtain ⟨k, hk⟩ := Nat.not_odd_iff_even.1 hev
  refine uc22s217u3a_false_of_sp D Ch h1930 c Nat.prime_three ?_ h3
  have h4 : 2 ^ c.n = 4 ^ k := by rw [hk, ← two_mul, pow_mul]; norm_num
  rw [h4]
  have e : (4 : ℕ) - 1 ∣ 4 ^ k - 1 := Nat.sub_one_dvd_pow_sub_one 4 k
  simpa using e

theorem u4p_dvd_of_mem_B0 {D : Data G} {Ch : Choice2011 G} (c : Ctx21 D Ch) (hodd : Odd c.n)
    {n p k q : ℕ} (hn : n = 2 ^ k * p) (hq : q.Prime) (hqB : q ∣ Nat.card c.B0)
    (hqL : q ∣ 2 ^ n - 1 ∨ q ∣ 2 ^ n + 1) : q ∣ 2 ^ p - 1 := by
  have hqc : q ∣ 2 ^ c.n - 1 := by
    have h : q ∈ piSet c.B0 := ⟨hq, hqB⟩
    rw [c.hpi] at h
    exact h.2
  have h2n : q ∣ 2 ^ (2 * n) - 1 := by
    have e : 2 ^ (2 * n) - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      rw [mul_comm, pow_mul, ← Nat.sq_sub_sq, one_pow]
    rw [e]
    rcases hqL with h | h
    · exact h.mul_left _
    · exact h.mul_right _
  have hg : Nat.gcd c.n (2 * n) = Nat.gcd c.n p := by
    rw [hn, ← mul_assoc, ← pow_succ']
    exact Nat.Coprime.gcd_mul_left_cancel_right p
      (Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hodd))
  have hd := Nat.dvd_gcd hqc h2n
  rw [Nat.pow_sub_one_gcd_pow_sub_one, hg] at hd
  exact hd.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 (Nat.gcd_dvd_right c.n p))

namespace U4P

variable {D : Data G} {L K : Subgroup G} {n p : ℕ}

theorem decomp (u : U4P D L K n p) {Ch : Choice2011 G}
    (c : Ctx21 D Ch) {b : G} (hb : b ∈ c.B0) {q : ℕ} (hq : q.Prime) (hqn : ¬ q ∣ n)
    (hbo : orderOf b = q) :
    ∃ x₀ ∈ barImage D.M L, ∃ x₁ ∈ barImage D.M K, x₀ ^ q = 1 ∧ x₁ ^ q = 1 ∧
      (∀ f ∈ barImage D.M L, uc22p21cPi D.M ⟨b, c.hBM hb⟩ * f *
        (uc22p21cPi D.M ⟨b, c.hBM hb⟩)⁻¹ = x₀ * f * x₀⁻¹) ∧
      (∀ f ∈ barImage D.M K, uc22p21cPi D.M ⟨b, c.hBM hb⟩ * f *
        (uc22p21cPi D.M ⟨b, c.hBM hb⟩)⁻¹ = x₁ * f * x₁⁻¹) ∧
      uc22p21cPi D.M ⟨b, c.hBM hb⟩ * (x₀ * x₁)⁻¹ ∈ centralizer
        ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)) := by
  have hodd := uc22p21d_odd_orderOf_of_mem_calB1 c.hB0 hb
  have hcK : (conjSetOf D.M K).ncard = 2 := by rw [uc22p2214_conjSetOf_eq u.mem_K]; exact u.hc2
  have hbq : b ^ q = 1 := by rw [← hbo]; exact pow_orderOf_eq_one b
  exact u4x_bar_decomp u.hL u.hK u.hne u.hset u.shape hq hqn (b := ⟨b, c.hBM hb⟩)
    (uc22p2214_mem_normalizer_of_odd u.hc2 (c.hBM hb) hodd)
    (uc22p2214_mem_normalizer_of_odd hcK (c.hBM hb) hodd) (Subtype.ext (by simpa using hbq))

theorem false_of_uniqueSet (u : U4P D L K n p)
    {Ch : Choice2011 G} (h211 : S21_1 D Ch) (hSg : UC6S846.SigmaStd D)
    (hfour : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M) (h614 : UC6.R6_14 D)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p)
    (h869 : F08.R869NS5 D) (h1930 : H1930 D) (c : Ctx21 D Ch) (hn3 : 3 ≤ c.n)
    {H₁ H₂ : Subgroup G} (hH₁ : H₁ ∈ hSet D.T D.M) (hH₂ : H₂ ∈ hSet D.T D.M)
    (hL0 : c.L0 ≤ H₁ ⊓ H₂)
    (hfX : ∀ X : Subgroup G, X ≤ D.M → D.T ≤ X → F12.InF 1 (⊤ : Subgroup (Bar2 X)) →
      (X : Set G) = ((H₁ ⊓ X : Subgroup G) : Set G) * ((H₂ ⊓ X : Subgroup G) : Set G))
    (hAL : ∀ r : ℕ, r.Prime → r ∣ 2 ^ p - 1 → ∀ A : Subgroup G, A ≤ L → Nat.card A = r →
      A ∈ uniqueSet D.M)
    (hAK : ∀ r : ℕ, r.Prime → r ∣ 2 ^ p - 1 → ∀ A : Subgroup G, A ≤ K → Nat.card A = r →
      A ∈ uniqueSet D.M) : False := by
  obtain ⟨k, hk, hn⟩ := u.hk
  obtain ⟨hpp, -⟩ := D.sig_prime p u.hσ
  have hodd := u4p_odd_n D Ch h1930 c
    (u4p_sp_three hSg hfour h614 h76 u.hL u.hc2 u.hL2 u.hσ hk hn u.hcong)
  have h7 : 2 ^ c.n - 1 ≠ 1 := by
    have : 2 ^ 3 ≤ 2 ^ c.n := Nat.pow_le_pow_right (by norm_num) hn3
    omega
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd h7
  have hqB : q ∈ piSet c.B0 := by rw [c.hpi]; exact ⟨hq, hqd⟩
  obtain ⟨b, hb, hbo⟩ := uc22p22i_exists_elt_of_mem_piSet hqB
  have hq2 : q ≠ 2 := by
    rintro rfl
    have hodd' := uc22p21d_odd_orderOf_of_mem_calB1 c.hB0 hb
    rw [hbo] at hodd'
    exact (by decide : ¬ Odd 2) hodd'
  have hqp : q ≠ p := by
    rintro rfl
    exact uc22s217v_not_sp D Ch h1930 c hb hq hbo
      (UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC u.hL) u.hσ)
  have hqn : ¬ q ∣ n := by
    rw [hn]
    intro h
    rcases (Nat.Prime.dvd_mul hq).1 h with h | h
    · exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h))
    · exact hqp ((Nat.prime_dvd_prime_iff_eq hq hpp).1 h)
  have hbN := u4x_B0_le_normalizer c hodd hb
  obtain ⟨x₀, hx₀, x₁, hx₁, hx₀q, hx₁q, hc₀, hc₁, hc⟩ := u.decomp c hb hq hqn hbo
  obtain ⟨hcomm, -, -, -, hX, hN, -⟩ := u4x_bar_structure u.hL u.hK u.hne u.hset u.shape
  have hT := u4x_isSylowOf_barImage D.sylowM
  have hbN' := uc22ine229_mk_mem_normalizer (L := D.T) (x := ⟨b, c.hBM hb⟩) hbN
  have hnot : x₀ ≠ 1 ∨ x₁ ≠ 1 := by
    by_contra hcon
    obtain ⟨rfl, rfl⟩ := not_or.1 hcon |>.imp not_not.1 not_not.1
    refine u4p_not_mem_centralizer h869 h1930 c u.hL u.pX hb hq hq2 hbo ?_
    rw [hX]
    simpa using hc
  have key : ∀ {F : Subgroup (Bar2 D.M)} {x : Bar2 D.M}, (IsL2 ↥F n ∨ IsSz ↥F n) →
      CFSG.ABGLocalTools.IsSylowOf 2 (barImage D.M D.T ⊓ F) F → x ∈ F → x ≠ 1 → x ^ q = 1 →
      (∀ f ∈ F, uc22p21cPi D.M ⟨b, c.hBM hb⟩ * f * (uc22p21cPi D.M ⟨b, c.hBM hb⟩)⁻¹ =
        x * f * x⁻¹) → q ∣ 2 ^ n - 1 := by
    intro F x hF hS hxF hx1 hxq hcx
    refine u4x_dvd_of_borel hF hS hxF hx1 (fun s hs => ?_) hq hq2 hxq
    rw [← hcx s hs.2]
    exact (Subgroup.mem_normalizer_iff.1 hbN' s).1 hs.1
  have hdvd : q ∣ 2 ^ n - 1 := by
    rcases hnot with h0 | h1
    · exact key (u4x_shape_barImage u.hL u.shape) (u4x_isSylowOf_inf hcomm hN hT) hx₀ h0 hx₀q
        hc₀
    · exact key (u4x_shape_barImage u.hK u.symm.shape)
        (u4x_isSylowOf_inf (fun x hx y hy => (hcomm y hy x hx).symm) (by rwa [sup_comm]) hT)
        hx₁ h1 hx₁q hc₁
  have hqp' : q ∣ 2 ^ p - 1 := u4p_dvd_of_mem_B0 c hodd hn hq hqB.2 (Or.inl hdvd)
  by_cases hc1 : uc22p21cPi D.M ⟨b, c.hBM hb⟩ * (x₀ * x₁)⁻¹ = 1
  · have hbx := mul_inv_eq_one.1 hc1
    by_cases hx₀1 : x₀ = 1
    · have hx₁1 : x₁ ≠ 1 := by
        rintro rfl
        subst hx₀1
        refine u4p_not_mem_centralizer h869 h1930 c u.hL u.pX hb hq hq2 hbo ?_
        rw [hbx, mul_one]
        exact one_mem _
      exact u.symm.false_of_eq_one h211 h1930 c hH₁ hH₂ hL0 hfX hq hq2 (hAK q hq hqp') hb hbN
        hbo hx₁ hx₀ hx₁q hx₀q hx₁1 (hbx.trans (hcomm x₀ hx₀ x₁ hx₁))
    · exact u.false_of_eq_one h211 h1930 c hH₁ hH₂ hL0 hfX hq hq2 (hAL q hq hqp') hb hbN hbo hx₀
        hx₁ hx₀q hx₁q hx₀1 hbx
  · exact u.false_of_ne_one h211 h869 h1930 c hq hq2 (u.dvd_card_of_dvd hdvd) (hAL q hq hqp') hb
      hbN hbo hx₀ hx₁ hx₀q hx₁q hc₀ hc₁ hc hc1

end U4P

end CFSG.LocalAnalysis.UniquenessCase.UC22
