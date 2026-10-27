module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3Res
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8100U2
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08UseS5
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08UsePair
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229N
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs13
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E3
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3F2
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214d
import CFSG.LocalAnalysis.UniquenessCase.UC22P2213a
import CFSG.LocalAnalysis.UniquenessCase.UC22P20zbb
import CFSG.LocalAnalysis.UniquenessCase.UC22S13b
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Cong
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Facts13
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22i
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22r3r_barInner_of_inner {M X : Subgroup G} (hXM : X ≤ M) {b : G} (hbM : b ∈ M)
    (h : ∃ y ∈ X, ∀ x ∈ X, b * x * b⁻¹ * (y * x * y⁻¹)⁻¹ ∈ CFSG.Open.pCoreOf 2 M) :
    ∃ x₀ ∈ barImage M X, ∀ f ∈ barImage M X,
      uc22p21cPi M ⟨b, hbM⟩ * f * (uc22p21cPi M ⟨b, hbM⟩)⁻¹ = x₀ * f * x₀⁻¹ := by
  obtain ⟨y, hy, hyc⟩ := h
  refine ⟨uc22p21cPi M ⟨y, hXM hy⟩, uc22p21c_mem_barImage.2 ⟨⟨y, hXM hy⟩, hy, rfl⟩,
    fun f hf => ?_⟩
  obtain ⟨x, hxX, rfl⟩ := uc22p21c_mem_barImage.1 hf
  set z : ↥M := ⟨b, hbM⟩ * x * ⟨b, hbM⟩⁻¹ * (⟨y, hXM hy⟩ * x * (⟨y, hXM hy⟩ : ↥M)⁻¹)⁻¹ with hz
  have h1 := (uc22s13b_mem_pCoreOf_iff z.2).1 (hyc x hxX)
  have hz' : (⟨(z : G), z.2⟩ : ↥M) = z := rfl
  rw [hz', hz, map_mul, map_inv, mul_inv_eq_one] at h1
  simpa only [map_mul, map_inv] using h1

theorem s21_22R3_of_residuals {D : Data G} {Ch : Choice2011 G}
    (hSg : UC6S846.SigmaStd D) (h13 : PartTwo.SigmaRankThree13 D) (h211 : S21_1 D Ch)
    (h869 : F08.R869NS5 D) (h869P : F08.R869NPair D) (h15 : S21_15C D Ch) (hU2 : R8100U2 D)
    (hF3 : S21_22R3F3 D Ch) (hE5 : S21_22R3E5 D Ch) (hNP : S21_22R3NoPair D Ch) :
    S21_22R3 D Ch := by
  intro h1930 c H₁ hH₁ H₂ hH₂ hL0 hfX hS1 hU3 hs he
  refine hNP h1930 c H₁ hH₁ H₂ hH₂ hL0 hfX hS1 hU3 hs he fun L hL hc2 n hn hS => ?_
  by_cases hpow0 : IsPowTwo c.n
  · exact hE5 h1930 c H₁ hH₁ H₂ hH₂ hL0 hfX hS1 hU3 hs he hpow0 L hL hc2 n hn hS
  obtain ⟨e, m, hmo, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (uc22p2213a_n_ne_zero D c)
  have hm1 : m ≠ 1 := by
    rintro rfl
    exact hpow0 ⟨e, by rw [hnm, mul_one]⟩
  have h7 : 2 ^ m - 1 ≠ 1 := by
    have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by have := hmo.pos; omega)
    omega
  obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd h7
  have hq7 := PartTwo.s13_seven_le_of_dvd hmo hq hqm
  have hqB : q ∈ piSet c.B0 := by
    rw [c.hpi]
    refine ⟨hq, hqm.trans ?_⟩
    have h := Nat.pow_sub_one_gcd_pow_sub_one 2 m c.n
    rw [Nat.gcd_eq_left (Dvd.intro_left _ hnm.symm)] at h
    rw [← h]
    exact Nat.gcd_dvd_right _ _
  obtain ⟨b, hb, hbo⟩ := uc22p22i_exists_elt_of_mem_piSet hqB
  have hbN : b ∈ normalizer (D.T : Set G) :=
    c.hα e m hmo hnm (uc22pwtb_mem_oPi c.hB0.2.1 hb fun r hr hrd => by
      rw [hbo] at hrd
      rw [(Nat.prime_dvd_prime_iff_eq hr hq).1 hrd]
      exact ⟨hq, hqm⟩)
  obtain ⟨K, hne, hset, hK⟩ := uc22s21ru4e_exists_second_member hc2 hL
  by_cases hP : IsL2 (Bar2 L) n ∧ IsPowTwo n
  · exact uc22r3f_false_of_isPowTwo h869P h1930 c hL hc2 hn hP.2 hP.1 hq hmo hqm hb hbo
  obtain ⟨p, hp⟩ := hSg.nonempty
  have hS' : IsSz (Bar2 L) n ∨ (IsL2 (Bar2 L) n ∧ ¬ IsPowTwo n) :=
    hS.elim (fun h => Or.inr ⟨h, fun h' => hP ⟨h, h'⟩⟩) Or.inl
  have u : R3Pair D L K n p := ⟨hL, hK, hne, hset, hc2, hn, hp, h15 h1930 c L hL hc2 n hS' p hp⟩
  have hβq : uc22p21cPi D.M ⟨b, c.hBM hb⟩ ^ q = 1 := by
    rw [← map_pow, show (⟨b, c.hBM hb⟩ : ↥D.M) ^ q = 1 from
      Subtype.ext (by simpa [← hbo] using pow_orderOf_eq_one b), map_one]
  have hodd := uc22p21d_odd_orderOf_of_mem_calB1 c.hB0 hb
  have key : ∀ {Y Y' : Subgroup G}, R3Pair D Y Y' n p → ∃ x ∈ barImage D.M Y,
      ∀ f ∈ barImage D.M Y, uc22p21cPi D.M ⟨b, c.hBM hb⟩ * f *
        (uc22p21cPi D.M ⟨b, c.hBM hb⟩)⁻¹ = x * f * x⁻¹ := by
    intro Y Y' v
    by_contra hninn
    by_cases hqn : q ∣ 2 ^ n - 1
    · exact v.false_of_not_inner hSg h13 he h1930 c hq hq7 hqn hb hbo hninn
    have hbY := uc22p2214_mem_normalizer_of_odd v.hc2 (c.hBM hb) hodd
    by_cases hqd : q ∣ n
    · refine hF3 h1930 c H₁ hH₁ H₂ hH₂ hL0 hfX hS1 hU3 hs he Y v.hL v.hc2 n v.hn v.shape q b hq
        hqd hqn ⟨e, m, hmo, hnm, hqm⟩ hb hbo hbN hbY fun h => hninn ?_
      exact uc22r3r_barInner_of_inner v.hL.1.le (c.hBM hb) h
    · have hinn : ∀ α : MulAut ↥(barImage D.M Y), α ^ q = 1 →
          α ∈ (MulAut.conj : _ →* MulAut _).range := by
        intro α hα
        rcases u4x_shape_barImage v.hL v.shape with h | h
        · exact uc22p2214_inner_of_prime_L2 h hq hqd hα
        · exact uc22p2214_inner_of_prime_Sz h hq hqd hα
      obtain ⟨x, hx, -, hcx⟩ := u4x_inner_part (u4x_center_eq_bot v.hL v.shape) hinn
        (uc22ine229_mk_mem_normalizer hbY) hβq
      exact hninn ⟨x, hx, hcx⟩
  exact u.false_of_inner h211 h869 hU2 he h1930 c hH₁ hH₂ hL0
    (fun X h1 h2 hF => hfX X h1 h2 (Or.inl hF)) hq hmo hqm hb hbN hbo (key u) (key u.symm)

end CFSG.LocalAnalysis.UniquenessCase.UC22
