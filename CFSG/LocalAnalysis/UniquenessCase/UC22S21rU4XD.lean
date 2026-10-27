module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4XB
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4XC
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214g
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Cong
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

structure U4X (D : Data G) (L K : Subgroup G) (n : ℕ) : Prop where
  hL : L ∈ calC D.M
  hK : K ∈ calC D.M
  hne : K ≠ L
  hset : conjSetOf D.M L = {L, K}
  hc2 : (conjSetOf D.M L).ncard = 2
  hLS : (n = 3 ∧ IsL2 (Bar2 L) n) ∨ (n = 5 ∧ IsSz (Bar2 L) n)
  hσ : n ∈ D.sig

theorem u4x_B0_le_normalizer {D : Data G} {Ch : Choice2011 G} (c : Ctx21 D Ch) (hodd : Odd c.n) :
    c.B0 ≤ normalizer (D.T : Set G) := by
  have hα := c.hα 0 c.n hodd (by simp)
  have hle : c.B0 ≤ oPi (etaSet c.n) c.B0 := by
    refine le_iSup₂_of_le c.B0 ⟨le_rfl, ?_, c.hpi.subset⟩ le_rfl
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.normal_top
  exact hle.trans (by simpa [etaSet] using hα)

theorem u4x_eq_one_of_pow {Q : Type} [Group Q] [Finite Q] {F : Subgroup Q} {x : Q} (hx : x ∈ F)
    {q : ℕ} (hq : q.Prime) (hqF : ¬ q ∣ Nat.card F) (hxq : x ^ q = 1) : x = 1 := by
  have h1 : orderOf (⟨x, hx⟩ : ↥F) ∣ q :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hxq))
  rcases (Nat.dvd_prime hq).1 h1 with h | h
  · simpa using congrArg Subtype.val (orderOf_eq_one_iff.1 h)
  · exact absurd (h ▸ orderOf_dvd_natCard _) hqF

namespace U4X

variable {D : Data G} {L K : Subgroup G} {n : ℕ}

theorem shape (u : U4X D L K n) : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n := by
  rcases u.hLS with ⟨-, h⟩ | ⟨-, h⟩
  exacts [Or.inl h, Or.inr h]

theorem mem_K (u : U4X D L K n) : K ∈ conjSetOf D.M L := by rw [u.hset]; simp

theorem shapeK (u : U4X D L K n) : IsL2 (Bar2 K) n ∨ IsSz (Bar2 K) n :=
  uc22s21ru4e_shape_conj u.mem_K u.shape

theorem prime_n (u : U4X D L K n) : n.Prime := by
  rcases u.hLS with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num

theorem prime_r (u : U4X D L K n) : (2 ^ n - 1).Prime := by
  rcases u.hLS with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num

theorem r_ne_two (u : U4X D L K n) : 2 ^ n - 1 ≠ 2 := by
  rcases u.hLS with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num

theorem mem_normalizer (u : U4X D L K n) {Ch : Choice2011 G} (c : Ctx21 D Ch) {b : G}
    (hb : b ∈ c.B0) : b ∈ normalizer (L : Set G) ∧ b ∈ normalizer (K : Set G) := by
  have hodd := uc22p21d_odd_orderOf_of_mem_calB1 c.hB0 hb
  have hcK : (conjSetOf D.M K).ncard = 2 := by rw [uc22p2214_conjSetOf_eq u.mem_K]; exact u.hc2
  exact ⟨uc22p2214_mem_normalizer_of_odd u.hc2 (c.hBM hb) hodd,
    uc22p2214_mem_normalizer_of_odd hcK (c.hBM hb) hodd⟩

theorem ne_n (u : U4X D L K n) {Ch : Choice2011 G} (hSg : UC6S846.SigmaStd D) (h1930 : H1930 D)
    (c : Ctx21 D Ch) {b : G} (hb : b ∈ c.B0) {q : ℕ} (hq : q.Prime) (hbo : orderOf b = q) :
    q ≠ n := by
  rintro rfl
  have hsp := UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC u.hL) u.hσ
  have hA : IsPGroup q (zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hbo, pow_one])
  have hA1 : zpowers b ≠ ⊥ := fun h =>
    hq.ne_one (by rw [← hbo, ← Nat.card_zpowers, h, Subgroup.card_bot])
  exact u4x_false_of_normalizer_le h1930 c hb
    (uc22p2214_normalizer_le_of_sp hq hsp (zpowers_le.2 (c.hBM hb)) hA hA1)

theorem decomp (u : U4X D L K n) {Ch : Choice2011 G}
    (c : Ctx21 D Ch) {b : G} (hb : b ∈ c.B0) {q : ℕ} (hq : q.Prime) (hqn : q ≠ n)
    (hbo : orderOf b = q) :
    ∃ x₀ ∈ barImage D.M L, ∃ x₁ ∈ barImage D.M K, x₀ ^ q = 1 ∧ x₁ ^ q = 1 ∧
      (∀ f ∈ barImage D.M L, uc22p21cPi D.M ⟨b, c.hBM hb⟩ * f *
        (uc22p21cPi D.M ⟨b, c.hBM hb⟩)⁻¹ = x₀ * f * x₀⁻¹) ∧
      (∀ f ∈ barImage D.M K, uc22p21cPi D.M ⟨b, c.hBM hb⟩ * f *
        (uc22p21cPi D.M ⟨b, c.hBM hb⟩)⁻¹ = x₁ * f * x₁⁻¹) ∧
      uc22p21cPi D.M ⟨b, c.hBM hb⟩ * (x₀ * x₁)⁻¹ ∈ centralizer
        ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)) := by
  obtain ⟨hbL, hbK⟩ := u.mem_normalizer c hb
  have hqn' : ¬ q ∣ n := fun h => hqn ((Nat.prime_dvd_prime_iff_eq hq u.prime_n).1 h)
  have hbq : b ^ q = 1 := by rw [← hbo]; exact pow_orderOf_eq_one b
  exact u4x_bar_decomp u.hL u.hK u.hne u.hset u.shape hq hqn' (b := ⟨b, c.hBM hb⟩) hbL hbK
    (Subtype.ext (by simpa using hbq))

theorem ne_three_of_five (u : U4X D L K n) {Ch : Choice2011 G}
    (h869 : F08.R869NS5 D) (h1930 : H1930 D) (c : Ctx21 D Ch) {b : G} (hb : b ∈ c.B0)
    (hbo : orderOf b = 3) (h5 : n = 5) : False := by
  obtain ⟨x₀, hx₀, x₁, hx₁, hx₀q, hx₁q, -, -, hc⟩ :=
    u.decomp c hb Nat.prime_three (by omega) hbo
  have hS5 : IsSz (Bar2 L) 5 := by
    rcases u.hLS with ⟨h3, -⟩ | ⟨-, h⟩
    · omega
    · rw [h5] at h
      exact h
  have hK5 : IsSz (Bar2 K) 5 := by
    obtain ⟨e⟩ := u4x_bar2_equiv u.mem_K
    exact CFSG.Blueprint.LieModel.of_mulEquiv e hS5
  have h3 : ∀ {P : Subgroup G}, P ∈ calC D.M → IsSz (Bar2 P) 5 → ∀ x ∈ barImage D.M P,
      x ^ 3 = 1 → x = 1 := fun hP hPS x hx hxq => by
    obtain ⟨e, -⟩ := uc22p22l_barImage_equiv hP
    refine u4x_eq_one_of_pow hx Nat.prime_three ?_ hxq
    rw [← Nat.card_congr e.toEquiv]
    exact CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 hPS
  obtain rfl := h3 u.hL hS5 x₀ hx₀ hx₀q
  obtain rfl := h3 u.hK hK5 x₁ hx₁ hx₁q
  obtain ⟨-, -, -, -, hX, -, -⟩ := u4x_bar_structure u.hL u.hK u.hne u.hset u.shape
  refine u4x_not_mem_centralizer h869 h1930 c u.hL u.hK u.hne u.hset u.hc2 u.hLS u.hσ hb
    Nat.prime_three (by norm_num) hbo ?_
  rw [hX]
  simpa using hc

theorem odd_n (u : U4X D L K n) {Ch : Choice2011 G}
    (hSg : UC6S846.SigmaStd D) (h869 : F08.R869NS5 D) (h1930 : H1930 D) (c : Ctx21 D Ch) :
    Odd c.n := by
  by_contra hev
  obtain ⟨k, hk⟩ := Nat.not_odd_iff_even.1 hev
  have h4 : 2 ^ c.n = 4 ^ k := by rw [hk, ← two_mul, pow_mul]; norm_num
  have h3 : 3 ∣ 2 ^ c.n - 1 := by
    rw [h4]
    have e : (4 : ℕ) - 1 ∣ 4 ^ k - 1 := Nat.sub_one_dvd_pow_sub_one 4 k
    simpa using e
  have h3B : 3 ∣ Nat.card c.B0 := by
    have h : 3 ∈ piSet c.B0 := by rw [c.hpi]; exact ⟨Nat.prime_three, h3⟩
    exact h.2
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥c.B0) 3 h3B
  have hbo : orderOf (b : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hb
  rcases u.hLS with ⟨h3n, -⟩ | ⟨h5, -⟩
  · exact u.ne_n hSg h1930 c b.2 Nat.prime_three hbo h3n.symm
  · exact u.ne_three_of_five h869 h1930 c b.2 hbo h5

theorem eq_r (u : U4X D L K n) {Ch : Choice2011 G}
    (hSg : UC6S846.SigmaStd D) (h869 : F08.R869NS5 D) (h1930 : H1930 D) (c : Ctx21 D Ch)
    {b : G} (hb : b ∈ c.B0) {q : ℕ} (hq : q.Prime) (hbo : orderOf b = q) : q = 2 ^ n - 1 := by
  have hodd := uc22p21d_odd_orderOf_of_mem_calB1 c.hB0 hb
  have hq2 : q ≠ 2 := by
    rintro rfl
    rw [hbo] at hodd
    exact (by decide : ¬ Odd 2) hodd
  obtain ⟨x₀, hx₀, x₁, hx₁, hx₀q, hx₁q, hc₀, hc₁, hc⟩ :=
    u.decomp c hb hq (u.ne_n hSg h1930 c hb hq hbo) hbo
  have hbN := uc22ine229_mk_mem_normalizer (L := D.T) (x := ⟨b, c.hBM hb⟩)
    (u4x_B0_le_normalizer c (u.odd_n hSg h869 h1930 c) hb)
  obtain ⟨hcomm, -, -, -, hX, hN, -⟩ := u4x_bar_structure u.hL u.hK u.hne u.hset u.shape
  have hT := u4x_isSylowOf_barImage D.sylowM
  have hnot : x₀ ≠ 1 ∨ x₁ ≠ 1 := by
    by_contra hcon
    obtain ⟨rfl, rfl⟩ := not_or.1 hcon |>.imp not_not.1 not_not.1
    refine u4x_not_mem_centralizer h869 h1930 c u.hL u.hK u.hne u.hset u.hc2 u.hLS u.hσ hb hq
      hq2 hbo ?_
    rw [hX]
    simpa using hc
  have key : ∀ {F : Subgroup (Bar2 D.M)} {x : Bar2 D.M}, (IsL2 ↥F n ∨ IsSz ↥F n) →
      CFSG.ABGLocalTools.IsSylowOf 2 (barImage D.M D.T ⊓ F) F → x ∈ F → x ≠ 1 → x ^ q = 1 →
      (∀ f ∈ F, uc22p21cPi D.M ⟨b, c.hBM hb⟩ * f * (uc22p21cPi D.M ⟨b, c.hBM hb⟩)⁻¹ =
        x * f * x⁻¹) → q ∣ 2 ^ n - 1 := by
    intro F x hF hS hxF hx1 hxq hcx
    refine u4x_dvd_of_borel hF hS hxF hx1 (fun s hs => ?_) hq hq2 hxq
    rw [← hcx s hs.2]
    exact (Subgroup.mem_normalizer_iff.1 hbN s).1 hs.1
  have hdvd : q ∣ 2 ^ n - 1 := by
    rcases hnot with h0 | h1
    · exact key (u4x_shape_barImage u.hL u.shape) (u4x_isSylowOf_inf hcomm hN hT) hx₀ h0 hx₀q hc₀
    · exact key (u4x_shape_barImage u.hK u.shapeK)
        (u4x_isSylowOf_inf (fun x hx y hy => (hcomm y hy x hx).symm) (by rwa [sup_comm]) hT)
        hx₁ h1 hx₁q hc₁
  exact (Nat.prime_dvd_prime_iff_eq hq u.prime_r).1 hdvd

theorem exists_r (u : U4X D L K n) {Ch : Choice2011 G}
    (hSg : UC6S846.SigmaStd D) (h869 : F08.R869NS5 D) (h1930 : H1930 D) (c : Ctx21 D Ch)
    (hn3 : 3 ≤ c.n) : ∃ b ∈ c.B0, orderOf b = 2 ^ n - 1 := by
  have h7 : 2 ^ c.n - 1 ≠ 1 := by
    have : 2 ^ 3 ≤ 2 ^ c.n := Nat.pow_le_pow_right (by norm_num) hn3
    omega
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h7
  have hpB : p ∣ Nat.card c.B0 := by
    have h : p ∈ piSet c.B0 := by rw [c.hpi]; exact ⟨hp, hpd⟩
    exact h.2
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨b, hbo⟩ := exists_prime_orderOf_dvd_card' (G := ↥c.B0) p hpB
  have hbo' : orderOf (b : G) = p := by rw [Subgroup.orderOf_coe]; exact hbo
  exact ⟨b, b.2, hbo'.trans (u.eq_r hSg h869 h1930 c b.2 hp hbo')⟩

end U4X

end CFSG.LocalAnalysis.UniquenessCase.UC22
