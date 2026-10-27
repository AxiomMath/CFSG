module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3PB
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8100U2
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4PA
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Cong
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Facts13

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace R3Pair

variable {D : Data G} {L K : Subgroup G} {n p : ℕ}

theorem false_of_inner (u : R3Pair D L K n p)
    {Ch : Choice2011 G} (h211 : S21_1 D Ch) (h869 : F08.R869NS5 D) (hU2 : R8100U2 D)
    (he : CFSG.Open.evenRank G = 3) (h1930 : H1930 D) (c : Ctx21 D Ch)
    {H₁ H₂ : Subgroup G} (hH₁ : H₁ ∈ hSet D.T D.M) (hH₂ : H₂ ∈ hSet D.T D.M)
    (hL0 : c.L0 ≤ H₁ ⊓ H₂)
    (hfX : ∀ X : Subgroup G, X ≤ D.M → D.T ≤ X → F12.InF 1 (⊤ : Subgroup (Bar2 X)) →
      (X : Set G) = ((H₁ ⊓ X : Subgroup G) : Set G) * ((H₂ ⊓ X : Subgroup G) : Set G))
    {q m : ℕ} (hq : q.Prime) (hm : Odd m) (hqm : q ∣ 2 ^ m - 1)
    {b : G} (hb : b ∈ c.B0) (hbN : b ∈ normalizer (D.T : Set G)) (hbo : orderOf b = q)
    (hinL : ∃ x₀ ∈ barImage D.M L, ∀ f ∈ barImage D.M L, uc22p21cPi D.M ⟨b, c.hBM hb⟩ * f *
      (uc22p21cPi D.M ⟨b, c.hBM hb⟩)⁻¹ = x₀ * f * x₀⁻¹)
    (hinK : ∃ x₁ ∈ barImage D.M K, ∀ f ∈ barImage D.M K, uc22p21cPi D.M ⟨b, c.hBM hb⟩ * f *
      (uc22p21cPi D.M ⟨b, c.hBM hb⟩)⁻¹ = x₁ * f * x₁⁻¹) : False := by
  have hq2 : q ≠ 2 := by have := PartTwo.s13_seven_le_of_dvd hm hq hqm; omega
  obtain ⟨hcomm, -, hZ₀, hZ₁, hX, hN, -⟩ := u4x_bar_structure u.hL u.hK u.hne u.hset u.shape
  obtain ⟨x₀, hx₀, hc₀⟩ := hinL
  obtain ⟨x₁, hx₁, hc₁⟩ := hinK
  have hβq : uc22p21cPi D.M ⟨b, c.hBM hb⟩ ^ q = 1 := by
    rw [← map_pow, show (⟨b, c.hBM hb⟩ : ↥D.M) ^ q = 1 from
      Subtype.ext (by simpa [← hbo] using pow_orderOf_eq_one b), map_one]
  have hpow : ∀ {F : Subgroup (Bar2 D.M)} {β x : Bar2 D.M}, center ↥F = ⊥ → x ∈ F →
      (∀ f ∈ F, β * f * β⁻¹ = x * f * x⁻¹) → β ^ q = 1 → x ^ q = 1 := by
    intro F β x hZ hx h hβ
    have hk : ∀ k : ℕ, ∀ f ∈ F, β ^ k * f * (β ^ k)⁻¹ = x ^ k * f * (x ^ k)⁻¹ := by
      intro k
      induction k with
      | zero => intro f _; simp
      | succ k ih =>
        intro f hf
        have hxf : x * f * x⁻¹ ∈ F := F.mul_mem (F.mul_mem hx hf) (F.inv_mem hx)
        calc β ^ (k + 1) * f * (β ^ (k + 1))⁻¹ = β ^ k * (β * f * β⁻¹) * (β ^ k)⁻¹ := by group
          _ = β ^ k * (x * f * x⁻¹) * (β ^ k)⁻¹ := by rw [h f hf]
          _ = x ^ k * (x * f * x⁻¹) * (x ^ k)⁻¹ := ih _ hxf
          _ = x ^ (k + 1) * f * (x ^ (k + 1))⁻¹ := by group
    have hc : (⟨x ^ q, F.pow_mem hx q⟩ : ↥F) ∈ center ↥F := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := hk q g g.2
      rw [hβ, one_mul, inv_one, mul_one] at h1
      apply Subtype.ext
      show (g : Bar2 D.M) * x ^ q = x ^ q * g
      calc (g : Bar2 D.M) * x ^ q = x ^ q * g * (x ^ q)⁻¹ * x ^ q := by rw [← h1]
        _ = x ^ q * g := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact congrArg Subtype.val hc
  have hx₀q := hpow hZ₀ hx₀ hc₀ hβq
  have hx₁q := hpow hZ₁ hx₁ hc₁ hβq
  have hc := u4x_mul_inv_mem_centralizer hcomm hx₀ hx₁ hc₀ hc₁
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
  have hs : Odd (Nat.gcd m n) := hm.of_dvd_nat (Nat.gcd_dvd_left m n)
  have hqs : q ∣ 2 ^ Nat.gcd m n - 1 := by
    rw [← Nat.pow_sub_one_gcd_pow_sub_one]
    exact Nat.dvd_gcd hqm hdvd
  have hAL := hU2 he L n _ q p u.hL u.hc2 u.hcong hs (Nat.gcd_dvd_right m n) hq hqs u.hσ
  have hAK := hU2 he K n _ q p u.symm.hL u.symm.hc2 u.symm.hcong hs (Nat.gcd_dvd_right m n) hq
    hqs u.symm.hσ
  by_cases hc1 : uc22p21cPi D.M ⟨b, c.hBM hb⟩ * (x₀ * x₁)⁻¹ = 1
  · have hbx := mul_inv_eq_one.1 hc1
    by_cases hx₀1 : x₀ = 1
    · have hx₁1 : x₁ ≠ 1 := by
        rintro rfl
        subst hx₀1
        refine u4p_not_mem_centralizer h869 h1930 c u.hL u.pX hb hq hq2 hbo ?_
        rw [hbx, mul_one]
        exact one_mem _
      exact u.symm.false_of_eq_one h211 h1930 c hH₁ hH₂ hL0 hfX hq hq2 hAK hb hbN hbo hx₁ hx₀
        hx₁q hx₀q hx₁1 (hbx.trans (hcomm x₀ hx₀ x₁ hx₁))
    · exact u.false_of_eq_one h211 h1930 c hH₁ hH₂ hL0 hfX hq hq2 hAL hb hbN hbo hx₀ hx₁ hx₀q
        hx₁q hx₀1 hbx
  · exact u.false_of_ne_one h211 h869 h1930 c hq hq2 (u.dvd_card_of_dvd hdvd) hAL hb hbN hbo hx₀
      hx₁ hx₀q hx₁q hc₀ hc₁ hc hc1

end R3Pair

end CFSG.LocalAnalysis.UniquenessCase.UC22
