module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4XH
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4XE

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace U4X

variable {D : Data G} {L K : Subgroup G} {n : ℕ}

theorem symm (u : U4X D L K n) : U4X D K L n where
  hL := u.hK
  hK := u.hL
  hne := u.hne.symm
  hset := by rw [uc22p2214_conjSetOf_eq u.mem_K, u.hset, Set.pair_comm]
  hc2 := by rw [uc22p2214_conjSetOf_eq u.mem_K]; exact u.hc2
  hLS := by
    obtain ⟨e⟩ := u4x_bar2_equiv u.mem_K
    rcases u.hLS with ⟨h3, h⟩ | ⟨h5, h⟩
    exacts [Or.inl ⟨h3, CFSG.Blueprint.LieModel.of_mulEquiv e h⟩,
      Or.inr ⟨h5, CFSG.Blueprint.LieModel.of_mulEquiv e h⟩]
  hσ := u.hσ

theorem false_of_uniqueSet (u : U4X D L K n) {Ch : Choice2011 G}
    (h211 : S21_1 D Ch) (hSg : UC6S846.SigmaStd D) (h869 : F08.R869NS5 D) (h1930 : H1930 D)
    (c : Ctx21 D Ch) (hn3 : 3 ≤ c.n) {H₁ H₂ : Subgroup G} (hH₁ : H₁ ∈ hSet D.T D.M)
    (hH₂ : H₂ ∈ hSet D.T D.M) (hL0 : c.L0 ≤ H₁ ⊓ H₂)
    (hfX : ∀ X : Subgroup G, X ≤ D.M → D.T ≤ X → F12.InF 1 (⊤ : Subgroup (Bar2 X)) →
      (X : Set G) = ((H₁ ⊓ X : Subgroup G) : Set G) * ((H₂ ⊓ X : Subgroup G) : Set G))
    (hAL : ∀ A : Subgroup G, A ≤ L → Nat.card A = 2 ^ n - 1 → A ∈ uniqueSet D.M)
    (hAK : ∀ A : Subgroup G, A ≤ K → Nat.card A = 2 ^ n - 1 → A ∈ uniqueSet D.M) : False := by
  obtain ⟨b, hb, hbo⟩ := u.exists_r hSg h869 h1930 c hn3
  have hbN := u4x_B0_le_normalizer c (u.odd_n hSg h869 h1930 c) hb
  obtain ⟨x₀, hx₀, x₁, hx₁, hx₀q, hx₁q, hc₀, hc₁, hc⟩ :=
    u.decomp c hb u.prime_r (u.ne_n hSg h1930 c hb u.prime_r hbo) hbo
  by_cases hc1 : uc22p21cPi D.M ⟨b, c.hBM hb⟩ * (x₀ * x₁)⁻¹ = 1
  · have hbx := mul_inv_eq_one.1 hc1
    obtain ⟨hcomm, -⟩ := u4x_bar_structure u.hL u.hK u.hne u.hset u.shape
    by_cases hx₀1 : x₀ = 1
    · have hx₁1 : x₁ ≠ 1 := by
        rintro rfl
        subst hx₀1
        refine u4x_not_mem_centralizer h869 h1930 c u.hL u.hK u.hne u.hset u.hc2 u.hLS u.hσ hb
          u.prime_r u.r_ne_two hbo ?_
        rw [hbx, mul_one]
        exact one_mem _
      exact u.symm.false_of_eq_one h211 h1930 c hH₁ hH₂ hL0 hfX hAK hb hbN hbo hx₁ hx₀ hx₁q hx₀q
        hx₁1 (hbx.trans (hcomm x₀ hx₀ x₁ hx₁))
    · exact u.false_of_eq_one h211 h1930 c hH₁ hH₂ hL0 hfX hAL hb hbN hbo hx₀ hx₁ hx₀q hx₁q hx₀1
        hbx
  · exact u.false_of_ne_one h211 h869 h1930 c hAL hb hbN hbo hx₀ hx₁ hx₀q hx₁q hc₀ hc₁ hc hc1

end U4X

end CFSG.LocalAnalysis.UniquenessCase.UC22
