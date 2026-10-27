module

public import CFSG.RankThree.PartTwo.Sec18.Item187Min

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Late
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem not_dvd_relIndex_of_isSylowOf {p : ℕ} [Fact p.Prime] {S X : Subgroup G}
    (h : CFSG.ABGLocalTools.IsSylowOf p S X) : ¬ p ∣ S.relIndex X :=
  (CFSG.ABGLocalTools.isSylowOf_iff.mp h).2.2

theorem eq_bot_of_inf_centralizer_le {X : Subgroup G}
    (hX : X ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 X : Set G) ≤ CFSG.Open.pCoreOf 2 X) :
    ∀ N : Subgroup G, N ≤ X → X ≤ Subgroup.normalizer (N : Set G) → ¬ 2 ∣ Nat.card N →
      N = ⊥ := by
  intro N hNX hXN hodd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNQ : N ⊓ CFSG.Open.pCoreOf 2 X = ⊥ := by
    have hsub : IsPGroup 2 (N ⊓ CFSG.Open.pCoreOf 2 X : Subgroup G) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).to_le inf_le_right
    obtain ⟨k, hk⟩ := hsub.exists_card_eq
    have hdvd : Nat.card (N ⊓ CFSG.Open.pCoreOf 2 X : Subgroup G) ∣ Nat.card N :=
      Subgroup.card_dvd_of_le inf_le_left
    rw [hk] at hdvd
    have hk0 : k = 0 := by
      by_contra hk0
      exact hodd ((dvd_pow_self 2 hk0).trans hdvd)
    rw [hk0, pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq _ hk
  rw [eq_bot_iff]
  intro n hn
  have hnX : n ∈ X := hNX hn
  have hcent : n ∈ Subgroup.centralizer (CFSG.Open.pCoreOf 2 X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hqQ : q ∈ CFSG.Open.pCoreOf 2 X := hq
    have hqX : q ∈ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X hqQ
    have h1 : n * q * n⁻¹ ∈ CFSG.Open.pCoreOf 2 X :=
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X hnX) q).mp hqQ
    have h3 : q * n⁻¹ * q⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hXN hqX) n⁻¹).mp (inv_mem hn)
    have e : n * q * n⁻¹ * q⁻¹ = n * (q * n⁻¹ * q⁻¹) := by simp only [mul_assoc]
    have h2 : n * q * n⁻¹ * q⁻¹ ∈ N := by
      rw [e]
      exact mul_mem hn h3
    have h4 : n * q * n⁻¹ * q⁻¹ ∈ CFSG.Open.pCoreOf 2 X := mul_mem h1 (inv_mem hqQ)
    have h5 : n * q * n⁻¹ * q⁻¹ ∈ N ⊓ CFSG.Open.pCoreOf 2 X :=
      Subgroup.mem_inf.mpr ⟨h2, h4⟩
    rw [hNQ, Subgroup.mem_bot] at h5
    exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h5)).symm
  have hnQ : n ∈ CFSG.Open.pCoreOf 2 X := hX (Subgroup.mem_inf.mpr ⟨hnX, hcent⟩)
  have h6 : n ∈ N ⊓ CFSG.Open.pCoreOf 2 X := Subgroup.mem_inf.mpr ⟨hn, hnQ⟩
  rw [hNQ] at h6
  exact h6

omit [Finite G] in
theorem sup_eq_of_mul_eq {X U V : Subgroup G} (hUX : U ≤ X) (hVX : V ≤ X)
    (h : (U : Set G) * (V : Set G) = (X : Set G)) : U ⊔ V = X := by
  refine le_antisymm (sup_le hUX hVX) fun x hx => ?_
  have hx' : x ∈ (U : Set G) * (V : Set G) := by
    rw [h]
    exact hx
  rw [Set.mem_mul] at hx'
  obtain ⟨u, hu, v, hv, rfl⟩ := hx'
  have hu' : u ∈ U := hu
  have hv' : v ∈ V := hv
  exact Subgroup.mul_mem_sup hu' hv'

omit [Finite G] in
private theorem le_normalizer_inf_core {K U V : Subgroup G}
    (hU : K ≤ Subgroup.normalizer (U : Set G))
    (hV : K ≤ Subgroup.normalizer (V : Set G)) :
    K ≤ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 := Subgroup.mem_normalizer_iff.mp (hU hg) x
  have h2 := Subgroup.mem_normalizer_iff.mp (hV hg) x
  simp only [SetLike.mem_coe, Subgroup.mem_inf]
  exact and_congr h1 h2

variable {A M H : Subgroup G} {c : G}

theorem MinCex.le_normalizer_or_le_normalizer {X : Subgroup G} (hX : MinCex A M H c X)
    {T T' : Subgroup G}
    (hT : A ⊔ CFSG.Open.pCoreOf 2 (H ⊓ M) ≤ Subgroup.normalizer (T : Set G))
    (hT' : A ⊔ CFSG.Open.pCoreOf 2 (H ⊓ M) ≤ Subgroup.normalizer (T' : Set G))
    (h : ((Subgroup.normalizer (T : Set G) ⊓ X : Subgroup G) : Set G) *
      ((Subgroup.normalizer (T' : Set G) ⊓ X : Subgroup G) : Set G) = (X : Set G)) :
    X ≤ Subgroup.normalizer (T : Set G) ∨ X ≤ Subgroup.normalizer (T' : Set G) := by
  have hAT : A ≤ Subgroup.normalizer (T : Set G) := le_sup_left.trans hT
  have hAT' : A ≤ Subgroup.normalizer (T' : Set G) := le_sup_left.trans hT'
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := le_sup_left.trans hX.le_normalizer
  have hUX : Subgroup.normalizer (T : Set G) ⊓ X ≤ X := inf_le_right
  have hVX : Subgroup.normalizer (T' : Set G) ⊓ X ≤ X := inf_le_right
  have hSU : CFSG.Open.pCoreOf 2 (H ⊓ M) ≤ Subgroup.normalizer (T : Set G) ⊓ X :=
    le_inf (le_sup_right.trans hT) hX.pCoreOf_le
  have hSV : CFSG.Open.pCoreOf 2 (H ⊓ M) ≤ Subgroup.normalizer (T' : Set G) ⊓ X :=
    le_inf (le_sup_right.trans hT') hX.pCoreOf_le
  have hAU : A ≤ Subgroup.normalizer
      ((Subgroup.normalizer (T : Set G) ⊓ X : Subgroup G) : Set G) :=
    le_normalizer_inf_core (hAT.trans Subgroup.le_normalizer) hAX
  have hAV : A ≤ Subgroup.normalizer
      ((Subgroup.normalizer (T' : Set G) ⊓ X : Subgroup G) : Set G) :=
    le_normalizer_inf_core (hAT'.trans Subgroup.le_normalizer) hAX
  have hUV := sup_eq_of_mul_eq hUX hVX h
  rcases hX.eq_or_eq hUX hVX hSU hSV hAU hAV hUV with h1 | h1
  · exact Or.inl ((le_of_eq h1.symm).trans inf_le_left)
  · exact Or.inr ((le_of_eq h1.symm).trans inf_le_left)

end CFSG.RankThree.PartTwo.Sec18.Item187Proof
