module

public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.StandardType.FrameRoute.FS81

theorem le_of_sylow_section {X : Type} [Group X] [Finite X] {H F R T₀ : Subgroup X}
    (hFT : F ≤ T₀) (hTR : T₀ ≤ R) (hRH : R ≤ H)
    (hRn : ∀ h ∈ H, ∀ r ∈ R, h * r * h⁻¹ ∈ R) (hTn : ∀ r ∈ R, ∀ t ∈ T₀, r * t * r⁻¹ ∈ T₀)
    (hT2 : IsPGroup 2 T₀) (hodd : Odd (T₀.relIndex R))
    (h2 : ∀ T : Subgroup X, F ≤ T → T ≤ H → (∀ h ∈ H, ∀ t ∈ T, h * t * h⁻¹ ∈ T) →
      IsPGroup 2 T → T ≤ F)
    (h1 : ∀ R' : Subgroup X, F ≤ R' → R' ≤ H → (∀ h ∈ H, ∀ r ∈ R', h * r * h⁻¹ ∈ R') →
      Odd (F.relIndex R') → R' ≤ F) :
    R ≤ T₀ := by
  have key : ∀ x ∈ R, (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ T₀ := by
    intro x hx hx2
    obtain ⟨k, hk⟩ := hx2
    have hN : (T₀.subgroupOf R).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hTn (g : X) g.2 (n : X) hn
    have hpow : x ^ (T₀.relIndex R) ∈ T₀ := by
      haveI : (T₀.subgroupOf R).Normal := hN
      have h := Subgroup.pow_index_mem (T₀.subgroupOf R) (⟨x, hx⟩ : R)
      rw [Subgroup.mem_subgroupOf] at h
      simpa [Subgroup.relIndex] using h
    have hdvd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have hm2 : (T₀.relIndex R).Coprime (2 ^ k) :=
      Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hodd)
    have hmo : (T₀.relIndex R).Coprime (orderOf x) :=
      Nat.Coprime.coprime_dvd_right hdvd hm2
    exact (Subgroup.zpowers_le.2 hpow)
      ((mem_zpowers_pow_iff (g := x) (k := T₀.relIndex R)).2 hmo)
  have step2 : ∀ h ∈ H, ∀ t ∈ T₀, h * t * h⁻¹ ∈ T₀ := by
    intro h hh t ht
    refine key (h * t * h⁻¹) (hRn h hh t (hTR ht)) ?_
    obtain ⟨k, hk⟩ := hT2 ⟨t, ht⟩
    refine ⟨k, ?_⟩
    have htk : t ^ 2 ^ k = 1 := by
      simpa using congrArg Subtype.val hk
    rw [conj_pow, htk]
    simp
  have hTF : T₀ ≤ F := h2 T₀ hFT (hTR.trans hRH) step2 hT2
  have hFT_eq : F = T₀ := le_antisymm hFT hTF
  have hodd' : Odd (F.relIndex R) := by rw [hFT_eq]; exact hodd
  exact (h1 R (hFT.trans hTR) hRH hRn hodd').trans hFT

end CFSG.StandardType.FrameRoute.FS81

end
