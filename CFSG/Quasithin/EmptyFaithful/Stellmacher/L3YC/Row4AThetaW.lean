module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row4AThetaSetting

public section

namespace CFSG.Quasithin

namespace Stellmacher.L3YC

section W

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_W_of_theta {T S L YL YC Yp Θ : Subgroup G} {t' : G} (hS2 : IsPGroup 2 ↥S)
    (hTS : T ≤ Subgroup.normalizer (S : Set G)) (hidx : S.relIndex T = 2) (ht'T : t' ∈ T)
    (ht'S : t' ∉ S) (hΘ0 : Θ ≠ ⊥) (hΘS : Θ ≤ S) (hSΘ : S ≤ Subgroup.normalizer (Θ : Set G))
    (hLΘ : L ≤ Subgroup.normalizer (Θ : Set G)) (hYCΘ : YC ≤ Subgroup.normalizer (Θ : Set G))
    (hLΘ' : L ≤ Subgroup.normalizer (B6.conjSub t' Θ : Set G))
    (hswap : B6.conjSub t' YL = YC) (hYLL : YL ≤ L) (hSY : S ≤ Subgroup.normalizer (YC : Set G))
    (hYp : Yp = YL ⊔ YC) :
    ∃ W : Subgroup G, W ≠ ⊥ ∧ IsPGroup 2 ↥W ∧ L ≤ Subgroup.normalizer (W : Set G) ∧
      T ≤ Subgroup.normalizer (W : Set G) ∧ Yp ≤ Subgroup.normalizer (W : Set G) := by
  classical
  have ht'2 : t' * t' ∈ S := mul_self_mem_S hidx ht'T
  have hΘ'S : B6.conjSub t' Θ ≤ S := by
    have := (B6.conjSub t').monotone hΘS
    rwa [B6.conjSub_eq_self (hTS ht'T)] at this
  have hSΘ' : S ≤ Subgroup.normalizer (B6.conjSub t' Θ : Set G) := by
    intro s hs
    rw [mem_normalizer_conjSub_iff]
    exact hSΘ ((Subgroup.mem_normalizer_iff''.mp (hTS ht'T) s).mp hs)
  have hYLΘ : YL ≤ Subgroup.normalizer (Θ : Set G) := fun g hg => hLΘ (hYLL hg)
  have hYLΘ' : YL ≤ Subgroup.normalizer (B6.conjSub t' Θ : Set G) := by
    intro g hg
    rw [mem_normalizer_conjSub_iff]
    refine hYCΘ ?_
    have h1 : t' * g * t'⁻¹ ∈ YC := by
      rw [← hswap, B6.mem_conjSub]
      have e : t'⁻¹ * (t' * g * t'⁻¹) * t' = g := by group
      rw [e]; exact hg
    have h2 := (Subgroup.mem_normalizer_iff.mp (hSY (S.inv_mem ht'2)) _).mp h1
    have e : (t' * t')⁻¹ * (t' * g * t'⁻¹) * ((t' * t')⁻¹)⁻¹ = t'⁻¹ * g * t' := by group
    rwa [e] at h2
  have hYCΘ' : YC ≤ Subgroup.normalizer (B6.conjSub t' Θ : Set G) := by
    intro g hg
    rw [mem_normalizer_conjSub_iff]
    refine hLΘ (hYLL ?_)
    rw [← hswap, B6.mem_conjSub] at hg
    exact hg
  have hWS : Θ ⊔ B6.conjSub t' Θ ≤ S := sup_le hΘS hΘ'S
  have hN : ∀ g : G, g ∈ Subgroup.normalizer (Θ : Set G) →
      g ∈ Subgroup.normalizer (B6.conjSub t' Θ : Set G) →
      g ∈ Subgroup.normalizer ((Θ ⊔ B6.conjSub t' Θ : Subgroup G) : Set G) := fun g h1 h2 =>
    Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨h1, h2⟩
  have ht'W : t' ∈ Subgroup.normalizer ((Θ ⊔ B6.conjSub t' Θ : Subgroup G) : Set G) := by
    rw [← conjSub_eq_self_iff, map_sup, ← B6.conjSub_mul,
      B6.conjSub_eq_self (hSΘ ht'2), sup_comm]
  refine ⟨Θ ⊔ B6.conjSub t' Θ, ?_, hS2.to_le hWS, fun g hg => hN g (hLΘ hg) (hLΘ' hg), ?_, ?_⟩
  · intro h
    apply hΘ0
    rw [eq_bot_iff]
    exact h ▸ le_sup_left
  · intro t ht
    rcases mem_S_or_of_index_two hidx ht'T ht'S ht with h | h
    · exact hN t (hSΘ h) (hSΘ' h)
    · have : t = t' * (t'⁻¹ * t) := by group
      rw [this]
      exact Subgroup.mul_mem _ ht'W (hN _ (hSΘ h) (hSΘ' h))
  · rw [hYp]
    refine sup_le (fun g hg => hN g (hYLΘ hg) (hYLΘ' hg)) (fun g hg => hN g (hYCΘ hg) (hYCΘ' hg))

end W

end Stellmacher.L3YC

end CFSG.Quasithin
