module

public import CFSG.Quasithin.Background.RonanH164Tiso
public import CFSG.Quasithin.Background.RonanH163Tconj
public import CFSG.Quasithin.Background.RonanH143ConjB

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH163

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.RonanH143

theorem h164w_mem_conj {c : P24} {K : Subgroup P24} {k : P24} (hk : k ∈ K) :
    c * k * c⁻¹ ∈ conjSubg c K := by
  rw [mem_conjSubg_iff, show c⁻¹ * (c * k * c⁻¹) * c = k by group]
  exact hk

theorem h164w_mem_conj_inv {c : P24} {K : Subgroup P24} {k : P24} (hk : k ∈ conjSubg c K) :
    c⁻¹ * k * c ∈ K :=
  mem_conjSubg_iff.1 hk

theorem h164w_MY_comp {α : Type*} [MulAction P24 α] {c : P24} {Γ Γ' : Subgroup P24}
    (hΓ : conjSubg c Γ = Γ') (Y : α) : MY Γ' (c • Y) = conjSubg c (MY Γ Y) := by
  subst hΓ
  exact MY_conjSubg c Γ Y

theorem h164w_KY_comp {α : Type*} [MulAction P24 α] {c : P24} {Γ Γ' : Subgroup P24}
    (hΓ : conjSubg c Γ = Γ') (Y : α) : KY Γ' (c • Y) = conjSubg c (KY Γ Y) := by
  subst hΓ
  exact KY_conjSubg c Γ Y

theorem h164w_exists_perm_conj (c : P24) (M K : Subgroup P24) (n : ℕ) :
    (∃ π : ↥(conjSubg c M) →* Equiv.Perm (Fin n), Function.Surjective π ∧
        π.ker = (conjSubg c K).subgroupOf (conjSubg c M)) ↔
      (∃ π : ↥M →* Equiv.Perm (Fin n), Function.Surjective π ∧ π.ker = K.subgroupOf M) := by
  have h := exists_perm_surj_conj c M K n
  simpa only [MonoidHom.range_eq_top] using h

variable {V : Type*} [CommGroup V] {Γ Γ' : Subgroup P24} (c : P24)

section Conj

variable (hΓ : conjSubg c Γ = Γ') (ρ' : ↥Γ' →* MulAut V) (φ : ↥Γ →* ↥Γ')
  (hφ : ∀ g : ↥Γ, (φ g : P24) = c * g * c⁻¹)

include hΓ hφ

theorem isDualOfConj_comp (G : Subgroup P24) (A B : Subgroup V) (K : Subgroup P24) :
    IsDualOfConj ρ' (conjSubg c G) A B (conjSubg c K) →
      IsDualOfConj (ρ'.comp φ) G A B K := by
  unfold IsDualOfConj
  rintro ⟨pr, h1, h2, h3, h4, h5, h6⟩
  refine ⟨fun x k => pr x (c * k * c⁻¹), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx k hk k' hk'
    show pr x (c * (k * k') * c⁻¹) = pr x (c * k * c⁻¹) + pr x (c * k' * c⁻¹)
    rw [show c * (k * k') * c⁻¹ = (c * k * c⁻¹) * (c * k' * c⁻¹) by group]
    exact h1 x hx (c * k * c⁻¹) (h164w_mem_conj hk) (c * k' * c⁻¹) (h164w_mem_conj hk')
  · intro x hx x' hx' k hk
    exact h2 x hx x' hx' (c * k * c⁻¹) (h164w_mem_conj hk)
  · intro x hx k hk
    exact h3 x hx (c * k * c⁻¹) (h164w_mem_conj hk)
  · intro x hx hxB
    obtain ⟨k', hk', hne⟩ := h4 x hx hxB
    refine ⟨c⁻¹ * k' * c, h164w_mem_conj_inv hk', ?_⟩
    show pr x (c * (c⁻¹ * k' * c) * c⁻¹) ≠ 0
    rw [show c * (c⁻¹ * k' * c) * c⁻¹ = k' by group]
    exact hne
  · intro k hk hk1
    have hne : c * k * c⁻¹ ≠ 1 := by
      intro h
      apply hk1
      calc k = c⁻¹ * (c * k * c⁻¹) * c := by group
        _ = c⁻¹ * 1 * c := by rw [h]
        _ = 1 := by group
    obtain ⟨x, hx, hpr⟩ := h5 (c * k * c⁻¹) (h164w_mem_conj hk) hne
    exact ⟨x, hx, hpr⟩
  · intro g hg x hx k hk
    have hgφ : ((φ g : ↥Γ') : P24) ∈ conjSubg c G := by
      rw [hφ g, mem_conjSubg_iff, show c⁻¹ * (c * (g : P24) * c⁻¹) * c = (g : P24) by group]
      exact hg
    have key := h6 (φ g) hgφ x hx (c * k * c⁻¹) (h164w_mem_conj hk)
    rw [hφ g] at key
    show pr (ρ' (φ g) x) (c * ((g : P24) * k * (g : P24)⁻¹) * c⁻¹) = pr x (c * k * c⁻¹)
    rw [show c * ((g : P24) * k * (g : P24)⁻¹) * c⁻¹ =
      (c * (g : P24) * c⁻¹) * (c * k * c⁻¹) * (c * (g : P24) * c⁻¹)⁻¹ by group]
    exact key

theorem chain164_comp (Hx : Finset (Fin 24)) (V₅ V₆ : Subgroup V) :
    Chain164 ρ' (c • Hx) V₅ V₆ → Chain164 (ρ'.comp φ) Hx V₅ V₆ := by
  have hM : rImg ρ' (MY Γ' (c • Hx)) = rImg (ρ'.comp φ) (MY Γ Hx) := by
    rw [h164w_MY_comp hΓ Hx, rImg_comp c hΓ ρ' φ hφ]
  have hK : rImg ρ' (KY Γ' (c • Hx)) = rImg (ρ'.comp φ) (KY Γ Hx) := by
    rw [h164w_KY_comp hΓ Hx, rImg_comp c hΓ ρ' φ hφ]
  unfold Chain164
  intro h
  rw [hM, hK] at h
  exact h

theorem chain163_comp (Q : Finset (Finset (Fin 24))) (V₈ V₉ : Subgroup V) :
    Chain163 ρ' (c • Q) V₈ V₉ ↔ Chain163 (ρ'.comp φ) Q V₈ V₉ := by
  have hM : rImg ρ' (MY Γ' (c • Q)) = rImg (ρ'.comp φ) (MY Γ Q) := by
    rw [h164w_MY_comp hΓ Q, rImg_comp c hΓ ρ' φ hφ]
  have hK : rImg ρ' (KY Γ' (c • Q)) = rImg (ρ'.comp φ) (KY Γ Q) := by
    rw [h164w_KY_comp hΓ Q, rImg_comp c hΓ ρ' φ hφ]
  unfold Chain163
  rw [hM, hK]

theorem Concl164_comp (Hx : Finset (Fin 24)) (Q : Finset (Finset (Fin 24))) :
    Concl164 ρ' (c • Hx) (c • Q) → Concl164 (ρ'.comp φ) Hx Q := by
  have hM : rImg ρ' (MY Γ' (c • Hx)) = rImg (ρ'.comp φ) (MY Γ Hx) := by
    rw [h164w_MY_comp hΓ Hx, rImg_comp c hΓ ρ' φ hφ]
  have hK : rImg ρ' (KY Γ' (c • Hx)) = rImg (ρ'.comp φ) (KY Γ Hx) := by
    rw [h164w_KY_comp hΓ Hx, rImg_comp c hΓ ρ' φ hφ]
  have hKQ : rImg ρ' (KY Γ' (c • Q)) = rImg (ρ'.comp φ) (KY Γ Q) := by
    rw [h164w_KY_comp hΓ Q, rImg_comp c hΓ ρ' φ hφ]
  have hR : rImg ρ' (conjSubg c (KY Γ Hx)) = rImg (ρ'.comp φ) (KY Γ Hx) :=
    (rImg_comp c hΓ ρ' φ hφ (KY Γ Hx)).symm
  have hPi : (∃ π : ↥(MY Γ' (c • Hx)) →* Equiv.Perm (Fin 6), Function.Surjective π ∧
      π.ker = (KY Γ' (c • Hx)).subgroupOf (MY Γ' (c • Hx))) ↔
      (∃ π : ↥(MY Γ Hx) →* Equiv.Perm (Fin 6), Function.Surjective π ∧
        π.ker = (KY Γ Hx).subgroupOf (MY Γ Hx)) := by
    rw [h164w_MY_comp hΓ Hx, h164w_KY_comp hΓ Hx]
    exact h164w_exists_perm_conj c (MY Γ Hx) (KY Γ Hx) 6
  unfold Concl164
  intro h
  obtain ⟨V₅, V₆, hC, ⟨hFT, hD⟩, ⟨hPi', hIOS⟩, ⟨⟨V₈, V₉, hC4, hle4, hnle4⟩, hall4⟩, h5⟩ := h
  refine ⟨V₅, V₆, chain164_comp c hΓ ρ' φ hφ Hx V₅ V₆ hC, ⟨?_, ?_⟩, ⟨hPi.1 hPi', ?_⟩,
    ⟨⟨V₈, V₉, (chain163_comp c hΓ ρ' φ hφ Q V₈ V₉).1 hC4, hle4, ?_⟩, ?_⟩, ?_⟩
  · rw [hM, hK] at hFT
    exact hFT
  · rw [h164w_MY_comp hΓ Hx, h164w_KY_comp hΓ Hx, hR] at hD
    exact isDualOfConj_comp c hΓ ρ' φ hφ (MY Γ Hx) V₅ _ (KY Γ Hx) hD
  · rw [hM] at hIOS
    exact hIOS
  · rw [hKQ] at hnle4
    exact hnle4
  · intro V₈' V₉' hC'
    obtain ⟨h₁, h₂⟩ := hall4 V₈' V₉' ((chain163_comp c hΓ ρ' φ hφ Q V₈' V₉').2 hC')
    rw [hKQ] at h₂
    exact ⟨h₁, h₂⟩
  · rw [hK] at h5
    exact h5

end Conj

theorem Concl164_of_transport {V' : Type*} [CommGroup V'] (hΓ : conjSubg c Γ = Γ')
    (ρ : ↥Γ →* MulAut V) (ρ' : ↥Γ' →* MulAut V') (φ : ↥Γ →* ↥Γ')
    (hφ : ∀ g : ↥Γ, (φ g : P24) = c * g * c⁻¹) (e : V ≃* V')
    (he : ∀ (g : ↥Γ) (v : V), e (ρ g v) = ρ' (φ g) (e v)) (Hx : Finset (Fin 24))
    (Q : Finset (Finset (Fin 24))) : Concl164 ρ' (c • Hx) (c • Q) → Concl164 ρ Hx Q := by
  intro h
  exact (Concl164_iff_of_iso ρ (ρ'.comp φ) e he Hx Q).2 (Concl164_comp c hΓ ρ' φ hφ Hx Q h)

end CFSG.Quasithin.RonanH163
