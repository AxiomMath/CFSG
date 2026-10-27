module

public import CFSG.Quasithin.Background.RonanH163Tiso
public import CFSG.Quasithin.Background.RonanH143ConjA

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH163

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.RonanH143

variable {V : Type*} [CommGroup V] {Γ Γ' : Subgroup P24} (c : P24)

theorem exists_conjHom (hΓ : conjSubg c Γ = Γ') :
    ∃ φ : ↥Γ →* ↥Γ', (∀ g : ↥Γ, (φ g : P24) = c * g * c⁻¹) := by
  subst hΓ
  have hmem : ∀ g : ↥Γ, c * (g : P24) * c⁻¹ ∈ conjSubg c Γ := fun g => by
    rw [mem_conjSubg_iff, show c⁻¹ * (c * (g : P24) * c⁻¹) * c = (g : P24) by group]
    exact g.2
  refine ⟨{ toFun := fun g => ⟨c * (g : P24) * c⁻¹, hmem g⟩,
            map_one' := Subtype.ext (by simp),
            map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) },
    fun g => rfl⟩

theorem h163_MY_comp (hΓ : conjSubg c Γ = Γ') (Q : Finset (Finset (Fin 24))) :
    MY Γ' (c • Q) = conjSubg c (MY Γ Q) := by
  subst hΓ
  exact MY_conjSubg c Γ Q

theorem h163_KY_comp (hΓ : conjSubg c Γ = Γ') (Q : Finset (Finset (Fin 24))) :
    KY Γ' (c • Q) = conjSubg c (KY Γ Q) := by
  subst hΓ
  exact KY_conjSubg c Γ Q

theorem h163_isPGroup_of_conjSubg (K : Subgroup P24) (h : IsPGroup 2 ↥(conjSubg c K)) :
    IsPGroup 2 ↥K := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 h
  exact IsPGroup.iff_card.2 ⟨n, (card_conjSubg c K).symm.trans hn⟩

section Conj

variable (hΓ : conjSubg c Γ = Γ') (ρ' : ↥Γ' →* MulAut V) (φ : ↥Γ →* ↥Γ')
  (hφ : ∀ g : ↥Γ, (φ g : P24) = c * g * c⁻¹)

include hΓ hφ

theorem rImg_comp (A : Subgroup P24) : rImg (ρ'.comp φ) A = rImg ρ' (conjSubg c A) := by
  have key : (A.subgroupOf Γ).map φ = (conjSubg c A).subgroupOf Γ' := by
    ext y
    constructor
    · intro hy
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hy
      rw [Subgroup.mem_subgroupOf] at hg
      rw [Subgroup.mem_subgroupOf, hφ g, mem_conjSubg_iff,
        show c⁻¹ * (c * (g : P24) * c⁻¹) * c = (g : P24) by group]
      exact hg
    · intro hy
      rw [Subgroup.mem_subgroupOf, mem_conjSubg_iff] at hy
      have hyΓ : (y : P24) ∈ conjSubg c Γ := by
        rw [hΓ]
        exact y.2
      have hg : c⁻¹ * (y : P24) * c ∈ Γ := mem_conjSubg_iff.1 hyΓ
      refine Subgroup.mem_map.2 ⟨⟨c⁻¹ * (y : P24) * c, hg⟩, Subgroup.mem_subgroupOf.2 hy, ?_⟩
      apply Subtype.ext
      rw [hφ]
      show c * (c⁻¹ * (y : P24) * c) * c⁻¹ = (y : P24)
      group
  unfold rImg
  rw [← Subgroup.map_map, key]

theorem cenM_comp (W : Subgroup V) : cenM (ρ'.comp φ) W = (cenM ρ' W).comap φ := by
  unfold cenM
  rw [Subgroup.comap_comap]

theorem comap_subgroupOf (K : Subgroup P24) :
    ((conjSubg c K).subgroupOf Γ').comap φ = K.subgroupOf Γ := by
  ext g
  have e : c⁻¹ * (c * (g : P24) * c⁻¹) * c = (g : P24) := by group
  simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf, hφ, mem_conjSubg_iff, e]

theorem Concl163_comp (Q : Finset (Finset (Fin 24))) :
    Concl163 ρ' (c • Q) → Concl163 (ρ'.comp φ) Q := by
  have hM : rImg ρ' (MY Γ' (c • Q)) = rImg (ρ'.comp φ) (MY Γ Q) := by
    rw [h163_MY_comp c hΓ Q, rImg_comp c hΓ ρ' φ hφ]
  have hK : rImg ρ' (KY Γ' (c • Q)) = rImg (ρ'.comp φ) (KY Γ Q) := by
    rw [h163_KY_comp c hΓ Q, rImg_comp c hΓ ρ' φ hφ]
  unfold Concl163
  rintro ⟨⟨V₈, V₉, hC, hF⟩, hI, hcen, hP⟩
  refine ⟨⟨V₈, V₉, ?_, ?_⟩, ?_, ?_, ?_⟩
  · unfold Chain163 at hC ⊢
    rw [hM, hK] at hC
    exact hC
  · rw [hM, hK] at hF
    exact hF
  · rw [hM, hK] at hI
    exact hI
  · rw [← hK, cenM_comp c hΓ ρ' φ hφ, hcen, h163_KY_comp c hΓ Q]
    exact comap_subgroupOf c hΓ φ hφ (KY Γ Q)
  · have hP' := hP
    rw [h163_KY_comp c hΓ Q] at hP'
    exact h163_isPGroup_of_conjSubg c (KY Γ Q) hP'

end Conj

theorem Concl163_of_transport {V' : Type*} [CommGroup V'] (hΓ : conjSubg c Γ = Γ')
    (ρ : ↥Γ →* MulAut V) (ρ' : ↥Γ' →* MulAut V') (φ : ↥Γ →* ↥Γ')
    (hφ : ∀ g : ↥Γ, (φ g : P24) = c * g * c⁻¹) (e : V ≃* V')
    (he : ∀ (g : ↥Γ) (v : V), e (ρ g v) = ρ' (φ g) (e v)) (Q : Finset (Finset (Fin 24))) :
    Concl163 ρ' (c • Q) → Concl163 ρ Q := by
  intro h
  exact (Concl163_iff_of_iso ρ (ρ'.comp φ) e he Q).2 (Concl163_comp c hΓ ρ' φ hφ Q h)

end CFSG.Quasithin.RonanH163
