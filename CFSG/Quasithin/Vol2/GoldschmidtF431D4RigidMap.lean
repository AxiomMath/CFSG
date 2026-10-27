module

public import CFSG.Quasithin.EmptyFaithful.S1421QA18Rig

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.Quasithin

theorem amalgamRigid_symm {D : Type} [Group D] {P₁ P₂ : Subgroup D}
    (h : S1421QA18.AmalgamRigid P₁ P₂) : S1421QA18.AmalgamRigid P₂ P₁ := by
  obtain ⟨hsup, hext⟩ := h
  refine ⟨by rw [sup_comm]; exact hsup, fun a₂ a₁ hag => ?_⟩
  obtain ⟨ρ, hρ₁, hρ₂⟩ := hext a₁ a₂ fun x h₁ h₂ => (hag x h₂ h₁).symm
  exact ⟨ρ, hρ₂, hρ₁⟩

theorem amalgamRigid_map {D D' : Type} [Group D] [Group D'] (e : D ≃* D') {P₁ P₂ : Subgroup D}
    (h : S1421QA18.AmalgamRigid P₁ P₂) :
    S1421QA18.AmalgamRigid (P₁.map e.toMonoidHom) (P₂.map e.toMonoidHom) := by
  obtain ⟨hsup, hext⟩ := h
  refine ⟨by rw [← Subgroup.map_sup, hsup, Subgroup.map_top_of_surjective _ e.surjective],
    fun a₁ a₂ hag => ?_⟩
  let e₁ : ↥P₁ ≃* ↥(P₁.map e.toMonoidHom) := e.subgroupMap P₁
  let e₂ : ↥P₂ ≃* ↥(P₂.map e.toMonoidHom) := e.subgroupMap P₂
  let b₁ : MulAut ↥P₁ := (e₁.trans a₁).trans e₁.symm
  let b₂ : MulAut ↥P₂ := (e₂.trans a₂).trans e₂.symm
  have hb₁ : ∀ (x : D) (hx : x ∈ P₁), ((b₁ ⟨x, hx⟩ : ↥P₁) : D) =
      e.symm ((a₁ ⟨e x, Subgroup.mem_map_of_mem _ hx⟩ : ↥(P₁.map e.toMonoidHom)) : D') := by
    intro x hx
    rfl
  have hb₂ : ∀ (x : D) (hx : x ∈ P₂), ((b₂ ⟨x, hx⟩ : ↥P₂) : D) =
      e.symm ((a₂ ⟨e x, Subgroup.mem_map_of_mem _ hx⟩ : ↥(P₂.map e.toMonoidHom)) : D') := by
    intro x hx
    rfl
  obtain ⟨ρ, hρ₁, hρ₂⟩ := hext b₁ b₂ fun x h₁ h₂ => by
    rw [hb₁, hb₂]
    exact congrArg e.symm (hag (e x) (Subgroup.mem_map_of_mem _ h₁) (Subgroup.mem_map_of_mem _ h₂))
  refine ⟨(e.symm.trans ρ).trans e, fun y hy => ?_, fun y hy => ?_⟩
  · have hx : e.symm y ∈ P₁ := by
      obtain ⟨x, hx, rfl⟩ := hy
      simpa using hx
    have := hρ₁ (e.symm y) hx
    rw [hb₁] at this
    show e (ρ (e.symm y)) = _
    rw [this]
    simp
  · have hx : e.symm y ∈ P₂ := by
      obtain ⟨x, hx, rfl⟩ := hy
      simpa using hx
    have := hρ₂ (e.symm y) hx
    rw [hb₂] at this
    show e (ρ (e.symm y)) = _
    rw [this]
    simp

theorem map_equiv_then_symm {D D' : Type} [Group D] [Group D'] (e : D ≃* D')
    (P : Subgroup D) : (P.map e.toMonoidHom).map e.symm.toMonoidHom = P := by
  ext x
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simpa using hz
  · intro hx
    exact ⟨e x, ⟨x, hx, rfl⟩, by simp⟩

theorem amalgamRigid_of_map {D D' : Type} [Group D] [Group D'] (e : D ≃* D')
    {P₁ P₂ : Subgroup D}
    (h : S1421QA18.AmalgamRigid (P₁.map e.toMonoidHom) (P₂.map e.toMonoidHom)) :
    S1421QA18.AmalgamRigid P₁ P₂ := by
  have := amalgamRigid_map e.symm h
  rwa [map_equiv_then_symm, map_equiv_then_symm] at this

end CFSG.Quasithin.D4Hex
