module

public import CFSG.Assembly.Defs
public import CFSG.Quasithin.Vol2.Ch10SecBL32K

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.L32

theorem u3_eq_mul : ∀ u : Γ, IsU u → ∃ e : Γ, IsEa e ∧ ∃ f : Γ, IsEb f ∧ u = e * f := by
  decide +kernel

theorem ka_not_u : ∃ k : Γ, IsKa k ∧ ¬ IsU k := by decide +kernel

theorem ka_not_pb : ∃ k : Γ, IsKa k ∧ ¬ IsPb k := by decide +kernel

theorem kb_not_pa : ∃ k : Γ, IsKb k ∧ ¬ IsPa k := by decide +kernel

theorem ka_sup_kb : Ka ⊔ Kb = ⊤ := by
  have hU : U3 ≤ Ka ⊔ Kb := fun u hu => by
    obtain ⟨e, he, f, hf, rfl⟩ := u3_eq_mul u hu
    exact Subgroup.mul_mem_sup (ea_le e he).1 (eb_le f hf).1
  rcases overgroups _ hU with h | h | h | h
  · exfalso
    obtain ⟨k, hk, hkU⟩ := ka_not_u
    have : k ∈ Ka ⊔ Kb := (le_sup_left : Ka ≤ Ka ⊔ Kb) hk
    rw [h] at this
    exact hkU this
  · exfalso
    obtain ⟨k, hk, hkP⟩ := kb_not_pa
    have : k ∈ Ka ⊔ Kb := (le_sup_right : Kb ≤ Ka ⊔ Kb) hk
    rw [h] at this
    exact hkP this
  · exfalso
    obtain ⟨k, hk, hkP⟩ := ka_not_pb
    have : k ∈ Ka ⊔ Kb := (le_sup_left : Ka ≤ Ka ⊔ Kb) hk
    rw [h] at this
    exact hkP this
  · exact h

theorem prod_sup_eq_top : Ka.prod Ka ⊔ Kb.prod Kb = ⊤ := by
  have hl : ∀ g : Γ, ((g, 1) : Γ × Γ) ∈ Ka.prod Ka ⊔ Kb.prod Kb := by
    intro g
    have hg : g ∈ Ka ⊔ Kb := by rw [ka_sup_kb]; trivial
    have h1 := Subgroup.mem_map_of_mem (MonoidHom.inl Γ Γ) hg
    rw [Subgroup.map_sup] at h1
    have hle : Ka.map (MonoidHom.inl Γ Γ) ⊔ Kb.map (MonoidHom.inl Γ Γ) ≤
        Ka.prod Ka ⊔ Kb.prod Kb :=
      sup_le_sup (by rintro _ ⟨k, hk, rfl⟩; exact ⟨hk, Subgroup.one_mem _⟩)
        (by rintro _ ⟨k, hk, rfl⟩; exact ⟨hk, Subgroup.one_mem _⟩)
    exact hle h1
  have hr : ∀ g : Γ, ((1, g) : Γ × Γ) ∈ Ka.prod Ka ⊔ Kb.prod Kb := by
    intro g
    have hg : g ∈ Ka ⊔ Kb := by rw [ka_sup_kb]; trivial
    have h1 := Subgroup.mem_map_of_mem (MonoidHom.inr Γ Γ) hg
    rw [Subgroup.map_sup] at h1
    have hle : Ka.map (MonoidHom.inr Γ Γ) ⊔ Kb.map (MonoidHom.inr Γ Γ) ≤
        Ka.prod Ka ⊔ Kb.prod Kb :=
      sup_le_sup (by rintro _ ⟨k, hk, rfl⟩; exact ⟨Subgroup.one_mem _, hk⟩)
        (by rintro _ ⟨k, hk, rfl⟩; exact ⟨Subgroup.one_mem _, hk⟩)
    exact hle h1
  refine eq_top_iff.mpr fun p _ => ?_
  have := (Ka.prod Ka ⊔ Kb.prod Kb).mul_mem (hl p.1) (hr p.2)
  simpa using this

end CFSG.Quasithin.Vol2.Ch10.SecB.L32
