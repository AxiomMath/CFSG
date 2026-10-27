module

public import CFSG.Milestones.ASVolI.F48.D43.Stab2

public section

namespace CFSG.ASVolI

open CFSG.Blueprint.Chevalley CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native

attribute [local irreducible] burnsideF48d_KeysHex burnsideF48d_TabsHex burnsideF48d_GensHex
  burnsideF48d_PhiHex burnsideF48d_limbs burnsideF48d_colTab

section Torus


theorem burnsideF48d_normalizer_T {b : ↥burnsideF48d_X} (hb : b ∈ burnsideF48d_P1 ⊓ burnsideF48d_P2)
    (hn : ∀ t ∈ burnsideF48d_T, b * t * b⁻¹ ∈ burnsideF48d_T) : b ∈ burnsideF48d_T := by
  obtain ⟨x0, x6, x479, x26571, x15916, x186, y0, y6, y479, y26571, y15916, y186⟩ :=
    burnsideF48d_xy_apt
  set f := (b : Equiv.Perm (Fin 26572)) with hf
  have hapt : ∀ p ∈ burnsideF48d_aptF, f p ∈ burnsideF48d_aptF := fun p hp => burnsideF48d_normT_apt hn hp
  have h0 : f 0 = 0 := (burnsideF48d_mem_P1 b).1 hb.1
  have hoc : ∀ p, burnsideF48d_oc (f p) = burnsideF48d_oc p := fun p => burnsideF48d_oc_smul hb.1 p
  obtain ⟨o0, o6, o186, o479, o15916, o26571⟩ := burnsideF48d_oc_values
  have h6 : f 6 = 6 := by
    have hl : f 6 ∈ burnsideF48d_line := (burnsideF48d_mem_P2 b).1 hb.2 6 (by decide)
    rcases burnsideF48d_apt_line (hapt 6 (by decide)) hl with h | h
    · rw [← h0] at h; exact absurd (f.injective h) (by decide)
    · exact h
  have h186 : f 186 = 186 := by
    rcases (burnsideF48d_apt_oc (hapt 186 (by decide))).1 (by rw [hoc, o186]) with h | h
    · rw [← h6] at h; exact absurd (f.injective h) (by decide)
    · exact h
  have h26571 : f 26571 = 26571 :=
    (burnsideF48d_apt_oc (hapt 26571 (by decide))).2.2 (by rw [hoc, o26571])
  have h479 : f 479 = 479 := by
    rcases (burnsideF48d_apt_oc (hapt 479 (by decide))).2.1 (by rw [hoc, o479]) with h | h
    · exact h
    ·
      exfalso
      set c := (burnsideF48d_L 1)⁻¹ * b * burnsideF48d_L 1 with hc
      have hc0 : (c : Equiv.Perm (Fin 26572)) 0 = 0 := by
        rw [hc]
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply,
          Equiv.Perm.mul_apply]
        rw [y0, ← hf, h6, Equiv.Perm.inv_eq_iff_eq, y0]
      have hc186 : (c : Equiv.Perm (Fin 26572)) 186 = 26571 := by
        rw [hc]
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply,
          Equiv.Perm.mul_apply]
        rw [y186, ← hf, h, Equiv.Perm.inv_eq_iff_eq, y26571]
      have := burnsideF48d_oc_smul ((burnsideF48d_mem_P1 c).2 hc0) 186
      rw [hc186, o26571, o186] at this
      omega
  have h15916 : f 15916 = 15916 := by
    rcases (burnsideF48d_apt_oc (hapt 15916 (by decide))).2.1 (by rw [hoc, o15916]) with h | h
    · rw [← h479] at h; exact absurd (f.injective h) (by decide)
    · exact h
  rw [burnsideF48d_mem_T]
  intro p hp
  rcases burnsideF48d_aptF_cases hp with h | h | h | h | h | h <;> subst h
  exacts [h0, h6, h479, h26571, h15916, h186]

theorem burnsideF48d_L0_normT : ∀ k ∈ burnsideF48d_T,
    burnsideF48d_L 0 * k * (burnsideF48d_L 0)⁻¹ ∈ burnsideF48d_T := by
  obtain ⟨x0, x6, x479, x26571, x15916, x186, -⟩ := burnsideF48d_xy_apt
  refine burnsideF48d_normT_of_apt fun p hp => ?_
  rcases burnsideF48d_aptF_cases hp with h | h | h | h | h | h <;> subst h
  · rw [x0]; decide
  · rw [x6]; decide
  · rw [x479]; decide
  · rw [x26571]; decide
  · rw [x15916]; decide
  · rw [x186]; decide

theorem burnsideF48d_L1_normT : ∀ k ∈ burnsideF48d_T,
    burnsideF48d_L 1 * k * (burnsideF48d_L 1)⁻¹ ∈ burnsideF48d_T := by
  obtain ⟨-, -, -, -, -, -, y0, y6, y479, y26571, y15916, y186⟩ := burnsideF48d_xy_apt
  refine burnsideF48d_normT_of_apt fun p hp => ?_
  rcases burnsideF48d_aptF_cases hp with h | h | h | h | h | h <;> subst h
  · rw [y0]; decide
  · rw [y6]; decide
  · rw [y479]; decide
  · rw [y26571]; decide
  · rw [y15916]; decide
  · rw [y186]; decide

theorem burnsideF48d_normT_mul {g h : ↥burnsideF48d_X}
    (hg : ∀ k ∈ burnsideF48d_T, g * k * g⁻¹ ∈ burnsideF48d_T)
    (hh : ∀ k ∈ burnsideF48d_T, h * k * h⁻¹ ∈ burnsideF48d_T) :
    ∀ k ∈ burnsideF48d_T, (g * h) * k * (g * h)⁻¹ ∈ burnsideF48d_T := by
  intro k hk
  have := hg _ (hh k hk)
  rwa [show g * (h * k * h⁻¹) * g⁻¹ = (g * h) * k * (g * h)⁻¹ by group] at this

theorem burnsideF48d_normT_inv {g : ↥burnsideF48d_X}
    (hg : ∀ k ∈ burnsideF48d_T, g * k * g⁻¹ ∈ burnsideF48d_T) :
    ∀ k ∈ burnsideF48d_T, g⁻¹ * k * g⁻¹⁻¹ ∈ burnsideF48d_T := by
  intro k hk
  rw [inv_inv]
  exact burnsideF48d_norm_inv hg k hk

theorem burnsideF48d_xred {x : ↥burnsideF48d_X} (hx : x ∈ burnsideF48d_P1) (hx2 : x ∉ burnsideF48d_P2)
    (hn : ∀ k ∈ burnsideF48d_T, x * k * x⁻¹ ∈ burnsideF48d_T) :
    (burnsideF48d_L 0)⁻¹ * x ∈ burnsideF48d_T := by
  obtain ⟨x0, x6, -, -, -, x186, -⟩ := burnsideF48d_xy_apt
  set f := (x : Equiv.Perm (Fin 26572)) with hf
  have h0 : f 0 = 0 := (burnsideF48d_mem_P1 x).1 hx
  have h6 : f 6 = 6 ∨ f 6 = 186 :=
    (burnsideF48d_apt_oc (burnsideF48d_normT_apt hn (by decide))).1
      (by rw [burnsideF48d_oc_smul hx, burnsideF48d_oc_values.2.1])
  rcases h6 with h6 | h6
  · exact absurd (burnsideF48d_B'_le_P2 (burnsideF48d_P1_6_le_B ⟨hx, burnsideF48d_fix_mem_stab h6⟩)) hx2
  · have hz : (burnsideF48d_L 0)⁻¹ * x ∈ burnsideF48d_P1 ⊓ burnsideF48d_P2 := by
      rw [burnsideF48d_B_eq_closure]
      refine burnsideF48d_P1_6_le_B ⟨(burnsideF48d_mem_P1 _).2 ?_, ?_⟩
      · rw [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply]
        rw [← hf, h0, Equiv.Perm.inv_eq_iff_eq, x0]
      · apply burnsideF48d_fix_mem_stab
        rw [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply]
        rw [← hf, h6, Equiv.Perm.inv_eq_iff_eq, x6]
    exact burnsideF48d_normalizer_T hz
      (burnsideF48d_normT_mul (burnsideF48d_normT_inv burnsideF48d_L0_normT) hn)

theorem burnsideF48d_yred {y : ↥burnsideF48d_X} (hy : y ∈ burnsideF48d_P2) (hy1 : y ∉ burnsideF48d_P1)
    (hn : ∀ k ∈ burnsideF48d_T, y * k * y⁻¹ ∈ burnsideF48d_T) :
    (burnsideF48d_L 1)⁻¹ * y ∈ burnsideF48d_T := by
  obtain ⟨-, -, -, -, -, -, y0, y6, -⟩ := burnsideF48d_xy_apt
  set f := (y : Equiv.Perm (Fin 26572)) with hf
  have hl : f 0 ∈ burnsideF48d_line := (burnsideF48d_mem_P2 y).1 hy 0 (by decide)
  have h0 : f 0 = 6 := by
    rcases burnsideF48d_apt_line (burnsideF48d_normT_apt hn (by decide)) hl with h | h
    · exact absurd ((burnsideF48d_mem_P1 y).2 h) hy1
    · exact h
  have hz : (burnsideF48d_L 1)⁻¹ * y ∈ burnsideF48d_P1 ⊓ burnsideF48d_P2 := by
    refine ⟨(burnsideF48d_mem_P1 _).2 ?_, burnsideF48d_P2.mul_mem (burnsideF48d_P2.inv_mem
      (Subgroup.subset_closure ⟨1, by decide, rfl⟩)) hy⟩
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply]
    rw [← hf, h0, Equiv.Perm.inv_eq_iff_eq, y0]
  exact burnsideF48d_normalizer_T hz
    (burnsideF48d_normT_mul (burnsideF48d_normT_inv burnsideF48d_L1_normT) hn)


end Torus

end CFSG.ASVolI
