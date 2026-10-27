module

public import CFSG.Quasithin.H13.GoldschmidtU43BNorm
public import CFSG.Quasithin.H13.GoldschmidtU43BOrb

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

abbrev Tn (z t : G) : Subgroup G := Hz z ⊓ Subgroup.normalizer (Vg z t : Set G)

theorem conj_z_eq {z x : G} (hx : x ∈ Hz z) : x * z * x⁻¹ = z := by
  have hxz : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp hx
  calc x * z * x⁻¹ = (z * x) * x⁻¹ := by rw [hxz]
    _ = z := by group

theorem z_mem_Vg (z t : G) : z ∈ Vg z t := Subgroup.subset_closure (by simp)

theorem t_mem_Vg (z t : G) : t ∈ Vg z t := Subgroup.subset_closure (by simp)

namespace Hyp

variable {z : G} (h : Hyp z)
include h

theorem t_ne_zt {t : G} : t ≠ z * t := by
  intro e
  apply h.z_ne_one
  calc z = (z * t) * t⁻¹ := by group
    _ = 1 := by rw [← e]; group

theorem mem_Tn_of [Finite G] {t x : G} (ht : t ∈ S z) (hx : x ∈ Hz z)
    (hxt : x * t * x⁻¹ ∈ Vg z t) : x ∈ Tn z t :=
  ⟨hx, (h.comm2 ht).mem_normalizer_Vg (by rw [conj_z_eq hx]; exact z_mem_Vg z t) hxt⟩

theorem conj_t_cases [Finite G] {t g : G} (ht : t ∈ S z) (hg : g ∈ Tn z t) :
    g * t * g⁻¹ = t ∨ g * t * g⁻¹ = z * t := by
  have hp := h.comm2 ht
  have hgz : g * z * g⁻¹ = z := conj_z_eq hg.1
  have hgt : g * t * g⁻¹ ∈ Vg z t := (Subgroup.mem_normalizer_iff.mp hg.2 t).mp (t_mem_Vg z t)
  rcases (hp.mem_Vg_iff₄ _).1 hgt with e | e | e | e
  · exact absurd (by simpa using e) ht.2.2.1
  · exfalso
    apply ht.2.2.2
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = g⁻¹ * z * g := by rw [e]
      _ = g⁻¹ * (g * z * g⁻¹) * g := by rw [hgz]
      _ = z := by group
  · exact Or.inl e
  · exact Or.inr e

theorem card_Tn [Finite G] {t : G} (ht : t ∈ S z) : Nat.card ↥(Tn z t) = 128 := by
  classical
  have hp := h.comm2 ht
  have hne := h.t_ne_zt (t := t)
  have hΩ : ∀ g ∈ Tn z t, ∀ y ∈ ({t, z * t} : Set G), g * y * g⁻¹ ∈ ({t, z * t} : Set G) := by
    intro g hg y hy
    have hgz : g * z * g⁻¹ = z := conj_z_eq hg.1
    have hgt' := h.conj_t_cases ht hg
    have hgzt : g * (z * t) * g⁻¹ = z * (g * t * g⁻¹) := by
      calc g * (z * t) * g⁻¹ = (g * z * g⁻¹) * (g * t * g⁻¹) := by group
        _ = z * (g * t * g⁻¹) := by rw [hgz]
    rcases hy with rfl | rfl
    · exact hgt'
    · rw [hgzt]
      rcases hgt' with e | e
      · rw [e]; exact Or.inr rfl
      · rw [e, ← mul_assoc, h.sq_z, one_mul]; exact Or.inl rfl
  have htr : ∀ y ∈ ({t, z * t} : Set G), ∃ g ∈ Tn z t, g * t * g⁻¹ = y := by
    intro y hy
    rcases hy with rfl | rfl
    · exact ⟨1, one_mem _, by group⟩
    · obtain ⟨x, hxH, hx⟩ := h.exists_conj ht.1 ht.2.2.1 ht.2.2.2 ht.2.1
        (mul_mem h.z_mem ht.1) (h.mul_z_mem_S ht).2.2.1 (h.mul_z_mem_S ht).2.2.2
        (h.mul_z_mem_S ht).2.1
      refine ⟨x, h.mem_Tn_of ht hxH ?_, hx⟩
      rw [hx]
      exact (hp.mem_Vg_iff₄ _).2 (Or.inr (Or.inr (Or.inr rfl)))
  have hstab : Tn z t ⊓ Subgroup.centralizer ({t} : Set G) =
      Hz z ⊓ Subgroup.centralizer ({t} : Set G) := by
    refine le_antisymm (inf_le_inf_right _ inf_le_left) fun x hx => ?_
    refine ⟨h.mem_Tn_of ht hx.1 ?_, hx.2⟩
    have hxt : x * t * x⁻¹ = t := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hx.2
      calc x * t * x⁻¹ = (t * x) * x⁻¹ := by rw [this]
        _ = t := by group
    rw [hxt]
    exact t_mem_Vg z t
  have := card_eq_ncard_mul_card_inf_centralizer (Tn z t) {t, z * t} t hΩ (by simp) htr
  rw [hstab, h.card_centralizer_S ht, Set.ncard_pair hne] at this
  omega

end Hyp

end CFSG.Quasithin.H13.U43
