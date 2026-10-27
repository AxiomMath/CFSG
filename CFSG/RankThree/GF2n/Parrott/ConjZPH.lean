module

public import CFSG.RankThree.GF2n.Parrott.Section2ClassCover

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

section DerivedLePH

variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

theorem commutator_H_le_map_P_H : ⁅H z, H z⁆ ≤ (P_H D).map (H z).subtype := by
  have hidx := index_P_H D
  rw [Subgroup.commutator_le]
  intro a ha b hb
  refine ⟨⁅(⟨a, ha⟩ : ↥(H z)), ⟨b, hb⟩⁆, ?_, by simp [commutatorElement_def]⟩
  rw [SetLike.mem_coe, commutatorElement_def, Subgroup.mul_mem_iff_of_index_two hidx,
    Subgroup.mul_mem_iff_of_index_two hidx, Subgroup.mul_mem_iff_of_index_two hidx,
    Subgroup.inv_mem_iff, Subgroup.inv_mem_iff]
  tauto

end DerivedLePH

section Cover

variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

theorem conj_z_mem_P_H_eq_of_cosets (h : Tim79a.ParrottHyp z)
    (hJ : ∀ j : G, j ∈ J z → orderOf j = 2 → j ≠ z → ∀ g : G, g * z * g⁻¹ ≠ j)
    (ht : ∀ x : G, cosetJ (z := z) (tH D) x → orderOf x = 2 → ∀ g : G, g * z * g⁻¹ ≠ x)
    (htu : ∀ x : G, cosetJ (z := z) (tH D * uH D) x → orderOf x = 2 →
      ∀ g : G, g * z * g⁻¹ ≠ x) :
    ∀ g : G, g * z * g⁻¹ ∈ (P_H D).map (H z).subtype → g * z * g⁻¹ = z := by
  intro g hg
  by_contra hne
  have hy2 : orderOf (g * z * g⁻¹) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj g) z
    rwa [MulAut.conj_apply, h.1] at this
  have hyH : g * z * g⁻¹ ∈ H z := Subgroup.map_subtype_le _ hg
  by_cases hyJ : g * z * g⁻¹ ∈ J z
  · exact hJ _ hyJ hy2 hne g rfl
  obtain ⟨k, hk, hcos⟩ := exists_conj_mem_cosets_of_involution D hyH hyJ hy2
  obtain ⟨yP, hyP, hyPeq⟩ := Subgroup.mem_map.mp hg
  have hwP : (⟨k, hk⟩ : ↥(H z)) * yP * (⟨k, hk⟩ : ↥(H z))⁻¹ ∈ P_H D :=
    (P_H_normal D).conj_mem yP hyP ⟨k, hk⟩
  have hweq : (((⟨k, hk⟩ : ↥(H z)) * yP * (⟨k, hk⟩ : ↥(H z))⁻¹ : ↥(H z)) : G) =
      k * (g * z * g⁻¹) * k⁻¹ := by
    rw [← hyPeq]
    rfl
  have hy2' : orderOf (k * (g * z * g⁻¹) * k⁻¹) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj k) (g * z * g⁻¹)
    rwa [MulAut.conj_apply, hy2] at this
  have hyz : (k * g) * z * (k * g)⁻¹ = k * (g * z * g⁻¹) * k⁻¹ := by group
  have hPcoset : ∀ t : ↥(H z), cosetJ (z := z) t (k * (g * z * g⁻¹) * k⁻¹) → t ∈ P_H D := by
    rintro t ⟨j, hj, hx⟩
    have hjP : (⟨j, J_le_H hj⟩ : ↥(H z)) ∈ P_H D :=
      J_le_P_H D (Subgroup.mem_subgroupOf.mpr hj)
    have ht_eq : t = ((⟨k, hk⟩ : ↥(H z)) * yP * (⟨k, hk⟩ : ↥(H z))⁻¹) *
        (⟨j, J_le_H hj⟩ : ↥(H z))⁻¹ := by
      apply Subtype.ext
      show (t : G) = ((((⟨k, hk⟩ : ↥(H z)) * yP * (⟨k, hk⟩ : ↥(H z))⁻¹ : ↥(H z)) : G)) * j⁻¹
      rw [hweq, hx]
      group
    rw [ht_eq]
    exact (P_H D).mul_mem hwP ((P_H D).inv_mem hjP)
  rcases hcos with h1 | h2 | h3 | h4
  · exact ht _ h1 hy2' (k * g) hyz
  · exact htu _ h2 hy2' (k * g) hyz
  · refine vH_not_mem_P_H D ?_
    have h5 := (P_H D).mul_mem ((P_H D).inv_mem (uH_mem_P_H D)) (hPcoset _ h3)
    rwa [inv_mul_cancel_left] at h5
  · refine vH_not_mem_P_H D ?_
    have h5 := (P_H D).mul_mem (hPcoset _ h4) ((P_H D).inv_mem (tH_mem_P_H D))
    rw [mul_inv_cancel_right] at h5
    have h6 := (P_H D).mul_mem ((P_H D).inv_mem (uH_mem_P_H D)) h5
    rwa [inv_mul_cancel_left] at h6

theorem conj_z_mem_derived_eq_of_cosets (h : Tim79a.ParrottHyp z)
    (hJ : ∀ j : G, j ∈ J z → orderOf j = 2 → j ≠ z → ∀ g : G, g * z * g⁻¹ ≠ j)
    (ht : ∀ x : G, cosetJ (z := z) (tH D) x → orderOf x = 2 → ∀ g : G, g * z * g⁻¹ ≠ x)
    (htu : ∀ x : G, cosetJ (z := z) (tH D * uH D) x → orderOf x = 2 →
      ∀ g : G, g * z * g⁻¹ ≠ x) :
    ∀ g : G, g * z * g⁻¹ ∈ ⁅H z, H z⁆ → g * z * g⁻¹ = z :=
  fun g hg => conj_z_mem_P_H_eq_of_cosets D h hJ ht htu g (commutator_H_le_map_P_H D hg)

end Cover

end CFSG.RankThree.GF2n.Parrott
