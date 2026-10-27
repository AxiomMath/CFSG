module

public import CFSG.Quasithin.AppendixH.H14.M24InvolutionClasses
public import CFSG.Quasithin.Background.F7TwoInvSporM23
public import CFSG.Quasithin.Background.F7TwoInvSporM22

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.ASVolI CFSG.ASVolI.ChH CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.Quasithin.F7Two

theorem isConjIn_of_mulEquiv {G : Subgroup S24} {Y : Type*} [Group Y] (E : ↥G ≃* Y)
    (hY : ∀ u u' : Y, orderOf u = 2 → orderOf u' = 2 → ∃ c : Y, u' = c * u * c⁻¹)
    {z z' : S24} (hz : z ∈ G) (hz' : z' ∈ G) (hz2 : orderOf z = 2) (hz2' : orderOf z' = 2) :
    IsConjIn G z z' := by
  have hu : orderOf (E ⟨z, hz⟩) = 2 := by
    rw [E.orderOf_eq, Subgroup.orderOf_mk, hz2]
  have hu' : orderOf (E ⟨z', hz'⟩) = 2 := by
    rw [E.orderOf_eq, Subgroup.orderOf_mk, hz2']
  obtain ⟨c, hc⟩ := hY (E ⟨z, hz⟩) (E ⟨z', hz'⟩) hu hu'
  refine ⟨(E.symm c : ↥G), (E.symm c).2, ?_⟩
  have key : E.symm c * (⟨z, hz⟩ : ↥G) * (E.symm c)⁻¹ = ⟨z', hz'⟩ := by
    apply E.injective
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hc.symm
  have hval := congrArg (fun x : ↥G => (x : S24)) key
  simpa using hval

theorem exists_involution_of_mulEquiv {G : Subgroup S24} {Y : Type*} [Group Y] (E : ↥G ≃* Y)
    (hY : ∃ u : Y, orderOf u = 2) : ∃ z ∈ G, orderOf z = 2 := by
  obtain ⟨u, hu⟩ := hY
  refine ⟨((E.symm u : ↥G) : S24), (E.symm u).2, ?_⟩
  rw [Subgroup.orderOf_coe, ← E.orderOf_eq, MulEquiv.apply_symm_apply, hu]

theorem m23_involutions_conj
    (u u' : ↥NativeSporadic.M23) (hu : orderOf u = 2)
    (hu' : orderOf u' = 2) : ∃ c : ↥NativeSporadic.M23, u' = c * u * c⁻¹ := by
  obtain ⟨c₁, hc₁, h₁⟩ :=
    m23_involution_conj u.2 (by rw [Subgroup.orderOf_coe, hu])
  obtain ⟨c₂, hc₂, h₂⟩ :=
    m23_involution_conj u'.2 (by rw [Subgroup.orderOf_coe, hu'])
  refine ⟨⟨c₂ * c₁⁻¹, Subgroup.mul_mem _ hc₂ (Subgroup.inv_mem _ hc₁)⟩, ?_⟩
  apply Subtype.ext
  show (u' : Equiv.Perm (Fin 23)) =
    (c₂ * c₁⁻¹) * (u : Equiv.Perm (Fin 23)) * (c₂ * c₁⁻¹)⁻¹
  rw [h₁, h₂]
  group

theorem exists_involution_M23 :
    ∃ u : ↥NativeSporadic.M23, orderOf u = 2 := by
  obtain ⟨hmem, hord, -⟩ := m23_rep_data1
  exact ⟨⟨m23Rep1, by simpa [m23Certificate_originalSubgroup] using hmem⟩,
    by rw [Subgroup.orderOf_mk]; exact hord⟩

theorem m22_involutions_conj
    (u u' : ↥NativeSporadic.M22) (hu : orderOf u = 2) (hu' : orderOf u' = 2) :
    ∃ c : ↥NativeSporadic.M22, u' = c * u * c⁻¹ := by
  obtain ⟨c₁, hc₁, h₁⟩ :=
    m22_inner_cover u.2 (by rw [Subgroup.orderOf_coe, hu])
  obtain ⟨c₂, hc₂, h₂⟩ :=
    m22_inner_cover u'.2 (by rw [Subgroup.orderOf_coe, hu'])
  refine ⟨⟨c₂ * c₁⁻¹, Subgroup.mul_mem _ hc₂ (Subgroup.inv_mem _ hc₁)⟩, ?_⟩
  apply Subtype.ext
  show (u' : Equiv.Perm (Fin 22)) =
    (c₂ * c₁⁻¹) * (u : Equiv.Perm (Fin 22)) * (c₂ * c₁⁻¹)⁻¹
  rw [h₁, h₂]
  group

theorem exists_involution_M22 :
    ∃ u : ↥NativeSporadic.M22, orderOf u = 2 := by
  obtain ⟨hmem, hord, -⟩ := m22_rep_data1
  exact ⟨⟨m22Rep1, by simpa [m22Certificate_originalSubgroup] using hmem⟩,
    by rw [Subgroup.orderOf_mk]; exact hord⟩

section Certs


theorem exists_involution_M23g (a : Fin 24) : ∃ z ∈ M23g a, orderOf z = 2 := by
  obtain ⟨E⟩ := nonempty_iso_M23g a
  exact exists_involution_of_mulEquiv E exists_involution_M23

theorem isConjIn_M23g (a : Fin 24) {z z' : S24} (hz : z ∈ M23g a) (hz' : z' ∈ M23g a)
    (hz2 : orderOf z = 2) (hz2' : orderOf z' = 2) : IsConjIn (M23g a) z z' := by
  obtain ⟨E⟩ := nonempty_iso_M23g a
  exact isConjIn_of_mulEquiv E (fun u u' hu hu' => m23_involutions_conj u u' hu hu')
    hz hz' hz2 hz2'

theorem exists_involution_M22g (a b : Fin 24) (hab : a ≠ b) : ∃ z ∈ M22g a b, orderOf z = 2 := by
  obtain ⟨E⟩ := nonempty_iso_M22g a b hab
  exact exists_involution_of_mulEquiv E exists_involution_M22

theorem isConjIn_M22g (a b : Fin 24) (hab : a ≠ b) {z z' : S24} (hz : z ∈ M22g a b)
    (hz' : z' ∈ M22g a b) (hz2 : orderOf z = 2) (hz2' : orderOf z' = 2) :
    IsConjIn (M22g a b) z z' := by
  obtain ⟨E⟩ := nonempty_iso_M22g a b hab
  exact isConjIn_of_mulEquiv E (fun u u' hu hu' => m22_involutions_conj u u' hu hu')
    hz hz' hz2 hz2'

theorem M23g_involution_fixed_octad (a : Fin 24) {z : S24} (hz : z ∈ M23g a) (hz2 : orderOf z = 2) :
    ∃ O : Finset (Fin 24), IsOctad O ∧ a ∈ O ∧ ∀ i, i ∈ O ↔ z i = i := by
  obtain ⟨hzM, hza⟩ := (mem_M23g_iff a z).1 hz
  rcases involution_dichotomy hzM hz2 with ⟨-, -, ⟨O, hO, hOz⟩, -⟩ | ⟨-, -, hfpf⟩
  · exact ⟨O, hO, (hOz a).2 hza, hOz⟩
  · exact absurd hza (hfpf a)

theorem M22g_involution_fixed_octad (a b : Fin 24) {z : S24} (hz : z ∈ M22g a b)
    (hz2 : orderOf z = 2) :
    ∃ O : Finset (Fin 24), IsOctad O ∧ a ∈ O ∧ b ∈ O ∧ ∀ i, i ∈ O ↔ z i = i := by
  obtain ⟨hzM, hza, hzb⟩ := (mem_M22g_iff a b z).1 hz
  rcases involution_dichotomy hzM hz2 with ⟨-, -, ⟨O, hO, hOz⟩, -⟩ | ⟨-, -, hfpf⟩
  · exact ⟨O, hO, (hOz a).2 hza, (hOz b).2 hzb, hOz⟩
  · exact absurd hza (hfpf a)

theorem m23_m22_involution_classes (a b : Fin 24) (hab : a ≠ b) :
    ((∃ z ∈ M23g a, orderOf z = 2) ∧
      (∀ z ∈ M23g a, ∀ z' ∈ M23g a, orderOf z = 2 → orderOf z' = 2 → IsConjIn (M23g a) z z') ∧
      (∀ z ∈ M23g a, orderOf z = 2 →
        ∃ O : Finset (Fin 24), IsOctad O ∧ a ∈ O ∧ ∀ i, i ∈ O ↔ z i = i)) ∧
    ((∃ z ∈ M22g a b, orderOf z = 2) ∧
      (∀ z ∈ M22g a b, ∀ z' ∈ M22g a b, orderOf z = 2 → orderOf z' = 2 →
        IsConjIn (M22g a b) z z') ∧
      (∀ z ∈ M22g a b, orderOf z = 2 →
        ∃ O : Finset (Fin 24), IsOctad O ∧ a ∈ O ∧ b ∈ O ∧ ∀ i, i ∈ O ↔ z i = i)) := by
  exact
    ⟨⟨exists_involution_M23g a,
        (fun z hz z' hz' hz2 hz2' => isConjIn_M23g a hz hz' hz2 hz2'),
        (fun z hz hz2 => M23g_involution_fixed_octad a hz hz2)⟩,
      ⟨exists_involution_M22g a b hab,
        (fun z hz z' hz' hz2 hz2' => isConjIn_M22g a b hab hz hz' hz2 hz2'),
        (fun z hz hz2 => M22g_involution_fixed_octad a b hz hz2)⟩⟩

end Certs

end CFSG.Quasithin.AppendixH.H14
