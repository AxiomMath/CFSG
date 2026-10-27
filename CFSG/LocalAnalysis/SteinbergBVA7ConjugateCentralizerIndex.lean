module

public import CFSG.Foundations.Basic

public section

namespace CFSG.LocalAnalysis.SteinbergBV

open Subgroup CFSG

variable {G : Type*} [Group G]

theorem conjugate_inf_centralizer_eq {Q A : Subgroup G} {k : G} (hQk : CFSG.conjugate Q k = Q) :
    (Q ⊓ centralizer (A : Set G)).map (MulAut.conj k⁻¹).toMonoidHom =
      Q ⊓ centralizer (CFSG.conjugate A k : Set G) := by
  rw [Subgroup.map_inf _ _ _ (MulAut.conj k⁻¹).injective]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_iff] at hy
    rw [mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show k⁻¹ * a * k⁻¹⁻¹ * (k⁻¹ * y * k⁻¹⁻¹) = k⁻¹ * (a * y) * k⁻¹⁻¹ by group, hy a ha]
    group
  · intro hx
    refine ⟨k⁻¹⁻¹ * x * k⁻¹, ?_, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
    rw [mem_centralizer_iff] at hx
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro a ha
    have h := hx (k⁻¹ * a * k⁻¹⁻¹) ⟨a, ha, rfl⟩
    calc a * (k⁻¹⁻¹ * x * k⁻¹) = k⁻¹⁻¹ * ((k⁻¹ * a * k⁻¹⁻¹) * x) * k⁻¹ := by group
      _ = k⁻¹⁻¹ * (x * (k⁻¹ * a * k⁻¹⁻¹)) * k⁻¹ := by rw [h]
      _ = k⁻¹⁻¹ * x * k⁻¹ * a := by group

theorem two_conjugate_centralizer_index_extracts_fixed_factor [Finite G] {Q K A U : Subgroup G}
    {k : G} (hQk : CFSG.conjugate Q k = Q) (hK : K ≤ A ⊔ CFSG.conjugate A k)
    (hUQ : U ≤ Q ⊓ centralizer (Q : Set G)) {m : ℕ} (hm : 1 ≤ m)
    (hA : (Q ⊓ centralizer (A : Set G)).relIndex Q = m)
    (hUK : (U ⊓ centralizer (K : Set G)).relIndex U = m ^ 2) :
    U ⊔ (Q ⊓ centralizer (K : Set G)) = Q ∧
    Q ⊓ centralizer (K : Set G) =
      (Q ⊓ centralizer (A : Set G)) ⊓ (Q ⊓ centralizer (CFSG.conjugate A k : Set G)) ∧
    Q ⊓ centralizer (K : Set G) ≤ centralizer (A : Set G) := by
  have hne : ∀ H L : Subgroup G, H.relIndex L ≠ 0 := fun H L => Subgroup.index_ne_zero_of_finite
  set CK := Q ⊓ centralizer (K : Set G) with hCK
  set CA := Q ⊓ centralizer (A : Set G) with hCA
  set CAk := Q ⊓ centralizer (CFSG.conjugate A k : Set G) with hCAk
  have hUQ' : U ≤ Q := hUQ.trans inf_le_left
  have hAk : CAk.relIndex Q = m := by
    have h := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj k⁻¹).toMonoidHom) CA Q
      (MulAut.conj k⁻¹).injective
    rw [hCA, conjugate_inf_centralizer_eq hQk] at h
    have hQ' : Q.map (MulAut.conj k⁻¹).toMonoidHom = Q := hQk
    rw [hQ'] at h
    rw [h, ← hCA, hA]
  have hDCK : CA ⊓ CAk ≤ CK := by
    intro x hx
    obtain ⟨⟨hxQ, hxA⟩, ⟨-, hxAk⟩⟩ := hx
    refine ⟨hxQ, mem_centralizer_iff.2 fun y hy => ?_⟩
    have hle : A ⊔ CFSG.conjugate A k ≤ centralizer {x} := sup_le
      (fun a ha => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hxA a ha))
      (fun a ha => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hxAk a ha))
    exact mem_centralizer_singleton_iff.1 (hle (hK hy))
  have hDQ : CA ⊓ CAk ≤ Q := inf_le_left.trans inf_le_left
  have hCKQ : CK ≤ Q := inf_le_left
  have hDle : (CA ⊓ CAk).relIndex Q ≤ m ^ 2 := by
    have h := Subgroup.relIndex_inf_le (H := CA) (K := CAk) (L := Q)
    rw [hA, hAk] at h
    rw [sq]
    exact h
  have hUCK : CK.relIndex U = m ^ 2 := by
    rw [← Subgroup.inf_relIndex_right, ← hUK]
    congr 1
    rw [hCK, inf_comm, ← inf_assoc, inf_of_le_left hUQ']
  have hCKge : m ^ 2 ≤ CK.relIndex Q := by
    rw [← hUCK]
    exact Subgroup.relIndex_le_of_le_right hUQ' (hne _ _)
  have hm2 : 0 < m ^ 2 := pow_pos hm 2
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hDCK hCKQ
  have hDCKone : (CA ⊓ CAk).relIndex CK = 1 := by
    have h1 : (CA ⊓ CAk).relIndex CK * CK.relIndex Q ≤ m ^ 2 := hmul ▸ hDle
    have h2 : (CA ⊓ CAk).relIndex CK ≠ 0 := hne _ _
    have h3 : (CA ⊓ CAk).relIndex CK * m ^ 2 ≤ m ^ 2 :=
      (Nat.mul_le_mul_left _ hCKge).trans h1
    have h4 : (CA ⊓ CAk).relIndex CK ≤ 1 := by
      by_contra hcon
      push Not at hcon
      have : 2 * m ^ 2 ≤ (CA ⊓ CAk).relIndex CK * m ^ 2 := Nat.mul_le_mul_right _ hcon
      omega
    omega
  have hCKD : CK = CA ⊓ CAk := le_antisymm (Subgroup.relIndex_eq_one.1 hDCKone) hDCK
  have hWQ : U ⊔ CK ≤ Q := sup_le hUQ' hCKQ
  have hCKW : CK ≤ U ⊔ CK := le_sup_right
  have hmul2 := Subgroup.relIndex_mul_relIndex _ _ _ hCKW hWQ
  have hCKQle : CK.relIndex Q ≤ m ^ 2 := by
    rw [hCKD]
    exact hDle
  have hW : (U ⊔ CK).relIndex Q = 1 := by
    have h1 : m ^ 2 ≤ CK.relIndex (U ⊔ CK) := by
      rw [← hUCK]
      exact Subgroup.relIndex_le_of_le_right le_sup_left (hne _ _)
    have h2 : (U ⊔ CK).relIndex Q ≠ 0 := hne _ _
    have h3 : m ^ 2 * (U ⊔ CK).relIndex Q ≤ m ^ 2 :=
      (Nat.mul_le_mul_right _ h1).trans (hmul2 ▸ hCKQle)
    have h4 : (U ⊔ CK).relIndex Q ≤ 1 := by
      by_contra hcon
      push Not at hcon
      have : m ^ 2 * 2 ≤ m ^ 2 * (U ⊔ CK).relIndex Q := Nat.mul_le_mul_left _ hcon
      omega
    omega
  refine ⟨le_antisymm hWQ (Subgroup.relIndex_eq_one.1 hW), hCKD, ?_⟩
  rw [hCKD]
  exact inf_le_left.trans inf_le_right

end CFSG.LocalAnalysis.SteinbergBV
