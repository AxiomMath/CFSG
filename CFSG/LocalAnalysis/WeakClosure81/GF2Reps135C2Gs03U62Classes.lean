module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaAut

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.EvenSmallLie.UnitarySix.Yamada
open CFSG.EvenSmallLie.UnitarySix
open CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwoAut

theorem gs03_u62_outer_classes {Q : Type} [Group Q]
    (hQ : CFSG.Blueprint.LieModel Q .PSU 6 2 1) :
    ∃ ρ₁ ρ₂ : MulAut Q, ∀ α : MulAut Q, α * α = 1 → α ∉ inner Q →
      IsConj ρ₁ α ∨ IsConj ρ₂ α := by
  obtain ⟨F, _, h, ⟨φ⟩⟩ := exists_sixQ_mulEquiv hQ
  obtain ⟨ω, hω⟩ := exists_omega h
  refine ⟨(MulAut.congr φ).symm (sigmaQ h), (MulAut.congr φ).symm (alphaOne h), ?_⟩
  intro α hα hout
  set α' : MulAut (sixQ h) := MulAut.congr φ α with hα'def
  have hα'2 : α' * α' = 1 := by
    rw [hα'def, ← map_mul, hα, map_one]
  have hα'ne : α' ≠ 1 := by
    intro h1
    apply hout
    have hα_one : α = 1 := (MulAut.congr φ).injective (by rw [← hα'def, h1, map_one])
    exact ⟨1, by rw [hα_one, map_one]⟩
  have hα'ord : orderOf α' = 2 :=
    orderOf_eq_prime (by rw [sq, hα'2]) hα'ne
  obtain ⟨A, hA⟩ := exists_conj_eq_of_orderOf_eq_two h ω hω α' hα'ord
  set c : MulAut (sixQ h) :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom h _ A with hc
  rcases hA with ⟨k, -, hkconj⟩ | hσ | hα1
  · have hinnerα' : α' ∈ inner (sixQ h) := by
      have hα'eq : α' = c⁻¹ * MulAut.conj (sixProj h (tElt h k)) * c := by
        calc α' = c⁻¹ * (c * α' * c⁻¹) * c := by group
             _ = c⁻¹ * MulAut.conj (sixProj h (tElt h k)) * c := by rw [hkconj]
      have hconj_inv : c⁻¹ * MulAut.conj (sixProj h (tElt h k)) * c =
          MulAut.conj (c⁻¹ (sixProj h (tElt h k))) := by
        ext u
        simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
          MulAut.inv_apply_self, MulAut.apply_inv_self]
      refine ⟨c⁻¹ (sixProj h (tElt h k)), ?_⟩
      rw [← hconj_inv, hα'eq]
    have hinnerα : α ∈ inner Q := by
      have hmap := Subgroup.mem_map_iff_mem (f := (MulAut.congr φ).toMonoidHom)
        (K := inner Q) (x := α) (MulAut.congr φ).injective
      rw [← hmap, CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr φ]
      simpa [hα'def] using hinnerα'
    exact absurd hinnerα hout
  · have hsymm : (MulAut.congr φ).symm α' = α := by
      rw [hα'def]
      exact MulEquiv.symm_apply_apply (MulAut.congr φ) α
    have h1 : (MulAut.congr φ).symm (sigmaQ h) =
        (MulAut.congr φ).symm c * α * ((MulAut.congr φ).symm c)⁻¹ := by
      rw [← hσ, map_mul, map_mul, map_inv, hsymm]
    exact Or.inl (isConj_iff.mpr ⟨((MulAut.congr φ).symm c)⁻¹, by rw [h1]; group⟩)
  · have hsymm : (MulAut.congr φ).symm α' = α := by
      rw [hα'def]
      exact MulEquiv.symm_apply_apply (MulAut.congr φ) α
    have h1 : (MulAut.congr φ).symm (alphaOne h) =
        (MulAut.congr φ).symm c * α * ((MulAut.congr φ).symm c)⁻¹ := by
      rw [← hα1, map_mul, map_mul, map_inv, hsymm]
    exact Or.inr (isConj_iff.mpr ⟨((MulAut.congr φ).symm c)⁻¹, by rw [h1]; group⟩)

end CFSG.LocalAnalysis.WeakClosure81
