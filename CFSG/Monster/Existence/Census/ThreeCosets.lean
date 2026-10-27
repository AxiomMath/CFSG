module

public import CFSG.Monster.Existence.Census.SylowReduction
public import CFSG.Monster.B.TwoA.Census.CosetReps
public import CFSG.Monster.B.TwoA.Census.LatticeInv

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence.Census

open CFSG.Monster CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.VisQuot
  CFSG.Monster.Generated CFSG.Monster.ScalarKernel CFSG.Monster.B.TwoA.Census

theorem exists_conj_involution_mem_cosetR
    {f : Gvis} (hf : f * f = 1)
    (hfQ : (f : SpaceB ≃ₗ[ℚ] SpaceB) ∉ rhoQ) :
    ∃ i ∈ ({1, 2, 6} : Finset ℕ), ∃ k : Gvis, k * f * k⁻¹ ∈ cosetR i := by
  set u := piVis f with hu
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective u.unop
  have hu' : u = MulOpposite.op (QuotientGroup.mk g) := by rw [hg, MulOpposite.op_unop]
  have hx : opQHom u = modTwoUnit g := by rw [hu']; exact opQHom_op_mk g
  have hxO : opQHom u ∈ OLvis := hx ▸ modTwoUnit_mem_OLvis g
  have hxx : opQHom u * opQHom u = 1 := by
    rw [← map_mul, hu, ← map_mul, hf, map_one, map_one]
  have hx1 : opQHom u ≠ 1 := by
    intro h
    have h1 : u = 1 := opQHom_injective (h.trans (map_one opQHom).symm)
    apply hfQ
    have h2 : f ∈ piVis.ker := h1
    rw [ker_piVis, Subgroup.mem_subgroupOf] at h2
    exact h2
  obtain ⟨i, hi, w, hw, hwi⟩ := exists_conj_three hxO hxx hx1
  obtain ⟨k₀, hk₀⟩ := mem_OLvis.1 (OLvis.inv_mem hw)
  obtain ⟨s, hs⟩ := exists_mem_Pvis k₀
  let p : Pvis := ⟨(s, k₀), hs⟩
  refine ⟨i, hi, ⟨thetaEquiv p, thetaEquiv_mem_Gvis p⟩, ?_⟩
  rw [mem_cosetR_iff, map_mul, map_mul, map_inv, piVis_thetaEquiv, piVis_cosetRep]
  apply opQHom_injective
  rw [map_mul, map_mul, map_inv]
  have e1 : opQHom (MulOpposite.op (QuotientGroup.mk p.1.2)) = modTwoUnit k₀ := opQHom_op_mk k₀
  rw [e1, opQHom_op_mk (monoAO i), ← hu, hk₀]
  show w⁻¹ * opQHom u * w⁻¹⁻¹ = monoN i
  rw [← hwi]
  group

theorem generated_involutions_three_visible_cosets :
    ∀ t : Gmat, orderOf t = 2 → ∃ c : Gmat, ∃ f : Gvis,
      (f : SpaceB ≃ₗ[ℚ] SpaceB) = ((c * t * c⁻¹ : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) ∧
      f * f = 1 ∧ f ≠ 1 ∧
      ((f : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Qmat ∨ f ∈ cosetR 1 ∨ f ∈ cosetR 2 ∨ f ∈ cosetR 6) := by
  intro t ht
  obtain ⟨c, f, hfc, hff, hf1⟩ := exists_conj_involution_mem_Gvis t ht
  by_cases hfQ : (f : SpaceB ≃ₗ[ℚ] SpaceB) ∈ rhoQ
  · exact ⟨c, f, hfc, hff, hf1, Or.inl hfQ⟩
  · obtain ⟨i, hi, k, hk⟩ := exists_conj_involution_mem_cosetR hff hfQ
    have hkG : (k : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Gmat := Hmat_le_Gmat k.2
    refine ⟨⟨_, hkG⟩ * c, k * f * k⁻¹, ?_, ?_, ?_, ?_⟩
    · have h1 : (f : SpaceB ≃ₗ[ℚ] SpaceB) = (c : SpaceB ≃ₗ[ℚ] SpaceB) * (t : SpaceB ≃ₗ[ℚ] SpaceB) *
          (c : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ := by
        rw [hfc]
        simp
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, h1]
      group
    · calc k * f * k⁻¹ * (k * f * k⁻¹) = k * (f * f) * k⁻¹ := by group
        _ = 1 := by rw [hff]; group
    · intro h
      apply hf1
      have : f = 1 := by
        have h' : k⁻¹ * (k * f * k⁻¹) * k = k⁻¹ * 1 * k := by rw [h]
        simpa [mul_assoc] using h'
      exact this
    · right
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl
      · exact Or.inl hk
      · exact Or.inr (Or.inl hk)
      · exact Or.inr (Or.inr hk)

end CFSG.Monster.Existence.Census
