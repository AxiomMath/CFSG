module

public import CFSG.Monster.Existence.TwoPoint.ShapeSixCover

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8

theorem shapeSix_uGriess_ne_one : uGriess ≠ 1 := by
  intro h
  have h2 : rhoEquiv rTwo = rhoEquiv 1 :=
    (congrArg Subtype.val h).trans Short.rhoEquiv_one.symm
  exact ne_one_of_isShortCoord isShortCoord_rTwo (rhoEquiv_injective h2)

theorem shapeSix_orderOf_uGriess : orderOf uGriess = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [sq]; exact uGriess_mul_self) shapeSix_uGriess_ne_one

theorem shapeSix_isConj_tGriess_of_trace
    {g : MGriess} (hg : orderOf g = 2)
    (htr : LinearMap.trace ℚ SpaceB ((g : SpaceB ≃ₗ[ℚ] SpaceB) : SpaceB →ₗ[ℚ] SpaceB) = 4372) :
    IsConj tGriess g := by
  rcases (involution_classes_MGriess_of_Gmat Census.generated_group_two_involution_classes).1 g hg
    with h | h
  · have := trace_eq_of_isConj_MGriess h
    rw [trace_xGriess, htr] at this
    norm_num at this
  · exact h

theorem shapeSix_isConj_tGriess_uGriess :
    IsConj tGriess uGriess :=
  shapeSix_isConj_tGriess_of_trace shapeSix_orderOf_uGriess
    (trace_of_mem_FE right_mem_kleinSubgroup shapeSix_uGriess_ne_one)

theorem shapeSix_uGriess_mem_cent : uGriess ∈ cent tGriess :=
  Subgroup.mem_centralizer_singleton_iff.2 tGriess_mul_uGriess.symm

@[expose] noncomputable def uGriessCent : cent tGriess := ⟨uGriess, shapeSix_uGriess_mem_cent⟩

theorem centToShat_uGriessCent
    (hG : Gmat = AutO) :
    ((centToShat hG uGriessCent : Shat) : Dfull) = cQ := by
  rw [coe_centToShat]
  exact (short_quadratic_involution_data.1).symm

theorem exists_lift_of_conj
    (hG : Gmat = AutO) {c : Shat}
    (hc : ∃ g : Shat, (c : Dfull) = (g : Dfull)⁻¹ * cQ * g) :
    ∃ ĉ : cent tGriess, centToShat hG ĉ = c ∧ (ĉ : MGriess) * ĉ = 1 ∧
      IsConj tGriess (ĉ : MGriess) := by
  obtain ⟨g, hg⟩ := hc
  obtain ⟨ĝ, rfl⟩ := centToShat_surjective hG g
  refine ⟨ĝ⁻¹ * uGriessCent * ĝ, Subtype.ext ?_, ?_, ?_⟩
  · rw [hg]
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, centToShat_uGriessCent]
  · show ((ĝ : MGriess)⁻¹ * uGriess * ĝ) * ((ĝ : MGriess)⁻¹ * uGriess * ĝ) = 1
    calc ((ĝ : MGriess)⁻¹ * uGriess * ĝ) * ((ĝ : MGriess)⁻¹ * uGriess * ĝ)
        = (ĝ : MGriess)⁻¹ * (uGriess * uGriess) * ĝ := by group
      _ = 1 := by rw [uGriess_mul_self]; group
  · refine shapeSix_isConj_tGriess_uGriess.trans (isConj_iff.2 ⟨(ĝ : MGriess)⁻¹, ?_⟩)
    show (ĝ : MGriess)⁻¹ * uGriess * ((ĝ : MGriess)⁻¹)⁻¹ = (ĝ : MGriess)⁻¹ * uGriess * ĝ
    rw [inv_inv]

end CFSG.Monster.Existence
