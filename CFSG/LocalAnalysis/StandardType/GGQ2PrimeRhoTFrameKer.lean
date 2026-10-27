module

public import CFSG.Fischer.T46Unitary

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Fischer

theorem rhoTFrame_piSU_scalarGL (c : F4ˣ) :
    piSU ⟨scalarGL c, scalarGL_mem c⟩ = 1 := by
  have hz : (⟨scalarGL c, scalarGL_mem c⟩ : SU0) ∈ Subgroup.center SU0 := by
    rw [Subgroup.mem_center_iff]
    intro w
    exact Subtype.ext (scalarGL_central c w).symm
  exact MonoidHom.mem_ker.1 (center_le_ker hz)

private theorem rhoTFrame_card_ker_le :
    Nat.card piSU.ker ≤ 3 := by
  have h1 := card_SU0_eq
  rw [range_piSU, card_T46] at h1
  have h2 := card_SU0_mul_three_le
  have h3 := card_GU0_le
  omega

theorem rhoTFrame_ker_scalar
    {g : SU0} (h : piSU g = 1) :
    ∃ c : F4, c ≠ 0 ∧ ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = c • 1 := by
  let f : F4ˣ → piSU.ker := fun c => ⟨⟨scalarGL c, scalarGL_mem c⟩,
    MonoidHom.mem_ker.2 (rhoTFrame_piSU_scalarGL c)⟩
  have hinj : Function.Injective f := by
    intro c d hcd
    apply scalarGL_injective
    exact congrArg (fun x : piSU.ker => ((x : SU0) : GL (Fin 6) F4)) hcd
  have hcard : Nat.card piSU.ker ≤ Nat.card F4ˣ := by
    have h4 : Nat.card F4 = 4 := by rw [Nat.card_eq_fintype_card, F4.card]
    rw [Nat.card_units, h4]
    have := rhoTFrame_card_ker_le
    omega
  obtain ⟨c, hc⟩ := (hinj.bijective_of_nat_card_le hcard).2 ⟨g, MonoidHom.mem_ker.2 h⟩
  refine ⟨c, c.ne_zero, ?_⟩
  have := congrArg (fun x : piSU.ker => ((x : SU0) : GL (Fin 6) F4)) hc
  change scalarGL c = (g : GL (Fin 6) F4) at this
  rw [← this]
  exact scalarGL_val c

theorem rhoTFrame_conj_mem_SU0 {u g : GL (Fin 6) F4} (hu : u ∈ GU0) (hg : g ∈ SU0) :
    u * g * u⁻¹ ∈ SU0 := by
  have hg' := mem_SU0.1 hg
  refine mem_SU0.2 ⟨?_, GU0.mul_mem (GU0.mul_mem hu (SU0_le_GU0 hg)) (GU0.inv_mem hu)⟩
  rw [map_mul, map_mul, map_inv, hg'.1, mul_one, mul_inv_cancel]

theorem rhoTFrame_commute_scalar
    {u : GU0} {v : SU0} (h : piGU u * piSU v = piSU v * piGU u) :
    ∃ c : F4, c ≠ 0 ∧ ((u : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *
      ((v : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
        c • (((v : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *
          ((u : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)) := by
  let v' : SU0 := ⟨(u : GL (Fin 6) F4) * v * (u : GL (Fin 6) F4)⁻¹,
    rhoTFrame_conj_mem_SU0 u.2 v.2⟩
  have hv' : piSU v' = piSU v := by
    have e : Subgroup.inclusion SU0_le_GU0 v' = u * Subgroup.inclusion SU0_le_GU0 v * u⁻¹ :=
      Subtype.ext rfl
    change piGU (Subgroup.inclusion SU0_le_GU0 v') = piGU (Subgroup.inclusion SU0_le_GU0 v)
    rw [e, map_mul, map_mul, map_inv]
    exact mul_inv_eq_iff_eq_mul.2 h
  have h1 : piSU (v' * v⁻¹) = 1 := by rw [map_mul, map_inv, hv', mul_inv_cancel]
  obtain ⟨c, hc, hX⟩ := rhoTFrame_ker_scalar h1
  refine ⟨c, hc, ?_⟩
  have e : (u : GL (Fin 6) F4) * (v : GL (Fin 6) F4) =
      ((v' * v⁻¹ : SU0) : GL (Fin 6) F4) * ((v : GL (Fin 6) F4) * (u : GL (Fin 6) F4)) := by
    simp only [v', Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have e2 := congrArg (fun g : GL (Fin 6) F4 => (g : Matrix (Fin 6) (Fin 6) F4)) e
  simp only [Units.val_mul] at e2
  rw [e2, hX, Matrix.smul_mul, Matrix.one_mul]

end CFSG.GGQ2Prime
