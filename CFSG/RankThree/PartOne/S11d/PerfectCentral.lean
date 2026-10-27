module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeGroup

public section

namespace CFSG.RankThree.PartOne

open Subgroup

theorem hom_eq_of_div_central {Q Γ : Type*} [Group Q] [Group Γ] (hQ : Group.IsPerfect Q)
    (f₁ f₂ : Q →* Γ) (h : ∀ q, f₁ q * (f₂ q)⁻¹ ∈ Subgroup.center Γ) : f₁ = f₂ := by
  let u : Q →* Subgroup.center Γ :=
    { toFun := fun q => ⟨f₁ q * (f₂ q)⁻¹, h q⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun q₁ q₂ => by
        apply Subtype.ext
        have hc : f₁ q₁ * (f₁ q₂ * (f₂ q₂)⁻¹) = (f₁ q₂ * (f₂ q₂)⁻¹) * f₁ q₁ :=
          Subgroup.mem_center_iff.mp (h q₂) (f₁ q₁)
        have hc' : (f₁ q₁ * (f₂ q₁)⁻¹) * (f₁ q₂ * (f₂ q₂)⁻¹) =
            (f₁ q₂ * (f₂ q₂)⁻¹) * (f₁ q₁ * (f₂ q₁)⁻¹) :=
          Subgroup.mem_center_iff.mp (h q₂) _
        show f₁ (q₁ * q₂) * (f₂ (q₁ * q₂))⁻¹ = (f₁ q₁ * (f₂ q₁)⁻¹) * (f₁ q₂ * (f₂ q₂)⁻¹)
        rw [map_mul, map_mul, mul_inv_rev]
        calc f₁ q₁ * f₁ q₂ * ((f₂ q₂)⁻¹ * (f₂ q₁)⁻¹)
            = (f₁ q₁ * (f₁ q₂ * (f₂ q₂)⁻¹)) * (f₂ q₁)⁻¹ := by group
          _ = ((f₁ q₂ * (f₂ q₂)⁻¹) * f₁ q₁) * (f₂ q₁)⁻¹ := by rw [hc]
          _ = (f₁ q₂ * (f₂ q₂)⁻¹) * (f₁ q₁ * (f₂ q₁)⁻¹) := by group
          _ = (f₁ q₁ * (f₂ q₁)⁻¹) * (f₁ q₂ * (f₂ q₂)⁻¹) := hc'.symm }
  have hu := KCUnitary.eq_one_of_perfect_of_comm hQ
    (fun a b : Subgroup.center Γ => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a)) u
  ext q
  have := congrArg Subtype.val (hu q)
  exact mul_inv_eq_one.mp this


theorem commute_of_commutator_central {Γ : Type*} [Group Γ] {Q : Subgroup Γ}
    (hQ : Group.IsPerfect ↥Q) {G : Γ} (h : ∀ q ∈ Q, G * q * G⁻¹ * q⁻¹ ∈ Subgroup.center Γ) :
    ∀ q ∈ Q, G * q = q * G := by
  have h1 := hom_eq_of_div_central hQ ((MulAut.conj G).toMonoidHom.comp Q.subtype) Q.subtype
    (fun q => h q q.2)
  intro q hq
  have := congrArg (fun f : ↥Q →* Γ => f ⟨q, hq⟩) h1
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    Subgroup.coe_subtype] at this
  calc G * q = G * q * G⁻¹ * G := by group
    _ = q * G := by rw [this]

end CFSG.RankThree.PartOne
