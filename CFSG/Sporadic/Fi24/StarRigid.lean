module

public import CFSG.Fischer.NoF25.StarRigid
public import CFSG.Sporadic.Fi24.Edge
public import CFSG.Sporadic.Fi23.Rigid
public import CFSG.Fischer.Polar.Facts
public import CFSG.Sporadic.Fi22.LH.Facts

public section

namespace CFSG.Sporadic.Fi24

open CFSG.Blueprint.Fischer CFSG.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem lift_star_tR
    (g : Fi23.J) : ∃ m : R, m * tR * m⁻¹ = tR ∧ ∀ x y : LocalClass D24 tR,
    (y : R) = m * x * m⁻¹ → (localPoints_tR.χ y : Fi23.J) = g * localPoints_tR.χ x * g⁻¹ := by
  set m0 : MR := fi23EquivJMR.symm g
  refine ⟨(m0 : R), ?_, fun x y hy => ?_⟩
  · have h := commute_tR_of_mem_MR m0.2
    rw [h, mul_inv_cancel_right]
  · have hf' : (m0 : R) * x * (m0 : R)⁻¹ ∈ LocalClass D24 tR := by rw [← hy]; exact y.2
    have e1 := starEquiv_conj m0.2 x hf'
    have e2 : fi23EquivJMR ⟨(m0 : R), m0.2⟩ = g := MulEquiv.apply_symm_apply _ _
    have e3 : y = ⟨(m0 : R) * x * (m0 : R)⁻¹, hf'⟩ := Subtype.ext hy
    rw [e2] at e1
    rw [e3]
    exact e1

theorem starRigid_tR :
    ∀ θ : LocalClass D24 tR ≃ LocalClass D24 tR, StarTau pair_R θ →
    ∃ m : R, m * tR * m⁻¹ = tR ∧ ∀ x, (θ x : R) = m * x * m⁻¹ :=
  starRigid_of_model pair_R Fi23.pair_J localPoints_tR
    (Fi23.tauGroup_D23_eq_range polarFacts hyperovalFacts
      (Fi22.fi22Facts polarFacts hyperovalFacts)) lift_star_tR

theorem exists_conj_of_star_equiv_D24
    {q p : R} (hq : q ∈ D24) (hp : p ∈ D24)
    (θ : LocalClass D24 q ≃ LocalClass D24 p) (hθ : StarTau pair_R θ) :
    ∃ r : R, r * q * r⁻¹ = p ∧ ∀ x, (θ x : R) = r * x * r⁻¹ :=
  exists_conj_of_star_equiv pair_R tR_mem_D24 starRigid_tR hq hp θ hθ

end CFSG.Sporadic.Fi24
