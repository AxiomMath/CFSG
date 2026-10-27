module

public import CFSG.Quasithin.Background.D2Basic
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin.StabLat

variable {V : Type*} [CommGroup V]

theorem autSub_map_conj_eq {X : Subgroup (MulAut V)} {U : Subgroup V} {t : MulAut V}
    (ht : t ∈ stabSub U) :
    autSub (X.map (MulAut.conj t).toMonoidHom) U =
      (autSub X U).map (MulAut.conj (resHom U ⟨t, ht⟩)).toMonoidHom := by
  ext φ
  rw [Subgroup.mem_map, mem_autSub]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 ha
    refine ⟨resHom U (⟨t, ht⟩⁻¹ * a * ⟨t, ht⟩), mem_autSub.2 ⟨_, ?_, rfl⟩, ?_⟩
    · have e : (a : MulAut V) = t * x * t⁻¹ := hxa.symm
      show t⁻¹ * (a : MulAut V) * t ∈ X
      rw [e]
      simpa [mul_assoc] using hx
    · simp only [map_mul, map_inv, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  · rintro ⟨ψ, hψ, rfl⟩
    obtain ⟨b, hb, rfl⟩ := mem_autSub.1 hψ
    refine ⟨⟨t, ht⟩ * b * ⟨t, ht⟩⁻¹, ⟨b, hb, rfl⟩, ?_⟩
    simp only [map_mul, map_inv, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

end CFSG.Quasithin.StabLat
