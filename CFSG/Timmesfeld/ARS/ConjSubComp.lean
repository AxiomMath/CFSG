module

public import CFSG.Timmesfeld.ARS.Defs
import CFSG.Timmesfeld.RankOne.Basic

public section

namespace CFSG.Timmesfeld.ARS

variable {G K : Type*} [Group G] [Group K]

theorem map_conjSub_comp_conj (Φ : G →* K) (R : Subgroup G) (x y : G) :
    (conjSub R y).map (Φ.comp (MulAut.conj x).toMonoidHom) = (conjSub R (x * y)).map Φ := by
  rw [conjSub, conjSub, CFSG.Timmesfeld.RankOne.map_conj_mul]
  rw [Subgroup.map_map (K := R) (g := (MulAut.conj x).toMonoidHom)
      (f := (MulAut.conj y).toMonoidHom),
    Subgroup.map_map (K := R) (g := Φ)
      (f := ((MulAut.conj x).toMonoidHom).comp ((MulAut.conj y).toMonoidHom)),
    Subgroup.map_map (K := R) (g := Φ.comp (MulAut.conj x).toMonoidHom)
      (f := (MulAut.conj y).toMonoidHom)]
  rfl

theorem range_comp_conj (Φ : G →* K) (x : G) :
    (Φ.comp (MulAut.conj x).toMonoidHom).range = Φ.range := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulAut.conj x).surjective,
    ← MonoidHom.range_eq_map]

theorem exists_eq_map_conjSub_comp_conj_iff (Φ : G →* K) (R : Subgroup G) (x : G)
    (U : Subgroup K) :
    (∃ y, U = (conjSub R y).map (Φ.comp (MulAut.conj x).toMonoidHom)) ↔
      ∃ y, U = (conjSub R y).map Φ := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨x * y, map_conjSub_comp_conj Φ R x y⟩
  · rintro ⟨y, rfl⟩
    exact ⟨x⁻¹ * y, by rw [map_conjSub_comp_conj, mul_inv_cancel_left]⟩

end CFSG.Timmesfeld.ARS
