
module

public import CFSG.Quasithin.Background.B4Models

public section

namespace CFSG.Quasithin

namespace FFModel

structure IsActionModel (D : FFModel) : Prop where
  act_mul : ∀ (γ : D.Gam) (x y : D.Amb), D.act γ (x * y) = D.act γ x * D.act γ y
  act_one : ∀ x : D.Amb, D.act 1 x = x
  act_mul_act : ∀ (γ δ : D.Gam) (x : D.Amb), D.act (γ * δ) x = D.act γ (D.act δ x)
  sec_inv : ∀ (γ : D.Gam), ∀ m ∈ D.sec, D.act γ m ∈ D.sec
  ker_inv : ∀ (γ : D.Gam), ∀ m ∈ D.ker, D.act γ m ∈ D.ker
  ker_le : D.ker ≤ D.sec

abbrev Mod (D : FFModel) : Type := ↥D.sec ⧸ D.ker.subgroupOf D.sec

namespace IsActionModel

variable {D : FFModel} (h : D.IsActionModel)

include h

theorem act_inv_act (γ : D.Gam) (x : D.Amb) : D.act γ⁻¹ (D.act γ x) = x := by
  rw [← h.act_mul_act, inv_mul_cancel, h.act_one]

theorem act_act_inv (γ : D.Gam) (x : D.Amb) : D.act γ (D.act γ⁻¹ x) = x := by
  rw [← h.act_mul_act, mul_inv_cancel, h.act_one]

@[expose] def actSec (γ : D.Gam) : ↥D.sec →* ↥D.sec where
  toFun m := ⟨D.act γ (m : D.Amb), h.sec_inv γ m m.2⟩
  map_one' := by
    apply Subtype.ext
    show D.act γ 1 = 1
    have h11 := h.act_mul γ 1 1
    rw [mul_one] at h11
    exact (mul_left_cancel (a := D.act γ 1) (by rw [mul_one]; exact h11)).symm
  map_mul' m n := Subtype.ext (h.act_mul γ m n)

@[expose] def modEnd (γ : D.Gam) : D.Mod →* D.Mod :=
  QuotientGroup.map (D.ker.subgroupOf D.sec) (D.ker.subgroupOf D.sec) (h.actSec γ) (by
    intro m hm
    exact h.ker_inv γ m hm)

theorem modEnd_mk (γ : D.Gam) (m : ↥D.sec) :
    h.modEnd γ (QuotientGroup.mk m) = QuotientGroup.mk (h.actSec γ m) := rfl

theorem modEnd_one : h.modEnd 1 = MonoidHom.id D.Mod := by
  ext m
  show h.modEnd 1 (QuotientGroup.mk m) = QuotientGroup.mk m
  rw [modEnd_mk]
  congr 1
  exact Subtype.ext (h.act_one m)

theorem modEnd_mul (γ δ : D.Gam) : h.modEnd (γ * δ) = (h.modEnd γ).comp (h.modEnd δ) := by
  ext m
  show h.modEnd (γ * δ) (QuotientGroup.mk m) =
    h.modEnd γ (h.modEnd δ (QuotientGroup.mk m))
  rw [modEnd_mk, modEnd_mk, modEnd_mk]
  congr 1
  exact Subtype.ext (h.act_mul_act γ δ m)

@[expose] def modAct : D.Gam →* MulAut D.Mod where
  toFun γ :=
    { toFun := h.modEnd γ
      invFun := h.modEnd γ⁻¹
      left_inv := fun q => by
        have := congrArg (fun f => f q) (h.modEnd_mul γ⁻¹ γ).symm
        simp only [MonoidHom.comp_apply, inv_mul_cancel, modEnd_one, MonoidHom.id_apply] at this
        exact this
      right_inv := fun q => by
        have := congrArg (fun f => f q) (h.modEnd_mul γ γ⁻¹).symm
        simp only [MonoidHom.comp_apply, mul_inv_cancel, modEnd_one, MonoidHom.id_apply] at this
        exact this
      map_mul' := (h.modEnd γ).map_mul }
  map_one' := by
    ext q
    exact congrArg (fun f => f q) h.modEnd_one
  map_mul' γ δ := by
    ext q
    exact congrArg (fun f => f q) (h.modEnd_mul γ δ)

theorem modAct_apply (γ : D.Gam) (q : D.Mod) : h.modAct γ q = h.modEnd γ q := rfl

theorem realizesMod_range : D.RealizesMod h.modAct.range := by
  refine ⟨h.modAct.rangeRestrict, MonoidHom.rangeRestrict_surjective _, le_top, h.ker_le,
    fun _ u _ => trivial, fun _ z hz => by simpa using hz, h.sec_inv, h.ker_inv, ?_⟩
  refine ⟨Subgroup.topEquiv.toMonoidHom, fun q => ⟨⟨q, trivial⟩, rfl⟩, fun u => ?_, ?_⟩
  · simp only [Subgroup.mem_bot]
    rfl
  · intro γ u m hu hm hum
    have hu' : (u : D.Mod) = QuotientGroup.mk m := hum
    show h.modAct γ (u : D.Mod) = QuotientGroup.mk ⟨D.act γ (m : D.Amb), hm⟩
    rw [hu', modAct_apply, modEnd_mk]
    rfl

end IsActionModel

end FFModel

end CFSG.Quasithin
