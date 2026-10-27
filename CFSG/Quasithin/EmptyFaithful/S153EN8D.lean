module

public import CFSG.Quasithin.EmptyFaithful.S153E51A

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153EN8

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

structure BarModel (cx : Ctx15350 T Mc M V₁ V₂ t) where
  L₁ : Subgroup (MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian))
  L₂ : Subgroup (MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian))
  tb : MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian)
  s₁ : MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian)
  s₂ : MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian)
  τ : MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian)
  a₁ : IntMod (VZ T M) cx.c.hyp.elemAbelian
  a₂ : IntMod (VZ T M) cx.c.hyp.elemAbelian
  hS : OfourStruct (autI cx.c.hyp.elemAbelian M) L₁ L₂ tb
  hF : OfourStruct.SylowFacts L₁ L₂ (autI cx.c.hyp.elemAbelian T) s₁ s₂ τ a₁ a₂
  hV₁ : (commV L₁).map (inclMod cx.c.hyp.elemAbelian) = V₁
  hV₂ : (commV L₂).map (inclMod cx.c.hyp.elemAbelian) = V₂

theorem nonempty_barModel (cx : Ctx15350 T Mc M V₁ V₂ t) : Nonempty (BarModel cx) := by
  obtain ⟨L₁, L₂, tb, s₁, s₂, τ, a₁, a₂, hS, hF, hV₁, hV₂⟩ := S153E.exists_bar_model cx
  exact ⟨⟨L₁, L₂, tb, s₁, s₂, τ, a₁, a₂, hS, hF, hV₁, hV₂⟩⟩

variable {cx : Ctx15350 T Mc M V₁ V₂ t}

@[expose] noncomputable def barM (cx : Ctx15350 T Mc M V₁ V₂ t) {x : G} (hx : x ∈ M) :
    MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian) :=
  convI cx.c.hyp.elemAbelian ⟨x, cx.c.hyp.le_normalizer hx⟩

theorem barM_apply_val {x : G} (hx : x ∈ M) (w : IntMod (VZ T M) cx.c.hyp.elemAbelian) :
    (barM cx hx w).val = x * w.val * x⁻¹ :=
  convI_apply_val _ _ _

theorem barM_mul {x y : G} (hx : x ∈ M) (hy : y ∈ M) :
    barM cx (M.mul_mem hx hy) = barM cx hx * barM cx hy := by
  unfold barM
  rw [← map_mul]
  rfl

theorem barM_inv {x : G} (hx : x ∈ M) : barM cx (M.inv_mem hx) = (barM cx hx)⁻¹ := by
  unfold barM
  rw [← map_inv]
  rfl

theorem barM_pow {x : G} (hx : x ∈ M) (n : ℕ) : barM cx (M.pow_mem hx n) = (barM cx hx) ^ n := by
  unfold barM
  rw [← map_pow]
  rfl

theorem barM_eq_one_iff {x : G} (hx : x ∈ M) :
    barM cx hx = 1 ↔ x ∈ Subgroup.centralizer (VZ T M : Set G) :=
  convI_eq_one_iff _ _

theorem barM_mem_autI {x : G} (hx : x ∈ M) : barM cx hx ∈ autI cx.c.hyp.elemAbelian M :=
  convI_mem_autI _ hx _

theorem barM_eq_iff {x y : G} (hx : x ∈ M) (hy : y ∈ M) :
    barM cx hx = barM cx hy ↔ x⁻¹ * y ∈ Subgroup.centralizer (VZ T M : Set G) := by
  have h1 : barM cx hx = barM cx hy ↔ (barM cx hx)⁻¹ * barM cx hy = 1 := by
    rw [inv_mul_eq_one]
  rw [h1, ← barM_inv hx, ← barM_mul (M.inv_mem hx) hy, barM_eq_one_iff]

theorem exists_barM {a : MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian)}
    (ha : a ∈ autI cx.c.hyp.elemAbelian M) : ∃ (x : G) (hx : x ∈ M), barM cx hx = a := by
  obtain ⟨g, hg, rfl⟩ := (mem_autI _).1 ha
  exact ⟨g, hg, rfl⟩

section Pre

variable (B : BarModel cx)

theorem mem_M₂_iff {x : G} :
    x ∈ M ⊓ Subgroup.centralizer (V₁ : Set G) ↔ ∃ hx : x ∈ M, barM cx hx ∈ B.L₂ := by
  have hMN := cx.c.hyp.le_normalizer
  have h := inf_centralizer_eq_preI cx.c.hyp.elemAbelian hMN B.hS.symm
  rw [B.hV₁] at h
  rw [h, mem_preI]
  rfl

theorem mem_M₁_iff {x : G} :
    x ∈ M ⊓ Subgroup.centralizer (V₂ : Set G) ↔ ∃ hx : x ∈ M, barM cx hx ∈ B.L₁ := by
  have hMN := cx.c.hyp.le_normalizer
  have h := inf_centralizer_eq_preI cx.c.hyp.elemAbelian hMN B.hS
  rw [B.hV₂] at h
  rw [h, mem_preI]
  rfl

end Pre

end S153EN8

end CFSG.Quasithin
