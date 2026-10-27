module

public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Finset.Attr
public import Mathlib.GroupTheory.QuotientGroup.Defs

public section

namespace CFSG.Quasithin

namespace F53.Stellmacher

namespace S35.B5

namespace GLY

open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def conjY (Y : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (Y : Set G)) :
    ↥Y ≃* ↥Y where
  toFun y := ⟨g * y * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg y).mp y.2⟩
  invFun y := ⟨g⁻¹ * y * g, by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) y).mp y.2
    simpa using this⟩
  left_inv y := Subtype.ext (by simp [mul_assoc])
  right_inv y := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

variable (Y V : Subgroup G) [hN : (V.subgroupOf Y).Normal]

@[expose] def convQ (g : ↥(Subgroup.normalizer (Y : Set G) ⊓ Subgroup.normalizer (V : Set G))) :
    MulAut (↥Y ⧸ V.subgroupOf Y) :=
  QuotientGroup.congr (V.subgroupOf Y) (V.subgroupOf Y) (conjY Y g g.2.1) (by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp g.2.2 x).mp hx
    · intro hy
      refine ⟨(conjY Y g g.2.1).symm y, ?_, (conjY Y g g.2.1).apply_symm_apply y⟩
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ g.2.2) y).mp hy
      simpa [conjY] using this)

theorem convQ_mk (g) (y : ↥Y) :
    convQ Y V g (QuotientGroup.mk y) = QuotientGroup.mk (conjY Y g g.2.1 y) := rfl

@[expose] def convHom : ↥(Subgroup.normalizer (Y : Set G) ⊓ Subgroup.normalizer (V : Set G)) →*
    MulAut (↥Y ⧸ V.subgroupOf Y) where
  toFun := convQ Y V
  map_one' := by
    refine MulEquiv.ext fun a => ?_
    induction a using QuotientGroup.induction_on with
    | H y => exact congrArg QuotientGroup.mk (Subtype.ext (by simp [conjY]))
  map_mul' g h := by
    refine MulEquiv.ext fun a => ?_
    induction a using QuotientGroup.induction_on with
    | H y => exact congrArg QuotientGroup.mk (Subtype.ext (by simp [conjY, mul_assoc]))

theorem convHom_fix_iff (g) (y : ↥Y) :
    convHom Y V g (QuotientGroup.mk y⁻¹) = QuotientGroup.mk y⁻¹ ↔ ⁅(y : G), (g : G)⁆ ∈ V := by
  show convQ Y V g (QuotientGroup.mk y⁻¹) = QuotientGroup.mk y⁻¹ ↔ _
  rw [convQ_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have e : ∀ h : (g : G) ∈ Subgroup.normalizer (Y : Set G),
      ((((conjY Y g h) y⁻¹)⁻¹ * y⁻¹ : ↥Y) : G) = ⁅(y : G), (g : G)⁆⁻¹ := by
    intro h
    simp only [conjY, MulEquiv.coe_mk, Equiv.coe_fn_mk, Subgroup.coe_mul, Subgroup.coe_inv,
      commutatorElement_def]
    group
  rw [e, inv_mem_iff]

theorem convHom_eq_one_iff (g) :
    convHom Y V g = 1 ↔ ∀ y ∈ Y, ⁅y, (g : G)⁆ ∈ V := by
  constructor
  · intro h y hy
    have := (convHom_fix_iff Y V g ⟨y, hy⟩).mp (by rw [h]; rfl)
    exact this
  · intro h
    refine MulEquiv.ext fun a => ?_
    induction a using QuotientGroup.induction_on with
    | H y =>
      have := (convHom_fix_iff Y V g y⁻¹).mpr (h _ (Subgroup.inv_mem _ y.2))
      simpa using this

end GLY

end S35.B5

end F53.Stellmacher

end CFSG.Quasithin
