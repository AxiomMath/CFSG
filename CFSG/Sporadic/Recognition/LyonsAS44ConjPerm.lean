module

public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Data.Finset.Attr

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Subgroup

variable {G : Type*} [Group G]

@[expose] def conjSub (g : G) (B : Subgroup G) : Subgroup G := B.map (MulAut.conj g).toMonoidHom

theorem mem_conjSub_iff {g : G} {B : Subgroup G} {x : G} : x ∈ conjSub g B ↔ g⁻¹ * x * g ∈ B := by
  constructor
  · rintro ⟨b, hb, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hb
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem conjSub_one (B : Subgroup G) : conjSub 1 B = B := by
  ext x
  simp [mem_conjSub_iff]

theorem conjSub_mul (g h : G) (B : Subgroup G) : conjSub (g * h) B = conjSub g (conjSub h B) := by
  ext x
  simp only [mem_conjSub_iff]
  have : (g * h)⁻¹ * x * (g * h) = h⁻¹ * (g⁻¹ * x * g) * h := by group
  rw [this]

theorem conjSub_zpowers (g a : G) : conjSub g (zpowers a) = zpowers (g * a * g⁻¹) := by
  rw [conjSub, MonoidHom.map_zpowers]
  rfl

theorem conjSub_inv_conjSub (g : G) (B : Subgroup G) : conjSub g⁻¹ (conjSub g B) = B := by
  rw [← conjSub_mul, inv_mul_cancel, conjSub_one]

theorem conjSub_conjSub_inv (g : G) (B : Subgroup G) : conjSub g (conjSub g⁻¹ B) = B := by
  rw [← conjSub_mul, mul_inv_cancel, conjSub_one]

@[expose] def conjPerm (Q : Subgroup G) (Ω : Set (Subgroup G))
    (h : ∀ g ∈ Q, ∀ B ∈ Ω, conjSub g B ∈ Ω) : Q →* Equiv.Perm Ω where
  toFun g :=
    { toFun := fun B => ⟨conjSub (g : G) B.1, h g g.2 B.1 B.2⟩
      invFun := fun B => ⟨conjSub (g : G)⁻¹ B.1, h _ (Q.inv_mem g.2) B.1 B.2⟩
      left_inv := fun B => Subtype.ext (conjSub_inv_conjSub _ _)
      right_inv := fun B => Subtype.ext (conjSub_conjSub_inv _ _) }
  map_one' := by
    refine Equiv.ext fun B => Subtype.ext ?_
    exact conjSub_one B.1
  map_mul' g g' := by
    refine Equiv.ext fun B => Subtype.ext ?_
    exact conjSub_mul (g : G) (g' : G) B.1

end CFSG.Sporadic.Recognition.LyonsSims
