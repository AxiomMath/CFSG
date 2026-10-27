module

public import CFSG.Monster.VisQuot.Monomial
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.Open.LocalVocabulary

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.VisQuot

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts

@[expose] def fixModΩ (P : Subgroup AutPerm) : Submodule (ZMod 2) C where
  carrier := {c | ∀ p ∈ P, permC p c - c ∈ ΩLine}
  add_mem' {a b} ha hb p hp := by
    have h := ΩLine.add_mem (ha p hp) (hb p hp)
    rwa [show permC p a - a + (permC p b - b) = permC p (a + b) - (a + b) by
      rw [map_add]; abel] at h
  zero_mem' p _ := by
    rw [map_zero, sub_zero]
    exact ΩLine.zero_mem
  smul_mem' s a ha p hp := by
    have h := ΩLine.smul_mem s (ha p hp)
    rwa [smul_sub, ← map_smul] at h

theorem mem_fixModΩ {P : Subgroup AutPerm} {c : C} :
    c ∈ fixModΩ P ↔ ∀ p ∈ P, permC p c - c ∈ ΩLine := Iff.rfl

theorem ΩC_mem_fixModΩ (P : Subgroup AutPerm) : ΩC ∈ fixModΩ P := fun p _ => by
  rw [permC_ΩC, sub_self]
  exact ΩLine.zero_mem

@[expose] def commΩ (P : Subgroup AutPerm) : Submodule (ZMod 2) C :=
  Submodule.span (ZMod 2) (insert ΩC {x | ∃ p ∈ P, ∃ c : C, x = permC p c - c})

theorem ΩC_mem_commΩ (P : Subgroup AutPerm) : ΩC ∈ commΩ P :=
  Submodule.subset_span (Set.mem_insert _ _)

theorem permC_sub_mem_commΩ {P : Subgroup AutPerm} {p : AutPerm} (hp : p ∈ P) (c : C) :
    permC p c - c ∈ commΩ P :=
  Submodule.subset_span (Set.mem_insert_of_mem _ ⟨p, hp, c, rfl⟩)

@[expose] def compatC (S : Submodule (ZMod 2) C) : Submodule (ZMod 2) C where
  carrier := {c | ∀ b ∈ S, (c : Fin 24 → ZMod 2) * (b : Fin 24 → ZMod 2) ∈ C}
  add_mem' {x y} hx hy b hb := by
    rw [Submodule.coe_add, add_mul]
    exact C.add_mem (hx b hb) (hy b hb)
  zero_mem' b _ := by
    rw [ZeroMemClass.coe_zero, zero_mul]
    exact C.zero_mem
  smul_mem' s x hx b hb := by
    rw [SetLike.val_smul, smul_mul_assoc]
    exact C.smul_mem s (hx b hb)

theorem mem_compatC {S : Submodule (ZMod 2) C} {c : C} :
    c ∈ compatC S ↔ ∀ b ∈ S, (c : Fin 24 → ZMod 2) * (b : Fin 24 → ZMod 2) ∈ C := Iff.rfl

theorem compatC_anti {S T : Submodule (ZMod 2) C} (h : S ≤ T) : compatC T ≤ compatC S :=
  fun _ hc b hb => hc b (h hb)

theorem ΩC_mem_compatC (S : Submodule (ZMod 2) C) : ΩC ∈ compatC S := fun b _ => by
  have e : (ΩC : Fin 24 → ZMod 2) * (b : Fin 24 → ZMod 2) = b := by
    funext i
    simp [ΩC, Ω]
  rw [e]
  exact b.2

@[expose] def FixBound : Prop :=
  ∀ P : Subgroup AutPerm,
    (∀ p ∈ P, (p : Equiv.Perm (Fin 24)) ∈ CFSG.Monster.B.TwoA.Census.sylowSub) →
    CFSG.Open.IsElemAbelian 2 P →
    ∀ X : Submodule (ZMod 2) C, ΩC ∈ X → X ≤ fixModΩ P →
      Nat.card X * Nat.card P * 2 ^ 11 * Nat.card ↥(compatC X ⊓ fixModΩ P) ≤
        2 ^ 14 * Nat.card ↥(commΩ P ⊔ X ⊔ (compatC X ⊓ fixModΩ P))

end CFSG.Monster.VisQuot
