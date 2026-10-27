module

public import CFSG.Quasithin.Background.B5Statement

public section

namespace CFSG.Quasithin

namespace R3c23

open CFSG.Assembly.LowTwoRank

section Defs

variable {V : Type} [CommGroup V]

@[expose] def fixMod (B : Subgroup (MulAut V)) (W C : Subgroup V) : Subgroup V where
  carrier := {w | w ∈ W ∧ ∀ b ∈ B, b w * w⁻¹ ∈ C}
  one_mem' := ⟨one_mem W, fun b _ => by simp⟩
  mul_mem' := fun {x y} hx hy =>
    ⟨mul_mem hx.1 hy.1, fun b hb => by
      have h : b (x * y) * (x * y)⁻¹ = (b x * x⁻¹) * (b y * y⁻¹) := by
        rw [map_mul, mul_inv_rev]
        ac_rfl
      rw [h]
      exact mul_mem (hx.2 b hb) (hy.2 b hb)⟩
  inv_mem' := fun {x} hx =>
    ⟨inv_mem hx.1, fun b hb => by
      have h : b x⁻¹ * (x⁻¹)⁻¹ = (b x * x⁻¹)⁻¹ := by
        rw [map_inv, inv_inv, mul_inv_rev, inv_inv]
        exact mul_comm _ _
      rw [h]
      exact inv_mem (hx.2 b hb)⟩

theorem mem_fixMod {B : Subgroup (MulAut V)} {W C : Subgroup V} {w : V} :
    w ∈ fixMod B W C ↔ w ∈ W ∧ ∀ b ∈ B, b w * w⁻¹ ∈ C := Iff.rfl

@[expose] def commMod (L : Subgroup (MulAut V)) (W : Subgroup V) : Subgroup V :=
  Subgroup.closure {x | ∃ l ∈ L, ∃ y ∈ W, x = l y * y⁻¹}

structure PairData (G₁ G₂ : Subgroup (MulAut V)) (W₁ W₂ C : Subgroup V) : Prop where
  comm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a
  inf_eq_bot : G₁ ⊓ G₂ = ⊥
  sup_eq_top : W₁ ⊔ W₂ = ⊤
  inf_eq : W₁ ⊓ W₂ = C
  fix_C : ∀ g ∈ G₁ ⊔ G₂, ∀ c ∈ C, g c = c
  inv₁ : ∀ a ∈ G₁, ∀ w ∈ W₁, a w ∈ W₁
  inv₂ : ∀ b ∈ G₂, ∀ w ∈ W₂, b w ∈ W₂
  triv₁ : ∀ b ∈ G₂, ∀ w ∈ W₁, b w = w
  triv₂ : ∀ a ∈ G₁, ∀ w ∈ W₂, a w = w

@[expose] def NatCount (G : Subgroup (MulAut V)) (W C : Subgroup V) : Prop :=
  ∀ B : Subgroup (MulAut V), B ≤ G → IsElemAbelian2 B →
    Nat.card B * Nat.card (fixMod B W C) ≤ Nat.card W

@[expose] def PairOutput (X L₁ L₂ : Subgroup (MulAut V)) : Prop :=
  ∃ (G₁ G₂ : Subgroup (MulAut V)) (W₁ W₂ C : Subgroup V),
    PairData G₁ G₂ W₁ W₂ C ∧ NatCount G₁ W₁ C ∧ NatCount G₂ W₂ C ∧ ffJ X ≤ G₁ ⊔ G₂ ∧
      L₁ ≤ G₁ ∧ L₂ ≤ G₂ ∧ (∃ w ∈ W₁, w ∉ C) ∧
      ∀ w ∈ W₁, (∀ l ∈ L₁, l w * w⁻¹ ∈ C) → w ∈ C

@[expose] def TwoB56Gen (X L₁ L₂ : Subgroup (MulAut V)) : Prop :=
  ∃ (G₁ G₂ : Subgroup (MulAut V)) (W₁ W₂ : Subgroup V),
    ffJ X = G₁ ⊔ G₂ ∧ G₁ ⊓ G₂ = ⊥ ∧ (∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) ∧ L₁ ≤ G₁ ∧ L₂ ≤ G₂ ∧
      (G₁ = L₁ ∨ (Nonempty (↥G₁ ≃* Equiv.Perm (Fin 5)) ∧ Nat.card ↥L₁ = 60)) ∧
      (G₂ = L₂ ∨ (Nonempty (↥G₂ ≃* Equiv.Perm (Fin 5)) ∧ Nat.card ↥L₂ = 60)) ∧
      fixV (G₁ ⊔ G₂) ≤ W₁ ∧ fixV (G₁ ⊔ G₂) ≤ W₂ ∧ W₁ ⊔ W₂ = ⊤ ∧ W₁ ⊓ W₂ = fixV (G₁ ⊔ G₂) ∧
      B56Piece G₁ W₁ (fixV (G₁ ⊔ G₂)) ∧ B56Piece G₂ W₂ (fixV (G₁ ⊔ G₂))

end Defs

@[expose] def SL2PieceFacts : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (L : Subgroup (MulAut V)) (W C : Subgroup V) (m : ℕ),
    BinaryNaturalSL L W C 2 m →
      NatCount L W C ∧ C ≤ W ∧ (∃ w ∈ W, w ∉ C) ∧
        (∀ w ∈ W, (∀ l ∈ L, l w * w⁻¹ ∈ C) → w ∈ C) ∧ W ≤ commMod L W ⊔ C

@[expose] def Sym5PieceFacts : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)) (W C : Subgroup V),
    SymmetricNatural G W C 5 → L ≤ G → Nat.card ↥L = 60 →
      NatCount G W C ∧ C ≤ W ∧ (∃ w ∈ W, w ∉ C) ∧
        (∀ w ∈ W, (∀ l ∈ L, l w * w⁻¹ ∈ C) → w ∈ C) ∧ W ≤ commMod L W ⊔ C

@[expose] def Lin2Cover (L : Type) [Group L] : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (n : ℕ), 2 ≤ n ∧ Nat.card F = 2 ^ n ∧
    Nonempty (L ≃* ↥(StatedSL 2 F))

end R3c23

end CFSG.Quasithin
