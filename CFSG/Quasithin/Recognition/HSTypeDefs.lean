module

public import CFSG.Open.QuasithinDefs

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open
open scoped MatrixGroups

@[expose] def z4Q8Q8Ident :
    Subgroup (Multiplicative (ZMod 4) × QuaternionGroup 2 × QuaternionGroup 2) :=
  Subgroup.closure {(Multiplicative.ofAdd 2, QuaternionGroup.a 2, 1),
    (Multiplicative.ofAdd 2, 1, QuaternionGroup.a 2)}

private theorem quaternion_a_two_central :
    ∀ q : QuaternionGroup 2, q * QuaternionGroup.a 2 = QuaternionGroup.a 2 * q := by
  decide

private theorem z4Q8Q8Ident_gens_central
    (g : Multiplicative (ZMod 4) × QuaternionGroup 2 × QuaternionGroup 2) :
    g * (Multiplicative.ofAdd 2, QuaternionGroup.a 2, 1) =
        (Multiplicative.ofAdd 2, QuaternionGroup.a 2, 1) * g ∧
      g * (Multiplicative.ofAdd 2, 1, QuaternionGroup.a 2) =
        (Multiplicative.ofAdd 2, 1, QuaternionGroup.a 2) * g := by
  obtain ⟨g₁, g₂, g₃⟩ := g
  refine ⟨Prod.ext (mul_comm _ _) (Prod.ext (quaternion_a_two_central g₂) ?_),
    Prod.ext (mul_comm _ _) (Prod.ext ?_ (quaternion_a_two_central g₃))⟩ <;>
  simp

instance z4Q8Q8Ident_normal : z4Q8Q8Ident.Normal := by
  have hle : z4Q8Q8Ident ≤ Subgroup.center _ := by
    rw [z4Q8Q8Ident, Subgroup.closure_le]
    rintro x (rfl | rfl) <;> rw [SetLike.mem_coe, Subgroup.mem_center_iff] <;> intro g
    · exact (z4Q8Q8Ident_gens_central g).1
    · exact (z4Q8Q8Ident_gens_central g).2
  exact ⟨fun n hn g => by
    have hc := Subgroup.mem_center_iff.mp (hle hn) g
    rw [hc, mul_inv_cancel_right]
    exact hn⟩

abbrev Z4Q8Q8 : Type :=
  (Multiplicative (ZMod 4) × QuaternionGroup 2 × QuaternionGroup 2) ⧸ z4Q8Q8Ident

@[expose] def IsZ4Q8Q8 (P : Type*) [Group P] : Prop :=
  Nonempty (P ≃* Z4Q8Q8)

@[expose] def IsZ4Cube (P : Type*) [Group P] : Prop :=
  Nonempty (P ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4) × Multiplicative (ZMod 4))

variable {G : Type*} [Group G]

structure HSOne (z : G) : Prop where
  fstar : IsZ4Q8Q8 ↥(quasithinGenFitting (Subgroup.centralizer ({z} : Set G)))
  quot : ∃ φ : ↥(Subgroup.centralizer ({z} : Set G)) →* Equiv.Perm (Fin 5),
    Function.Surjective φ ∧
      φ.ker = (quasithinGenFitting (Subgroup.centralizer ({z} : Set G))).subgroupOf
        (Subgroup.centralizer ({z} : Set G))

structure HSTwo (z : G) (V : Subgroup G) : Prop where
  le : V ≤ quasithinGenFitting (Subgroup.centralizer ({z} : Set G))
  fstar : IsZ4Cube ↥(quasithinGenFitting (Subgroup.normalizer (V : Set G)))
  quot : ∃ θ : ↥(Subgroup.normalizer (V : Set G)) →* SL(3, ZMod 2), Function.Surjective θ ∧
    θ.ker = (quasithinGenFitting (Subgroup.normalizer (V : Set G))).subgroupOf
      (Subgroup.normalizer (V : Set G))

@[expose] def IsTypeHS (G : Type*) [Group G] : Prop :=
  ∃ (z : G) (V : Subgroup G), orderOf z = 2 ∧ IsElemAbelian 2 V ∧ Nat.card V = 8 ∧
    HSOne z ∧ HSTwo z V

@[expose] def StatementI48 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsTypeHS G →
    Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.HS)

end CFSG.Quasithin.HSType
