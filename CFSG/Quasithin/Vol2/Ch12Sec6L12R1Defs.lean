module

public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Milestones.CL_LIT_SQTK_simple_listBase
public import CFSG.Open.QuasithinDefs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def FactKv1262aTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K T T₀ L E : Subgroup G),
    CFSG.IsQuasisimple ↥K → CFSG.Milestones.SQTKSimpleList (↥K ⧸ Subgroup.center ↥K) →
    IsSylowTwoOf T K → T₀ ≤ T → T₀ ≤ Subgroup.normalizer (L : Set G) → T₀.relIndex T ≤ 2 →
    L ≤ K → ⁅L, L⁆ = L → quasithinO2QuotientIso L ↥(alternatingGroup (Fin 6)) →
    E ≤ pCoreOf 2 L → IsElemAbelian 2 E → Nat.card ↥E = 32 →
    L ≤ Subgroup.normalizer (E : Set G) → ⁅E, L⁆ = E →
    Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set G)) = 2 →
      (Nonempty (↥K ⧸ Subgroup.center ↥K ≃* ↥NativeSporadic.M22) ∨
        Nonempty (↥K ⧸ Subgroup.center ↥K ≃* NativeSporadic.HS)) ∧
      E ⊓ Subgroup.centralizer (L : Set G) ≤ (Subgroup.center ↥K).map K.subtype

@[expose] def autCentralizer {X : Type*} [Group X] (α : MulAut X) : Subgroup X where
  carrier := {x | α x = x}
  one_mem' := map_one α
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, ha, hb]
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_inv, ha]

theorem mem_autCentralizer {X : Type*} [Group X] {α : MulAut X} {x : X} :
    x ∈ autCentralizer α ↔ α x = x :=
  Iff.rfl

structure A6LocalData {X : Type*} [Group X] (B P E : Subgroup X) : Prop where
  perfect : ⁅B, B⁆ = B
  le : P ≤ B
  pGroup : IsPGroup 2 ↥P
  normalizes : B ≤ Subgroup.normalizer (P : Set X)
  card : Nat.card ↥B = 360 * Nat.card ↥P
  le_P : E ≤ P
  elemAbelian : IsElemAbelian 2 E
  card_E : Nat.card ↥E = 16
  normalizes_E : B ≤ Subgroup.normalizer (E : Set X)

@[expose] def FactHSNormLv : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* NativeSporadic.HS) →
    ∀ (B P E : Subgroup X), A6LocalData B P E →
      ∀ α : MulAut X, (∀ e ∈ E, α e = e) → (∀ b ∈ B, α b = b) → α = 1

@[expose] def FactHSE16Outer : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* NativeSporadic.HS) →
    ∀ (B P E : Subgroup X), A6LocalData B P E →
      ∀ A : Finset (MulAut X), 7 ≤ A.card →
        (∀ α ∈ A, (∀ e ∈ E, α e = e) ∧ ∀ e ∈ E, α ≠ MulAut.conj e) →
          ∃ α ∈ A, IsSimpleGroup ↥(perfectCore (autCentralizer α)) ∧
            Nat.card ↥(perfectCore (autCentralizer α)) = 20160

end CFSG.Quasithin.H13
