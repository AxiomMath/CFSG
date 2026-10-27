module

public import CFSG.Quasithin.EmptyFaithful.S1422Elim

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

section SecondCenter

variable {G : Type*} [Group G]

private theorem comm_of_mem_centerOf {X : Subgroup G} {a c : G} (ha : a ∈ X) (hc : c ∈ centerOf X) :
    a * c = c * a := Subgroup.mem_centralizer_iff.mp hc.2 a ha

@[expose] def secondCenterOf (X : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ X ∧ ∀ y ∈ X, x * y * x⁻¹ * y⁻¹ ∈ centerOf X}
  one_mem' := ⟨X.one_mem, fun y _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, hac⟩ ⟨hb, hbc⟩
    refine ⟨X.mul_mem ha hb, fun y hy => ?_⟩
    have h1 := hac y hy
    have h2 := hbc y hy
    have hcomm : a * (b * y * b⁻¹ * y⁻¹) = (b * y * b⁻¹ * y⁻¹) * a := comm_of_mem_centerOf ha h2
    have h3 : a * b * y * (a * b)⁻¹ * y⁻¹ =
        (a * (b * y * b⁻¹ * y⁻¹) * a⁻¹) * (a * y * a⁻¹ * y⁻¹) := by group
    have h4 : a * (b * y * b⁻¹ * y⁻¹) * a⁻¹ = b * y * b⁻¹ * y⁻¹ := by
      rw [hcomm]; group
    rw [h3, h4]
    exact (centerOf X).mul_mem h2 h1
  inv_mem' := by
    rintro a ⟨ha, hac⟩
    refine ⟨X.inv_mem ha, fun y hy => ?_⟩
    have h1 := hac y hy
    have h1' : (a * y * a⁻¹ * y⁻¹)⁻¹ ∈ centerOf X := (centerOf X).inv_mem h1
    have hcomm : a⁻¹ * (a * y * a⁻¹ * y⁻¹)⁻¹ = (a * y * a⁻¹ * y⁻¹)⁻¹ * a⁻¹ :=
      comm_of_mem_centerOf (X.inv_mem ha) h1'
    have h3 : a⁻¹ * y * (a⁻¹)⁻¹ * y⁻¹ = (a⁻¹ * (a * y * a⁻¹ * y⁻¹)⁻¹ * a⁻¹⁻¹) := by group
    rw [h3, hcomm]
    have : (a * y * a⁻¹ * y⁻¹)⁻¹ * a⁻¹ * a⁻¹⁻¹ = (a * y * a⁻¹ * y⁻¹)⁻¹ := by group
    rw [this]
    exact h1'

theorem mem_secondCenterOf {X : Subgroup G} {x : G} :
    x ∈ secondCenterOf X ↔ x ∈ X ∧ ∀ y ∈ X, x * y * x⁻¹ * y⁻¹ ∈ centerOf X := Iff.rfl

theorem secondCenterOf_le {X : Subgroup G} : secondCenterOf X ≤ X := fun _ hx => hx.1

end SecondCenter

@[expose] def AutM12AmalgamLocal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H L2 : Subgroup G), CaseAutM12 H L2 →
    Nat.card (secondCenterOf (pCoreOf 2 H)) = 8 ∧
    (∀ x ∈ secondCenterOf (pCoreOf 2 H), x * x = 1) ∧
    (∀ Q : Subgroup G, secondCenterOf (pCoreOf 2 H) ≤ Q → Q ≤ pCoreOf 2 H →
        H ≤ Subgroup.normalizer (Q : Set G) →
        Q = secondCenterOf (pCoreOf 2 H) ∨
        (Nat.card Q = 16 ∧ ∀ x ∈ Q, x * x = 1 → x ∈ secondCenterOf (pCoreOf 2 H)) ∨
        omegaOneOf (pCoreOf 2 H) ≤ Q) ∧
    IsQ8Sq ↥(omegaOneOf (pCoreOf 2 H)) ∧
    ∃ E : Subgroup G, E ≤ omegaOneOf (pCoreOf 2 H) ∧ IsElemAbelian 2 E ∧ Nat.card E = 8 ∧
      L2 ≤ Subgroup.normalizer (E : Set G) ∧
      ∀ V : Subgroup G, V ≤ pCoreOf 2 H → Nat.card V = 4 →
        L2 ≤ Subgroup.normalizer (V : Set G) → V ≤ E

end CFSG.Quasithin
