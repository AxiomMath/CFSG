module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.LocalAnalysis

open Subgroup

@[expose] def GMSLinearLocalApplication {H : Type*} [Group H] (A : Subgroup H) (t : H)
    (U V D : Subgroup H) (n : ℕ) : Prop :=
  2 ≤ n ∧ orderOf t = 2 ∧
    (CFSG.Assembly.ComponentType.IsStandardSubgroup A ∧ ¬A.Normal ∧
      ∃ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = 2 ^ n ∧
        Nonempty (A ≃* Matrix.SpecialLinearGroup (Fin 2) k)) ∧
    (t ∈ centralizer (A : Set H) ∧
      (∃ T : Sylow 2 (centralizer (A : Set H)),
        (T : Subgroup (centralizer (A : Set H))) = (zpowers t).subgroupOf (centralizer A)) ∧
      A ≤ centralizer ({t} : Set H) ∧ (A.subgroupOf (centralizer ({t} : Set H))).Normal) ∧
    (U ≤ A ∧ (∃ T : Sylow 2 A, (T : Subgroup A) = U.subgroupOf A) ∧
      IsElementaryAbelian 2 V ∧ Nat.card V = (2 ^ n) ^ 2 ∧ t ∈ normalizer (V : Set H) ∧
      V ⊓ A = U ∧ V ⊓ centralizer ({t} : Set H) = U ∧
      closure {x | ∃ v ∈ V, x = v⁻¹ * (t⁻¹ * v * t)} = U) ∧
    (D ≤ A ⊓ normalizer (U : Set H) ∧ IsCyclic D ∧ Nat.card D = 2 ^ n - 1 ∧
      D ⊓ U = ⊥ ∧ U ⊔ D = A ⊓ normalizer (U : Set H) ∧
      D ≤ normalizer (V : Set H) ∧ D ≤ centralizer ({t} : Set H) ∧
      (∀ u ∈ U, u ≠ 1 → ∀ w ∈ U, w ≠ 1 → ∃! d : D, (d : H) * u * (d : H)⁻¹ = w) ∧
      ∀ v ∈ V, v ∉ U → ∀ w ∈ V, w ∉ U → ∃! d : D, ((d : H) * v * (d : H)⁻¹)⁻¹ * w ∈ U) ∧
    ∀ T : Sylow 2 H, t ∈ (T : Subgroup H) → ∃ x ∈ (T : Subgroup H), x * t ≠ t * x

theorem GMSLinearLocalApplication.le {H : Type*} [Group H] {A : Subgroup H} {t : H}
    {U V D : Subgroup H} {n : ℕ} (h : GMSLinearLocalApplication A t U V D n) :
    U ≤ V ∧ U ≤ centralizer ({t} : Set H) := by
  obtain ⟨-, -, -, -, ⟨-, -, -, -, -, -, hVt, -⟩, -⟩ := h
  rw [← hVt]
  exact ⟨inf_le_left, inf_le_right⟩

end CFSG.LocalAnalysis
