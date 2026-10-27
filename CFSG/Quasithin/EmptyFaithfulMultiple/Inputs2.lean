module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Statements
public import CFSG.Quasithin.EmptyFaithful.S14111

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def wreathSFourTwo : Subgroup (Equiv.Perm (Fin 8)) where
  carrier := {σ | ∀ i j : Fin 8, (i.val / 4 = j.val / 4 ↔ (σ i).val / 4 = (σ j).val / 4)}
  one_mem' := fun _ _ => Iff.rfl
  mul_mem' := by
    intro σ τ hσ hτ i j
    exact (hτ i j).trans (hσ (τ i) (τ j))
  inv_mem' := by
    intro σ hσ i j
    have h := hσ (σ⁻¹ i) (σ⁻¹ j)
    have hi : σ (σ⁻¹ i) = i := (Equiv.eq_symm_apply σ).mp rfl
    have hj : σ (σ⁻¹ j) = j := (Equiv.eq_symm_apply σ).mp rfl
    rw [hi, hj] at h
    exact h.symm

@[expose] def Input1391 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → CFSG.QuasithinUnique.quasithinIsQTKECat G → quasithinIsSylowTwo T →
    ∀ M : Subgroup G, InM T M → IsEmpty (M ≃* wreathSFourTwo)

@[expose] def InputI41Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G],
    (∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y) →
    ∀ z : G, orderOf z = 2 →
      Nonempty (Subgroup.centralizer ({z} : Set G) ≃* DihedralGroup 4) →
      IsLThreeTwoOrASix G

@[expose] def InputGNC128Solv : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSimpleGroup G →
    CFSG.QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → T ≠ ⊥ →
    ∃ C₁ C₂ : Subgroup G, C₁ ≠ ⊥ ∧ C₁ ≤ quasithinOmegaOneCenter T ∧
      (C₁.subgroupOf T).Characteristic ∧ C₂ ≠ ⊥ ∧ C₂ ≤ baum T ∧
      (C₂.subgroupOf (baum T)).Characteristic ∧
      ∀ M : Subgroup G, InM T M → perfectCore M ≤ Subgroup.centralizer (VZ T M : Set G) →
        M = (M ⊓ Subgroup.centralizer (C₁ : Set G)) ⊔ (M ⊓ Subgroup.normalizer (C₂ : Set G)) ∨
        ∃ (s : ℕ) (L : Fin s → Subgroup G), 1 ≤ s ∧ s ≤ 2 ∧
          (∀ i, IsChiBlock M (L i) ∧ ⁅L i, thompsonJ T⁆ = L i) ∧
          M = ((M ⊓ Subgroup.centralizer (C₁ : Set G)) ⊔
            (M ⊓ Subgroup.normalizer (C₂ : Set G))) ⊔ ⨆ i, L i

end CFSG.Quasithin.EmptyFaithfulMultiple
