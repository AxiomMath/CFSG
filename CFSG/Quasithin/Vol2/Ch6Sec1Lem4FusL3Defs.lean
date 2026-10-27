module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def leviOfL3 {G : Type*} [Group G] (N : Subgroup G) (u : G) : Subgroup G :=
  ⁅N ⊓ Subgroup.centralizer ({u} : Set G), N ⊓ Subgroup.centralizer ({u} : Set G)⁆

@[expose] def IsL3Levi {G : Type*} [Group G] (K : Subgroup G) (u : G) (p : ℕ) : Prop :=
  orderOf u = 2 ∧ u ∈ K ∧
    (∀ x : ↥K, x ∈ Subgroup.center ↥K ↔ ((x : G) = 1 ∨ (x : G) = u)) ∧
    Group.IsPerfect ↥K ∧
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ∧
      Nonempty (↥K ⧸ Subgroup.center ↥K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)

@[expose] def LocFusL3 (G : Type*) [Group G] (N : Subgroup G) : Prop :=
  ∀ (T X E : Subgroup G), IsSylowTwoOf T (N ⊔ T) → X ≤ N → X = oTwoUpper X →
    (X ⊓ T).relIndex X = 5 → ((X ⊓ T).subgroupOf X).Normal →
    T ≤ Subgroup.normalizer (X : Set G) →
    ¬ X ≤ Subgroup.normalizer ((T ⊓ N : Subgroup G) : Set G) →
    E ≤ pCoreOf 2 (X ⊔ T) → IsElemAbelian 2 E → E ≠ ⊥ →
      ∃ n ∈ N, E.map (MulAut.conj n).toMonoidHom ≤ T ∧
        ¬ E.map (MulAut.conj n).toMonoidHom ≤ pCoreOf 2 (X ⊔ T)

structure L3FusFacts {G : Type*} [Group G] (N : Subgroup G) (p : ℕ) : Prop where
  rank : ∀ V : Subgroup G, V ≤ N → IsElemAbelian 2 V → Nat.card V ≤ 4
  invConj : ∀ u ∈ N, ∀ v ∈ N, orderOf u = 2 → orderOf v = 2 → ∃ g ∈ N, g * u * g⁻¹ = v
  levi : ∀ u ∈ N, orderOf u = 2 →
    IsL3Levi (leviOfL3 N u) u p ∧
      ∀ c ∈ N, Commute c u → c ∈ Subgroup.centralizer (leviOfL3 N u : Set G) →
        ∀ g ∈ N, Commute g u → Commute c g
  uniq : 5 < p → ∀ y ∈ N, orderOf y = 5 → ∀ u ∈ N, ∀ v ∈ N, orderOf u = 2 → orderOf v = 2 →
    Commute u y → Commute v y → y ∈ leviOfL3 N u → y ∈ leviOfL3 N v → u = v
  invert : 5 < p → ∀ y ∈ N, ∀ z ∈ N, orderOf y = 5 → orderOf z = 2 → y ∈ leviOfL3 N z →
    ∃ t ∈ N, orderOf t = 2 ∧ t * y * t⁻¹ = y⁻¹
  factB : ∀ u ∈ N, orderOf u = 2 → ∀ v : G, v * v = 1 →
    v ∈ Subgroup.centralizer (leviOfL3 N u : Set G) → v = 1 ∨ v = u

end CFSG.Quasithin.H13
