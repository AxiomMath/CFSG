module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Walter.Defs

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups

structure Hyp (G : Type) [Group G] [Finite G] where
  p : ℕ
  f : ℕ
  [fact_prime : Fact p.Prime]
  p_ne_two : p ≠ 2
  f_pos : 0 < f
  abelian_sylow : HasAbelianSylowTwo G
  card_sylow : ∀ P : Sylow 2 G, Nat.card P = 8
  J : G
  orderOf_J : orderOf J = 2
  K : Subgroup G
  le_centralizer : K ≤ Subgroup.centralizer ({J} : Set G)
  normal : (K.subgroupOf (Subgroup.centralizer ({J} : Set G))).Normal
  iso : K ≃* PSL(2, GaloisField p f)

attribute [instance] Hyp.fact_prime

variable {G : Type} [Group G] [Finite G]

@[expose] def Hyp.q (h : Hyp G) : ℕ := h.p ^ h.f

@[expose] def IsAlmostPSL2 {X : Type} [Group X] (M : Subgroup X) (p f : ℕ) [Fact p.Prime] :
    Prop :=
  ∃ K : Subgroup X, K ≤ M ∧ (K.subgroupOf M).Normal ∧ M ⊓ Subgroup.centralizer (K : Set X) = ⊥ ∧
    Nonempty (K ≃* PSL(2, GaloisField p f))

@[expose] def Case1 (h : Hyp G) : Prop :=
  Subgroup.centralizer ({h.J} : Set G) ⊔ CFSG.pPrimeCore 2 G = ⊤ ∧
    (∃ M : Subgroup (G ⧸ CFSG.pPrimeCore 2 G), M.Normal ∧
      (QuotientGroup.mk h.J : G ⧸ CFSG.pPrimeCore 2 G) ∉ M ∧
      M ≤ Subgroup.centralizer ({(QuotientGroup.mk h.J : G ⧸ CFSG.pPrimeCore 2 G)} : Set _) ∧
      Subgroup.zpowers (QuotientGroup.mk h.J : G ⧸ CFSG.pPrimeCore 2 G) ⊔ M = ⊤ ∧
      IsAlmostPSL2 M h.p h.f) ∧
    (h.q % 8 = 3 ∨ h.q % 8 = 5)

@[expose] def Case2 (h : Hyp G) : Prop :=
  ∃ L : Subgroup G, L.Normal ∧ Odd L.index ∧
    (∃ g : G, Subgroup.zpowers g ⊔ (L ⊔ Subgroup.centralizer (L : Set G)) = ⊤) ∧
    (∃ K' : Subgroup G, K' ≤ L ⊓ Subgroup.centralizer ({h.J} : Set G) ∧ h.J ∉ K' ∧
      L ⊓ Subgroup.centralizer ({h.J} : Set G) = Subgroup.zpowers h.J ⊔ K' ∧
      Nonempty (K' ≃* PSL(2, GaloisField h.p h.f))) ∧
    (h.q % 8 = 3 ∨ h.q % 8 = 5)

@[expose] def Theorem : Prop := ∀ (G : Type) [Group G] [Finite G] (h : Hyp G), Case1 h ∨ Case2 h

end CFSG.Walter.W67
