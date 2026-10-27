module

public import CFSG.Quasithin.H13.L32ASk5
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

structure Ctx726 (G : Type) [Group G] [Finite G] (T L V H D : Subgroup G) : Prop where
  setting : Setting147 G T L V H
  three : IsPOnePlusTwo 3 ↥(oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)))
  l1_eq : L32A.l1 T L V = oTwoUpper (L32A.o2z (oTwoUpper H))
  l1_normal : H ≤ Subgroup.normalizer (L32A.l1 T L V : Set G)
  r1_irred : ∀ W : Subgroup G, L32A.l1 T L V ⊔ pCoreOf 2 (oTwoUpper H) ≤ W →
    W ≤ oTwoUpper H → pCoreOf 2 (L32A.l1 T L V ⊔ T) ≤ Subgroup.normalizer (W : Set G) →
    W = L32A.l1 T L V ⊔ pCoreOf 2 (oTwoUpper H) ∨ W = oTwoUpper H
  eq_hz : H = L32A.hz T V
  eq_kt : H = oTwoUpper H ⊔ T
  two_three : ∀ p : ℕ, p.Prime → p ∣ Nat.card H → p = 2 ∨ p = 3
  u_eq : ⁅fsuU T V, L32A.l1 T L V⁆ = fsuU T V
  o2_l1_ne : pCoreOf 2 (L32A.l1 T L V) ≠ ⊥
  max_two_local : quasithinIsMaxTwoLocal H
  center_p : ∀ x ∈ pCoreOf 2 (oTwoUpper H), (∀ y ∈ pCoreOf 2 (oTwoUpper H), x * y = y * x) →
    ∀ k ∈ oTwoUpper H, x * k = k * x
  d_le : D ≤ oTwoUpper H
  d_comm : ∀ d ∈ D, ∀ k ∈ oTwoUpper H, d * k = k * d
  card_d : Nat.card D = 4
  v1_le_d : fsuV1 T V ≤ D
  d_normal : H ≤ Subgroup.normalizer (D : Set G)

@[expose] def Lemma14_7_26 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H D : Subgroup G), Ctx726 G T L V H D → fusionIsTI D

end CFSG.Quasithin.H13
