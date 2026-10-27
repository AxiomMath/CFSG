module

public import CFSG.Quasithin.Vol2.Ch12Sec2Setting
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative Pointwise

@[expose] def Lem12211Borel : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → quasithinIsMaxTwoLocal M → T ≤ M →
    Subgroup.normalizer (T : Set G) ≤ M → IsHStar T M H → 2 ≤ E1.nParam H →
      (∃ C : Subgroup G, C ≤ H ⊓ M ∧ Odd (Nat.card C) ∧ ∃ k : ℕ, C.relIndex (H ⊓ M) = 2 ^ k) ∧
      ∀ C : Subgroup G, C ≤ H ⊓ M → Odd (Nat.card C) → (∃ k : ℕ, C.relIndex (H ⊓ M) = 2 ^ k) →
        C ≠ ⊥ ∧ ((2 < E1.nParam H ∨ ¬ IsPGroup 3 C) →
          ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ 3 < p ∧ A ≤ C ∧ A ≠ ⊥ ∧ IsElemAbelian p A ∧
            (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G))

@[expose] def Lem12211A315 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (h : Hyp1223 G T L V)
    (A : Subgroup G) (p : ℕ), p.Prime → 3 < p → A ≤ h.MV → IsPGroup p A → IsMulCommutative ↥A →
    (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) → autOn A V ≤ autOn L V →
      A ≤ Subgroup.centralizer (V : Set G)

end CFSG.Quasithin.H13
