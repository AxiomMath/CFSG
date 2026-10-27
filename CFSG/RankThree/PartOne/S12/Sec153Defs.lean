module

public import CFSG.RankThree.PartOne.S12.KFTransfer
public import CFSG.RankThree.PartOne.U5K.Model
public import CFSG.RankThree.PartOne.U5K.Transport
public import CFSG.RankThree.PartOne.S12.Facts

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory

@[expose] def KFU5Mod : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152Five p E A (lieGenerated p E) →
    ∃ (θ : ↥(reflectionGroup p E) ≃* Equiv.Perm (Fin 5)) (v : Fin 5 → ↥E),
      (∀ (w : ↥(reflectionGroup p E)) (i : Fin 5), (w : MulAut ↥E) (v i) = v (θ w i)) ∧
      (∀ x : ↥E, ∃ a : Fin 5 → ℤ,
        x = v 0 ^ a 0 * v 1 ^ a 1 * v 2 ^ a 2 * v 3 ^ a 3 * v 4 ^ a 4) ∧
      (∀ a : Fin 5 → ℤ, v 0 ^ a 0 * v 1 ^ a 1 * v 2 ^ a 2 * v 3 ^ a 3 * v 4 ^ a 4 = 1 ↔
        ∃ m : ℤ, ∀ i, (p : ℤ) ∣ a i - m) ∧
      (∀ (t : MulAut ↥E) (ht : t ∈ reflectionSet p E),
        ∃ a b : Fin 5, a ≠ b ∧ θ ⟨t, Subgroup.subset_closure ht⟩ = Equiv.swap a b)

@[expose] def KFU5At : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G) (f : ℕ),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152Five p E A (lieGenerated p E) →
    1 ≤ f → p ∣ 2 ^ f + 1 →
    Nonempty ((lieGenerated p E ⧸ Subgroup.center ↥(lieGenerated p E)) ≃* projSU 5 2 f) →
    ∀ t ∈ reflectionSet p E, KFAt p E f t

@[expose] def U5FiveInndiag : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152Five p E A (lieGenerated p E) →
    p = 5 → ∀ (f : ℕ)
      (e : ↥(lieGenerated p E) ⧸ Subgroup.center ↥(lieGenerated p E) ≃* projSU 5 2 f)
      (x : G) (hx : x ∈ lieNormalizer p E), x ∈ E →
        U5K.U5Act (lieGenerated p E) e ⟨x, hx⟩ ∈ U5K.U5Inndiag f

end CFSG.RankThree.PartOne
