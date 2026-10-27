module

public import CFSG.RankThree.PartTwo.Sec21.Item21Early3ProofJ3

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint

@[expose] def Item217InLIrred : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nonempty (L ⧸ Subgroup.center L ≃* NativeSporadic.J3) → c ∈ L →
      (Nonempty (lBar L ≃* NativeSporadic.J3) ∨ Sec4.IsTripleCover (lBar L) NativeSporadic.J3) →
      Nat.card A = 3 ^ 4 →
      Sec4.IsExtOf ↥(starOf A L) (Multiplicative (ZMod 8)) (Multiplicative (ZMod 3 × ZMod 3)) →
      IsIrreducibleOn (wStar A)

@[expose] def Item217InLTrans : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nonempty (L ⧸ Subgroup.center L ≃* NativeSporadic.J3) → c ∈ L →
      (Nonempty (lBar L ≃* NativeSporadic.J3) ∨ Sec4.IsTripleCover (lBar L) NativeSporadic.J3) →
      Nat.card A = 3 ^ 4 →
      Sec4.IsExtOf ↥(starOf A L) (Multiplicative (ZMod 8)) (Multiplicative (ZMod 3 × ZMod 3)) →
      ∃ t ∈ wStar A, IsTransvectionOn t

@[expose] def Item217InLSylow : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nonempty (L ⧸ Subgroup.center L ≃* NativeSporadic.J3) → c ∈ L →
      (Nonempty (lBar L ≃* NativeSporadic.J3) ∨ Sec4.IsTripleCover (lBar L) NativeSporadic.J3) →
      Nat.card A = 3 ^ 4 →
      Sec4.IsExtOf ↥(starOf A L) (Multiplicative (ZMod 8)) (Multiplicative (ZMod 3 × ZMod 3)) →
      ∃ P : Sylow 3 (wStar A), ∀ x ∈ (P : Subgroup (wStar A)), (x : MulAut A) ∈ starOf A L

@[expose] def Item217InLNoTrans : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nonempty (L ⧸ Subgroup.center L ≃* NativeSporadic.J3) → c ∈ L →
      (Nonempty (lBar L ≃* NativeSporadic.J3) ∨ Sec4.IsTripleCover (lBar L) NativeSporadic.J3) →
      Nat.card A = 3 ^ 4 →
      Sec4.IsExtOf ↥(starOf A L) (Multiplicative (ZMod 8)) (Multiplicative (ZMod 3 × ZMod 3)) →
      ∀ x ∈ starOf A L, ¬ IsTransvectionOn x

namespace Item2113Proof

theorem item217InLLocal_of (hI : Item217InLIrred) (hT : Item217InLTrans)
    (hS : Item217InLSylow) (hN : Item217InLNoTrans) : Item217InLLocal := by
  intro G _ _ A E U c L hpair hJ hcL h11 h81 hext
  exact ⟨hI G A E U c L hpair hJ hcL h11 h81 hext, hT G A E U c L hpair hJ hcL h11 h81 hext,
    hS G A E U c L hpair hJ hcL h11 h81 hext, hN G A E U c L hpair hJ hcL h11 h81 hext⟩

end Item2113Proof

end CFSG.RankThree.PartTwo.Sec21
