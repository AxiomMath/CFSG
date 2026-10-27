module

public import CFSG.RankThree.PartTwo.Sec21.Item2113ProofJ3
import CFSG.RankThree.PartTwo.Sec21.Item2113ProofList
import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint

@[expose] def Item217InLIrredCover : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nonempty (L ⧸ Subgroup.center L ≃* NativeSporadic.J3) → c ∈ L →
      Sec4.IsTripleCover (lBar L) NativeSporadic.J3 → Nat.card A = 3 ^ 4 →
      Sec4.IsExtOf ↥(starOf A L) (Multiplicative (ZMod 8)) (Multiplicative (ZMod 3 × ZMod 3)) →
      IsIrreducibleOn (wStar A)

@[expose] def Item217InLTransCover : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nonempty (L ⧸ Subgroup.center L ≃* NativeSporadic.J3) → c ∈ L →
      Sec4.IsTripleCover (lBar L) NativeSporadic.J3 → Nat.card A = 3 ^ 4 →
      Sec4.IsExtOf ↥(starOf A L) (Multiplicative (ZMod 8)) (Multiplicative (ZMod 3 × ZMod 3)) →
      ∃ t ∈ wStar A, IsTransvectionOn t

@[expose] def Item217InLSylowCover : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nonempty (L ⧸ Subgroup.center L ≃* NativeSporadic.J3) → c ∈ L →
      Sec4.IsTripleCover (lBar L) NativeSporadic.J3 → Nat.card A = 3 ^ 4 →
      Sec4.IsExtOf ↥(starOf A L) (Multiplicative (ZMod 8)) (Multiplicative (ZMod 3 × ZMod 3)) →
      ∃ P : Sylow 3 (wStar A), ∀ x ∈ (P : Subgroup (wStar A)), (x : MulAut A) ∈ starOf A L

@[expose] def Item217InLNoTransCover : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nonempty (L ⧸ Subgroup.center L ≃* NativeSporadic.J3) → c ∈ L →
      Sec4.IsTripleCover (lBar L) NativeSporadic.J3 → Nat.card A = 3 ^ 4 →
      Sec4.IsExtOf ↥(starOf A L) (Multiplicative (ZMod 8)) (Multiplicative (ZMod 3 × ZMod 3)) →
      ∀ x ∈ starOf A L, ¬ IsTransvectionOn x

namespace Item2113Res3Proof


theorem lBar_not_j3_of_mem {G : Type} [Group G] [Finite G] {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hcL : c ∈ L) :
    ¬ Nonempty (lBar L ≃* NativeSporadic.J3) := by
  rintro ⟨e⟩
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt ((lZeroStarAt_subset A c) hpairs.2.2.1)
  exact Item2113Proof.not_mem_of_center_lBar_eq_bot hLc (hpair.mem_S.1.1.2 c hcA) hpairs.2.1
    (Item2113Proof.center_eq_bot_of_mulEquiv Item21Early2Proof.center_nativeJ3_eq_bot e) hcL

theorem item217InLIrred_of (h : Item217InLIrredCover) : Item217InLIrred := by
  intro G _ _ A E U c L hpair hJ hcL h11 h81 hext
  exact h G A E U c L hpair hJ hcL
    (h11.resolve_left (lBar_not_j3_of_mem hpair hcL)) h81 hext

theorem item217InLTrans_of (h : Item217InLTransCover) : Item217InLTrans := by
  intro G _ _ A E U c L hpair hJ hcL h11 h81 hext
  exact h G A E U c L hpair hJ hcL
    (h11.resolve_left (lBar_not_j3_of_mem hpair hcL)) h81 hext

theorem item217InLSylow_of (h : Item217InLSylowCover) : Item217InLSylow := by
  intro G _ _ A E U c L hpair hJ hcL h11 h81 hext
  exact h G A E U c L hpair hJ hcL
    (h11.resolve_left (lBar_not_j3_of_mem hpair hcL)) h81 hext

theorem item217InLNoTrans_of (h : Item217InLNoTransCover) : Item217InLNoTrans := by
  intro G _ _ A E U c L hpair hJ hcL h11 h81 hext
  exact h G A E U c L hpair hJ hcL
    (h11.resolve_left (lBar_not_j3_of_mem hpair hcL)) h81 hext

end Item2113Res3Proof

end CFSG.RankThree.PartTwo.Sec21
