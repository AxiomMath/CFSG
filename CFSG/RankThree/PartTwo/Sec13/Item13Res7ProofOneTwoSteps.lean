module

public import CFSG.RankThree.PartTwo.Sec13.Item13Res7ProofOneTwo

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CritProof

@[expose] def Item135A7OneTwoCrit2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L → HypS A ∨ HypT A → ¬ IsQuasisimple (L ⧸ CFSG.pCore 2 L) →
    CFSG.pCore 2 L = ⊥ → CFSG.Open.pRank 2 (⊤ : Subgroup L) ≤ 2 →
    IsQuasisimple (L ⧸ CFSG.oddCore L) →
    Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* alternatingGroup (Fin 7)) →
    Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × alternatingGroup (Fin 7)) →
    Nonempty (Sec4.autIn L A ≃* Multiplicative (ZMod 4)) → c ∉ L →
    Nat.card (A ⊓ L : Subgroup G) = 9 →
    (Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) ∨
      ((Nonempty (wStar A ≃* Equiv.Perm (Fin 4)) ∨
          Nonempty (wStar A ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))) ∧
        Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × alternatingGroup (Fin 7)) ∧
        (omegaA A).ncard = 3 ∧
        (∀ F ∈ omegaA A, ∃ w ∈ Subgroup.normalizer (A : Set G),
          F = (Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom) ∧
        ∃ t ∈ Subgroup.normalizer (A : Set G), t * c * t⁻¹ = c⁻¹ ∧
          ∃ (ht : t ∈ Subgroup.normalizer (L : Set G))
            (e : L ⧸ aschbacherSolvableCore 3 L ≃* alternatingGroup (Fin 7))
            (τ : Equiv.Perm (Fin 7)), τ.IsSwap ∧ ∀ y : L ⧸ aschbacherSolvableCore 3 L,
              ((e (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨t, ht⟩) y) :
                  Equiv.Perm (Fin 7))) = τ * (e y : Equiv.Perm (Fin 7)) * τ⁻¹)) →
    ∀ (p : ℕ) (C : Subgroup (CFSG.pCore p L)), Crit135 L p C →
      OddCoreAlt7 L (aschbacherSolvableCore 3 L) →
      Nat.card (Subgroup.center (L ⧸ CFSG.oddCore L)) = 2 → False

theorem item135A7OneTwoCrit_of_two (h : Item135A7OneTwoCrit2) : Item135A7OneTwoCrit := by
  intro G _ _ A c L hD hST hnq hO2 hm hO hA7 hprod hstar hcL h9 h12 p C hcrit hodd
  have hle := hodd.card_center_le
  have hpos : 0 < Nat.card (Subgroup.center (L ⧸ CFSG.oddCore L)) := Nat.card_pos
  rcases (show Nat.card (Subgroup.center (L ⧸ CFSG.oddCore L)) = 1 ∨
      Nat.card (Subgroup.center (L ⧸ CFSG.oddCore L)) = 2 by omega) with h1 | h2
  · exact Res7Proof.false_of_center_one hcrit hodd h1
  · exact h G A c L hD hST hnq hO2 hm hO hA7 hprod hstar hcL h9 h12 p C hcrit hodd h2

theorem item135A7_of_two
    (h131 : Item131) (h133 : Item133) (h : Item135A7OneTwoCrit2) : Item135A7 :=
  item135A7_of_crit h131 h133 (item135A7OneTwoCrit_of_two h)

end CFSG.RankThree.PartTwo.Sec13
