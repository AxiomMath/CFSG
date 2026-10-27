module

public import CFSG.RankThree.PartTwo.Sec13.Item135CritProofA7
public import CFSG.RankThree.PartTwo.Sec13.Item135CritProofTwoLocal
public import CFSG.RankThree.PartTwo.Sec13.Item13Res4ProofA7Z3
import CFSG.RankThree.PartTwo.Sec13.Item13Basic

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CritProof

@[expose] def Item135A7OneTwoCrit : Prop :=
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
      OddCoreAlt7 L (aschbacherSolvableCore 3 L) → False

@[expose] def Item135A7Z3HypTKCrit : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L → HypT A → c ∈ L → ¬ IsQuasisimple (L ⧸ CFSG.pCore 2 L) →
    CFSG.pCore 2 L = ⊥ → CFSG.Open.pRank 2 (⊤ : Subgroup L) ≤ 2 →
    IsQuasisimple (L ⧸ CFSG.oddCore L) →
    Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) →
    Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L) →
    ∀ K ∈ thetaComponentsAt 3 c, A ≤ L ⊔ K →
      Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6)) →
      ∀ (p : ℕ) (C : Subgroup (CFSG.pCore p L)), Crit135 L p C →
        OddCoreAlt7 L ((Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)).comap
          (QuotientGroup.mk' (aschbacherSolvableCore 3 L))) →
        Crit135K c L K ((omegaOneCore p C).map L.subtype) → False

theorem item135A7OneTwo_of_crit
    (h : Item135A7OneTwoCrit) : Item135A7OneTwo := by
  intro G _ _ A c L hD hST hnq hO2 hm hO hA7 hprod hstar hcL h9 h12
  obtain ⟨e⟩ := hA7
  obtain ⟨φ, hφ, hK, hker⟩ := surj_alt7_of_equiv e
  have hperf : Group.IsPerfect L :=
    Sec6.isPerfect_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt
  obtain ⟨p, -, C, hcrit⟩ := exists_crit135 hD hnq hO2 φ hφ hK
  have hodd := oddCoreAlt7_of hO φ hφ hK
  rw [hker] at hodd
  exact h G A c L hD hST hnq hO2 hm hO ⟨e⟩ hprod hstar hcL h9 h12 p C hcrit hodd

theorem item135A7Z3HypTK_of_crit
    (h : Item135A7Z3HypTKCrit) : Item135A7Z3HypTK := by
  intro G _ _ A c L hD hT hcL hnq hO2 hm hO hA7 hHeis K hK hAK hK6
  obtain ⟨φ, hφ, hKs, hker⟩ := surj_alt7_of_tripleCover hA7
  have hperf : Group.IsPerfect L :=
    Sec6.isPerfect_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt
  obtain ⟨p, -, C, hcrit⟩ := exists_crit135 hD hnq hO2 φ hφ hKs
  have hodd := oddCoreAlt7_of hO φ hφ hKs
  rw [hker] at hodd
  have hKL : K ≠ L := ne_of_tripleCover hK6 hA7
  have := hcrit.characteristic
  exact h G A c L hD hT hcL hnq hO2 hm hO hA7 hHeis K hK hAK hK6 p C hcrit hodd
    (crit135K_of hD hK hKL hO hcrit.odd_card_centralizer)

theorem item135A7_of_crit
    (h131 : Item131) (h133 : Item133) (h12 : Item135A7OneTwoCrit) : Item135A7 :=
  item135A7_of_cases h131 h133 item135A7Three (item135A7OneTwo_of_crit h12)

end CFSG.RankThree.PartTwo.Sec13
