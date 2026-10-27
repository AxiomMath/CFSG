module

public import CFSG.RankThree.PartTwo.Sec13.Item135
public import CFSG.RankThree.PartTwo.Sec13.Steps
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.KFacts.KS14Orders

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Item135A7Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L → HypS A ∨ HypT A → ¬ IsQuasisimple (L ⧸ CFSG.pCore 2 L) →
    CFSG.pCore 2 L = ⊥ → CFSG.Open.pRank 2 (⊤ : Subgroup L) ≤ 2 →
    IsQuasisimple (L ⧸ CFSG.oddCore L) →
    Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* alternatingGroup (Fin 7)) →
    Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × alternatingGroup (Fin 7)) →
    Nonempty (Sec4.autIn L A ≃* Multiplicative (ZMod 4)) → c ∉ L →
    Nat.card (A ⊓ L : Subgroup G) = 9 →
    Sec21.IsIrreducibleOn (Sec4.autIn (L ⊓ Subgroup.normalizer (A : Set G)) (A ⊓ L)) →
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) →
    CFSG.Assembly.IsElemAbelian 3 (oThreeWStar A) → Nat.card (oThreeWStar A) = 9 →
    wStar A = oThreeWStar A ⊔ Sec4.autIn (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A →
    omegaA A = orbitIn (Subgroup.normalizer (A : Set G)) (Subgroup.zpowers c) →
    (omegaA A).ncard = 9 →
    Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) → False

@[expose] def Item135A7OneTwo : Prop :=
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
                  Equiv.Perm (Fin 7))) = τ * (e y : Equiv.Perm (Fin 7)) * τ⁻¹)) → False

namespace Res4Proof

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

theorem not_isoLThreePi_alt7 (p e : ℕ) [Fact p.Prime] :
    ¬ Sec4.IsoLThreePi ↥(alternatingGroup (Fin 7)) p e :=
  KFacts.KS14.not_isoLThreePi_of_card KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1
    (KFacts.KS14.forall_of_forall_lt (B := 14) (by norm_num) (by norm_num) (by decide +kernel))
    (KFacts.KS14.forall_of_forall_lt (B := 14) (by norm_num) (by norm_num) (by decide +kernel))
    p e

theorem not_isLThreePi_of_alt7 {X : Type} [Group X] (φ : X ≃* alternatingGroup (Fin 7)) :
    ¬ IsLThreePi X := by
  intro hX
  obtain ⟨p, e, hp, -, h⟩ := isLThreePi_of_mulEquiv φ.symm hX
  exact not_isoLThreePi_alt7 p e h

theorem false_of_alt7_of_sporadic {X : Type} [Group X] (φ : X ≃* alternatingGroup (Fin 7))
    {S : Type} [Group S] (hS : IsEmpty (S ≃* alternatingGroup (Fin 7))) (ψ : X ≃* S) : False :=
  hS.false (ψ.symm.trans φ)

theorem facts131_of_alt7
    (h131 : Item131) (hD : Sec13Data G A c L)
    (φ : L ⧸ aschbacherSolvableCore 3 L ≃* alternatingGroup (Fin 7)) :
    Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × alternatingGroup (Fin 7)) ∧
      Nonempty (Sec4.autIn L A ≃* Multiplicative (ZMod 4)) ∧ c ∉ L ∧
      Nat.card (A ⊓ L : Subgroup G) = 9 := by
  obtain ⟨⟨hM22p, hM22z⟩, ⟨hM12p, hM12z⟩, ⟨hJ2p, hJ2z⟩⟩ := sporadicModels131
  have hnL3 := not_isLThreePi_of_alt7 φ
  have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ := by
    have h1 := Subgroup.map_center_eq φ
    rw [isPerfect_center_alt7.2] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp h1
  have hcL : c ∉ L := not_mem_of_center_eq_bot hD hZ
  rcases h131 G A c L hD with ⟨hL3, -⟩ | ⟨hPGL, -, -⟩ | ⟨⟨ψ⟩, hstar⟩ | ⟨⟨ψ⟩, -⟩ |
      ⟨⟨ψ⟩, -⟩ | ⟨⟨ψ⟩, -⟩ | ⟨h7, -⟩
  ·
    exfalso
    obtain ⟨p, e, hp, he, hcase⟩ := hL3
    rcases hcase with ⟨hq, ⟨ψ⟩⟩ | ⟨hq, ⟨ψ⟩⟩
    · obtain ⟨hS, hZS⟩ := isPerfect_center_projSL p e he hq
      obtain ⟨-, -, -, ⟨χ⟩⟩ := facts_of_prod hD hS hZS ψ
      exact hnL3 ⟨p, e, hp, he, Or.inl ⟨hq, ⟨χ⟩⟩⟩
    · by_cases hq2 : 2 < p ^ e
      · obtain ⟨hS, hZS⟩ := isPerfect_center_projSU p e he hq hq2
        obtain ⟨-, -, -, ⟨χ⟩⟩ := facts_of_prod hD hS hZS ψ
        exact hnL3 ⟨p, e, hp, he, Or.inr ⟨hq, ⟨χ⟩⟩⟩
      · have h2 : p ^ e = 2 := by
          have : 2 ≤ p ^ e := le_trans hp.out.two_le (Nat.le_self_pow (by omega) _)
          omega
        obtain ⟨rfl, rfl⟩ := eq_two_one_of_pow_eq_two hp.out h2
        exact false_of_isSolvable hD isSolvable_projSU_two ψ
  ·
    exact absurd (facts_of_isZ3PGLThreePi hD hPGL).1 hnL3
  ·
    obtain ⟨-, h9, -, -⟩ := facts_of_prod hD isPerfect_center_alt7.1 isPerfect_center_alt7.2 ψ
    exact ⟨⟨ψ⟩, hstar, hcL, h9⟩
  ·
    obtain ⟨-, -, -, ⟨χ⟩⟩ := facts_of_prod hD hM22p hM22z ψ
    exact (false_of_alt7_of_sporadic φ KFacts.KS14.isEmpty_mulEquiv_M22_alternating.2.1 χ).elim
  ·
    obtain ⟨-, -, -, ⟨χ⟩⟩ := facts_of_prod hD hM12p hM12z ψ
    exact (false_of_alt7_of_sporadic φ KFacts.KS14.isEmpty_mulEquiv_M12_alternating.2.1 χ).elim
  ·
    obtain ⟨-, -, -, ⟨χ⟩⟩ := facts_of_prod hD hJ2p hJ2z ψ
    exact (false_of_alt7_of_sporadic φ KFacts.KS14.isEmpty_mulEquiv_j2_alternating.2.1 χ).elim
  ·
    exfalso
    rcases h7 with hSL | ⟨hHeis, -⟩
    · exact hcL (mem_of_isSLThreePiTwo slTwoCenter hD hSL)
    · exact hcL (mem_of_isHeisCentral hD hHeis)

end Res4Proof

open Res4Proof

theorem item135A7_of_cases
    (h131 : Item131) (h133 : Item133) (h3 : Item135A7Three)
    (h12 : Item135A7OneTwo) : Item135A7 := by
  intro G _ _ A c L hD hST hnq hO2 hm hO ⟨φ⟩
  obtain ⟨-, ⟨hM12p, hM12z⟩, ⟨hJ2p, hJ2z⟩⟩ := sporadicModels131
  obtain ⟨hprod, hstar, hcL, h9⟩ := facts131_of_alt7 h131 hD φ
  rcases h133 G A c L hD hST with h1 | h2 | ⟨hirr, hN, hO3, hO9, hW, hΩ, hΩ9, hL, -⟩ | h4
  · exact h12 G A c L hD hST hnq hO2 hm hO ⟨φ⟩ hprod hstar hcL h9 (Or.inl h1)
  · exact h12 G A c L hD hST hnq hO2 hm hO ⟨φ⟩ hprod hstar hcL h9 (Or.inr h2)
  · exact h3 G A c L hD hST hnq hO2 hm hO ⟨φ⟩ hprod hstar hcL h9 hirr hN hO3 hO9 hW hΩ hΩ9 hL
  · exfalso
    rcases h4 with hPGL | ⟨⟨ψ⟩⟩ | ⟨⟨ψ⟩⟩
    · exact not_isLThreePi_of_alt7 φ (facts_of_isZ3PGLThreePi hD hPGL).1
    · obtain ⟨-, -, -, ⟨χ⟩⟩ := facts_of_prod hD hM12p hM12z ψ
      exact false_of_alt7_of_sporadic φ KFacts.KS14.isEmpty_mulEquiv_M12_alternating.2.1 χ
    · obtain ⟨-, -, -, ⟨χ⟩⟩ := facts_of_prod hD hJ2p hJ2z ψ
      exact false_of_alt7_of_sporadic φ KFacts.KS14.isEmpty_mulEquiv_j2_alternating.2.1 χ

end CFSG.RankThree.PartTwo.Sec13
