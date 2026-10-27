module

import CFSG.Models.PGLOrders
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec21.Item221ResProofStatements
public import CFSG.RankThree.PartTwo.Sec21.Item221ResProofThree
public import CFSG.RankThree.PartTwo.Sec21.Item222ProofKZero
public import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly (IsElemAbelian)

@[expose] def Item233ZRootGenThreeNotU54 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Item231Concl A → Nat.card A = 3 ^ 3 →
      ∀ φ ∈ dStar A, ∀ Z ∈ lStar A, kOf A φ ≤ Z →
      (∀ ψ ∈ dStar A, ψ ≠ φ → Item228OneConcl A φ Z) →
      (∀ ρ ∈ starOf A Z, IsReflectionOn ρ → ρ ∈ dStar A) →
      IsEmpty (Z ≃* projSU 5 2 2) →
        Z ≤ (Z ⊓ Subgroup.normalizer (A : Set G)) ⊔
          ⨆ (ψ : MulAut A) (_ : ψ ∈ dStar A) (_ : ψ ∈ starOf A Z), kOf A ψ

@[expose] def Item233ZNotU54 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Item231Concl A → Nat.card A = 3 ^ 3 →
      ∀ φ ∈ dStar A, ∀ Z ∈ lStar A, kOf A φ ≤ Z →
      (∀ ψ ∈ dStar A, ψ ≠ φ → Item228OneConcl A φ Z) →
      (∀ ρ ∈ starOf A Z, IsReflectionOn ρ → ρ ∈ dStar A) →
        IsEmpty (Z ≃* projSU 5 2 2)

@[expose] def U54LongRoot : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A Z : Subgroup G),
    Maximal (fun B : Subgroup G => IsElemAbelian 3 B) A → Nat.card A = 3 ^ 3 →
    A ≤ Subgroup.normalizer (Z : Set G) →
    Nat.card (A ⊓ Subgroup.centralizer (Z : Set G) : Subgroup G) = 3 →
    Nonempty (Z ≃* projSU 5 2 2) →
    ∃ ρ ∈ starOf A Z, IsReflectionOn ρ ∧
      Nonempty (inSubgroup perfectResidual (Z ⊓ Subgroup.centralizer (fixedInG A ρ : Set G)) ≃*
        projSL 2 (GaloisField 2 4))

@[expose] def TerminalRootSmall : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I A B P : Subgroup G), A ≤ I → IsElemAbelian 3 A →
    Nat.card A = 3 ^ 3 →
    (Nonempty (I ≃* projSL 4 (GaloisField 2 2)) ∨ Nonempty (I ≃* projSp 3 (GaloisField 2 2))) →
    B ≤ A → Nat.card B = 9 → P ≤ I → P ≤ Subgroup.centralizer (B : Set G) →
      Group.IsPerfect P → Nat.card P ≤ 60

theorem item233ZRootGenThree_of_notU54 (hN : Item233ZRootGenThreeNotU54)
    (hX : Item233ZNotU54) : Item233ZRootGenThree := by
  intro G _ _ A E U c L hpair hconc hA27 φ hφ Z hZ hKZ h3 hR
  exact hN G A E U c L hpair hconc hA27 φ hφ Z hZ hKZ h3 hR
    (hX G A E U c L hpair hconc hA27 φ hφ Z hZ hKZ h3 hR)

namespace Item228ResProof

variable {G : Type} [Group G]

theorem card_fixedInG_eq_nine [Finite G] {A : Subgroup G} (hAc : ∀ a b : A, a * b = b * a)
    (hA27 : Nat.card A = 3 ^ 3) {ρ : MulAut A} (hρ : IsReflectionOn ρ) :
    Nat.card (fixedInG A ρ) = 9 := by
  rw [fixedInG, Subgroup.card_map_of_injective A.subtype_injective]
  have h := card_eq_three_mul_card_fixed hAc hρ
  rw [hA27] at h
  omega

theorem card_projSL_two_sixteen : Nat.card (projSL 2 (GaloisField 2 4)) = 4080 :=
  CFSG.PGLModel.card_projSL_two_sixteen

end Item228ResProof

open Item228ResProof

theorem item233ZNotU54_of (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) (h2130 : Item2130)
    (h222 : Item222) (hKW : KOfWellDefinedAll) (hU54 : U54LongRoot)
    (hSmall : TerminalRootSmall) : Item233ZNotU54 := by
  intro G _ _ A E U c L hpair hconc hA27 φ hφ Z hZ hKZ _ hR
  refine ⟨fun eZ => ?_⟩
  have hK := hKW G A E U c L hpair
  have hAF := hpair.mem_S.1
  have hAe : IsElemAbelian 3 A := hAF.1
  have hAc : ∀ a b : A, a * b = b * a := hAe.1.is_comm.comm
  have hAmax : Maximal (fun B : Subgroup G => IsElemAbelian 3 B) A :=
    ⟨hAe, fun B hB hAB => (hAF.2.1 B hB hAB).le⟩
  obtain ⟨z, hzA, hz1, hZz⟩ := mem_thetaComponentFamily_iff.mp hZ.1
  have hAN : A ≤ Subgroup.normalizer (Z : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hpair.standing.toTheoremFourHyp hAe hzA hz1
      Z hZz
  have hC3 := Item221ResProof.card_inf_centralizer_eq_three h66 hpair.standing hpair.mem_S hZ
  obtain ⟨ρ, hρZ, hρ, ⟨eP⟩⟩ := hU54 G A Z hAmax hA27 hAN hC3 ⟨eZ⟩
  have hρD : ρ ∈ dStar A := hR ρ hρZ hρ
  obtain ⟨eK⟩ := Item222Proof.nonempty_kOf_mulEquiv_projSL hAF hzA hZz hρZ hρ.1
    (by norm_num : 2 ≤ 4) eP
  have hKI : kOf A ρ ≤ iGroup A := kOf_le_iGroup hρD
  have hKC : kOf A ρ ≤ Subgroup.centralizer (fixedInG A ρ : Set G) :=
    (kOf_le_kZero hK hρD).trans (kZero_le_centralizer A ρ)
  have hKp : Group.IsPerfect (kOf A ρ) := isPerfect_of_mulEquiv_projSL (by norm_num) eK
  have hAI : A ≤ iGroup A := le_iGroup h2130 h222 hpair hK
  have hBA : fixedInG A ρ ≤ A := Subgroup.map_subtype_le _
  have hB9 := card_fixedInG_eq_nine hAc hA27 hρ
  have hI : Nonempty (iGroup A ≃* projSL 4 (GaloisField 2 2)) ∨
      Nonempty (iGroup A ≃* projSp 3 (GaloisField 2 2)) := by
    rcases hconc with ⟨-, -, h81⟩ | ⟨hI, -, -⟩ | ⟨hI, -, -⟩
    · rw [hA27] at h81
      norm_num at h81
    · exact Or.inl hI
    · exact Or.inr hI
  have h60 := hSmall G (iGroup A) A (fixedInG A ρ) (kOf A ρ) hAI hAe hA27 hI hBA hB9 hKI hKC hKp
  rw [Nat.card_congr eK.toEquiv, card_projSL_two_sixteen] at h60
  norm_num at h60

end CFSG.RankThree.PartTwo.Sec21
