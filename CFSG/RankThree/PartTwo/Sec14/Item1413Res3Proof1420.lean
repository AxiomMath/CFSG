module

import CFSG.RankThree.PartOne.KE8F.HyperGen
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res2ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS

@[expose] noncomputable def Step1420A7SneR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Fail1411 A (lB A) →
      ∀ c' : G, Subgroup.zpowers c' ∈ gammaA A (lB A) → ∀ L' ∈ lA A c',
        Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* alternatingGroup (Fin 7)) →
        ((Nonempty (wStar A ≃* Equiv.Perm (Fin 4)) ∨
            Nonempty (wStar A ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))) ∧
          Nonempty (lBarA c' L' A ≃* Multiplicative (ZMod 3) × alternatingGroup (Fin 7)) ∧
          (omegaA A).ncard = 3 ∧
          (∀ F ∈ omegaA A, ∃ w ∈ Subgroup.normalizer (A : Set G),
            F = (Subgroup.zpowers c').map (MulAut.conj w).toMonoidHom) ∧
          ∃ t ∈ Subgroup.normalizer (A : Set G), t * c' * t⁻¹ = c'⁻¹ ∧
            ∃ (ht : t ∈ Subgroup.normalizer (L' : Set G))
              (e : L' ⧸ aschbacherSolvableCore 3 L' ≃* alternatingGroup (Fin 7))
              (τ : Equiv.Perm (Fin 7)), τ.IsSwap ∧ ∀ y : L' ⧸ aschbacherSolvableCore 3 L',
                ((e (Sec4.thetaQuotMulAut L' (L'.normalizerMonoidHom ⟨t, ht⟩) y) :
                    Equiv.Perm (Fin 7))) = τ * (e y : Equiv.Perm (Fin 7)) * τ⁻¹) →
        ∀ R ∈ scriptQPiStar A (lB A) L' (piOf 2), R ∉ scriptQPiStar A (lB A) ⊤ (piOf 2)

namespace Proof1413Res3

variable {G : Type} [Group G] [Finite G]

theorem le_of_forall_hyperplane {A T U : Subgroup G} (hA : IsE27 A)
    (hAT : A ≤ Subgroup.normalizer (T : Set G)) (hT3 : ¬ 3 ∣ Nat.card T)
    (hU : ∀ D, IsHyperplane A D → T ⊓ Subgroup.centralizer (D : Set G) ≠ ⊥ →
      T ⊓ Subgroup.centralizer (D : Set G) ≤ U) : T ≤ U := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CFSG.IsElementaryAbelian 3 ↥A := Proof1413Res2.isElementaryAbelian_of_isElemAbelian hA.1
  have : Nontrivial ↥A := by
    rw [← Finite.one_lt_card_iff_nontrivial, hA.2]
    norm_num
  refine (PartOne.KE8F.le_iSup_hyperplane_centralizers hAT hT3).trans
    (iSup₂_le fun B hB => ?_)
  have hD : IsHyperplane A (B.map A.subtype) := by
    refine ⟨Subgroup.map_subtype_le B, ?_⟩
    rw [Subgroup.card_map_of_injective A.subtype_injective, ← hB, Subgroup.index_mul_card]
  by_cases h0 : T ⊓ Subgroup.centralizer ((B.map A.subtype : Subgroup G) : Set G) = ⊥
  · rw [h0]
    exact bot_le
  · exact hU _ hD h0

omit [Finite G] in
theorem mem_of_zpowers_le {D : Subgroup G} {x : G} (h : Subgroup.zpowers x ≤ D) : x ∈ D :=
  h (Subgroup.mem_zpowers x)

end Proof1413Res3

end CFSG.RankThree.PartTwo.Sec14
