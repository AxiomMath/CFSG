module

import CFSG.CGT.PushingUp.TwoLocals
public import CFSG.RankThree.PartTwo.Sec15.HypR
public import CFSG.RankThree.PartTwo.Sec15.Item155ProofDefs

public section

@[expose] def CFSG.RankThree.PartTwo.Sec15.Big152 {G : Type} [Group G] (Y : Subgroup G) :
    Prop :=
  8 ∣ Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y)

@[expose] def CFSG.RankThree.PartTwo.Sec15.IsJ2Type {G : Type} [Group G] (Y : Subgroup G) :
    Prop :=
  Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Blueprint.NativeSporadic.J2)

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Item152Big (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY4 A LB, Big152 Y → ∀ M ∈ scriptY2 A, Y ≤ M →
    generalizedFitting ↥M = CFSG.pCore 2 ↥M →
      ∃ X ∈ thetaComponentsIn M, Y ≤ X ∧ X ∈ scriptY0 A LB

@[expose] noncomputable def Item153MainJ2 (A : Subgroup G) (LB : Subgroup G → Subgroup G) :
    Prop :=
  ∀ Y ∈ scriptY0Star A LB, IsJ2Type Y →
    CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G) =
        {Subgroup.normalizer
          (oPrimeResidualOf 3 (delta A LB (Subgroup.normalizer (Y : Set G))) : Set G)} ∧
      (∀ S ∈ scriptQPiStar A LB (Subgroup.normalizer
          (oPrimeResidualOf 3 (delta A LB (Subgroup.normalizer (Y : Set G))) : Set G)) (piOf 2),
        S ∈ scriptQPiStar A LB ⊤ (piOf 2) ∧
          Subgroup.normalizer ((A ⊔ S : Subgroup G) : Set G) ≤
            Subgroup.normalizer
              (oPrimeResidualOf 3 (delta A LB (Subgroup.normalizer (Y : Set G))) : Set G)) ∧
      generalizedFitting ↥Y = CFSG.pCore 2 ↥Y

@[expose] noncomputable def Item155wJ2 (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY3 A LB, oPrimeResidualOf 3 Y ∈ scriptY4 A LB → Big152 (oPrimeResidualOf 3 Y) →
    Y = oPrimeResidualOf 3 Y ⊔ CFSG.Open.pCoreOf 2 Y →
      ∀ K ∈ gam155 A LB Y (oPrimeResidualOf 3 Y), IsJ2Type K →
        (omg155 A (oPrimeResidualOf 3 Y) ∨
          K = oPrimeResidualOf 3 Y ⊔ CFSG.Open.pCoreOf 2 K) →
        ∀ M ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ Y : Subgroup G) : Set G),
          delta A LB M ≤ Subgroup.normalizer
            (oPrimeResidualOf 3 (delta A LB (Subgroup.normalizer (K : Set G))) : Set G)

end CFSG.RankThree.PartTwo.Sec15

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14

@[expose] noncomputable def Item152BigR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Item152Big A (lB A)

@[expose] noncomputable def Item153MainJ2R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Item153MainJ2 A (lB A)

@[expose] noncomputable def Item155wJ2R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Item155wJ2 A (lB A)

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {LB : Subgroup G → Subgroup G}

theorem normalizer_le_n155w_of_j2 (h153 : Item153MainJ2 A (lB A)) {K : Subgroup G}
    (hK : K ∈ scriptY0Star A (lB A)) (hKJ : IsJ2Type K) :
    Subgroup.normalizer (K : Set G) ≤ n155 A K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK2 : CFSG.Open.pCoreOf 2 K ≠ ⊥ := hK.prop.2.2
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := hK.prop.1.1.2
  have hloc : IsPLocal 2 (Subgroup.normalizer (CFSG.Open.pCoreOf 2 K : Set G)) :=
    CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) K) hK2
  obtain ⟨M', hle, hM'⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge hloc
  have hmem : M' ∈ CFSG.maximalTwoLocalsContaining ((K ⊔ A : Subgroup G) : Set G) :=
    ⟨hM', fun x hx => hle ((sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
      (hAK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))) hx)⟩
  rw [(h153 K hK hKJ).1, Set.mem_singleton_iff] at hmem
  exact (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K).trans (hle.trans hmem.le)

end CFSG.RankThree.PartTwo.Sec15
