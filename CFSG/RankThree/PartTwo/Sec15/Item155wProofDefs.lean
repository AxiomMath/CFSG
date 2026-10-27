module

public import CFSG.RankThree.PartTwo.Sec15.Item155ProofDefs
public import CFSG.RankThree.PartTwo.Sec15.HypR
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item1411Chain
import CFSG.CGT.PushingUp.TwoLocals

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Two155w (A Y : Subgroup G) : Prop :=
  ∀ K ∈ gam155 A (lB A) Y (oPrimeResidualOf 3 Y),
    (omg155 A (oPrimeResidualOf 3 Y) ∨ K = oPrimeResidualOf 3 Y ⊔ CFSG.Open.pCoreOf 2 K) →
    ∀ M ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ Y : Subgroup G) : Set G),
      delta A (lB A) M ≤ n155 A K

@[expose] noncomputable def Item155w (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY3 A LB, oPrimeResidualOf 3 Y ∈ scriptY4 A LB →
    Y = oPrimeResidualOf 3 Y ⊔ CFSG.Open.pCoreOf 2 Y →
      (omg155 A (oPrimeResidualOf 3 Y) → (gam155 A LB Y (oPrimeResidualOf 3 Y)).Nonempty) ∧
      ∀ K ∈ gam155 A LB Y (oPrimeResidualOf 3 Y),
        (omg155 A (oPrimeResidualOf 3 Y) ∨
          K = oPrimeResidualOf 3 Y ⊔ CFSG.Open.pCoreOf 2 K) →
        ∀ M ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ Y : Subgroup G) : Set G),
          delta A LB M ≤ Subgroup.normalizer
            (oPrimeResidualOf 3 (delta A LB (Subgroup.normalizer (K : Set G))) : Set G)

theorem item155w_iff {A : Subgroup G} :
    Item155w A (lB A) ↔ ∀ Y, IsY155 A Y → One155 A Y ∧ Two155w A Y :=
  ⟨fun h Y hY => h Y hY.1 hY.2.1 hY.2.2, fun h Y hY hX hYX => h Y ⟨hY, hX, hYX⟩⟩

@[expose] noncomputable def Above155w (A X : Subgroup G) : Prop :=
  ∀ Y, IsY155 A Y → X < oPrimeResidualOf 3 Y → One155 A Y ∧ Two155w A Y

@[expose] noncomputable def Item155wR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Item155w A (lB A)

theorem normalizer_le_n155w {A : Subgroup G} (h153 : Item153Main A (lB A)) {K : Subgroup G}
    (hK : K ∈ scriptY0Star A (lB A)) : Subgroup.normalizer (K : Set G) ≤ n155 A K := by
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
  rw [(h153 K hK).1, Set.mem_singleton_iff] at hmem
  exact (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K).trans (hle.trans hmem.le)

theorem two155_of_two155w {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (hN : Step155N A c L) {Y : Subgroup G} (hw : Two155w A Y) : Two155 A Y := by
  intro K hK hhyp M hM
  calc delta A (lB A) M = delta A (lB A) (delta A (lB A) M) := (delta_delta M).symm
    _ ≤ delta A (lB A) (n155 A K) := delta_mono (hw K hK hhyp M hM)
    _ ≤ Subgroup.normalizer (K : Set G) := hN h K hK.1

@[expose] noncomputable def Step155GrowW (A : Subgroup G) (c : G) (L : Subgroup G) : Prop :=
  Sec14Std G A c L → ∀ X K Y M T : Subgroup G, Ctx155 A X K Y M T → MaxT155 A X K T →
    Above155w A X → ¬ K ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) →
      Claim155 A K Y

@[expose] noncomputable def Step155GrowWR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step155GrowW A c L

end CFSG.RankThree.PartTwo.Sec15
