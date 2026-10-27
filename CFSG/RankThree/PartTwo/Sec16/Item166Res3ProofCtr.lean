module

public import CFSG.RankThree.PartTwo.Sec15.Item15More
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.CGT.PushingUp.TwoLocals
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec16.Item163Proof
public import CFSG.RankThree.PartTwo.Sec16.Item169HJ
public import CFSG.RankThree.PartTwo.Sec17.Item17Q0ProofTools
public import CFSG.RankThree.PartTwo.Sec17.Item17Setup

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

section Steps

@[expose] def Omg166 (A Y₀ : Subgroup G) : Prop :=
  ∀ X ∈ scriptY3Star A (lB A), oPrimeResidualOf 3 X ≠ ⊥ →
    ¬ X ≤ Subgroup.normalizer (Y₀ : Set G) → ∀ X' ∈ scriptY4 A (lB A), X' ≤ X →
      ∀ J ∈ thetaComponentsIn (Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G)),
        J ∈ scriptY0 A (lB A) → X' ≤ J → omg155 A J

@[expose] def Omg166Ctr (A Y₀ : Subgroup G) : Prop :=
  ∀ X ∈ scriptY3Star A (lB A), ¬ Group.IsSolvable ↥X → Group.IsSolvable ↥(pPrimeCoreOf 3 X) →
    oPrimeResidualOf 3 X ≠ ⊥ → ¬ X ≤ Subgroup.normalizer (Y₀ : Set G) →
      ∀ X' ∈ scriptY4 A (lB A), X' ≤ X →
        ∀ J ∈ thetaComponentsIn (Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G)),
          J ∈ scriptY0 A (lB A) → X' ≤ J → omg155 A J

@[expose] def Omg166Sz (A Y₀ : Subgroup G) : Prop :=
  ∀ K₀ Z : Subgroup G, K₀ = delta A (lB A) K₀ →
    (∃ m : ℕ, CFSG.Blueprint.SuzukiModel (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) 2 m) → K₀ ≤ Z →
      Z ∈ scriptY3Star A (lB A) → oPrimeResidualOf 3 Z ≠ ⊥ →
        ¬ Z ≤ Subgroup.normalizer (Y₀ : Set G) → ∀ X' ∈ scriptY4 A (lB A), X' ≤ Z →
          ∀ J ∈ thetaComponentsIn (Subgroup.normalizer (CFSG.Open.pCoreOf 2 Z : Set G)),
            J ∈ scriptY0 A (lB A) → X' ≤ J → omg155 A J

@[expose] def Omega166Three (A Y₀ : Subgroup G) : Prop :=
  ∀ K₀ Z : Subgroup G, K₀ = delta A (lB A) K₀ →
    (∃ m : ℕ, CFSG.Blueprint.SuzukiModel (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) 2 m) → K₀ ≤ Z →
      Z ∈ scriptY3Star A (lB A) → oPrimeResidualOf 3 Z = ⊥ →
        Z ≤ Subgroup.normalizer (Y₀ : Set G)

end Steps

@[expose] def Step166OmgOther : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → ¬ IsL3TwoPow L →
      IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
        Omg166 A Y₀

@[expose] def Step166OmgCtrHJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ →
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
        Omg166Ctr A Y₀

@[expose] def Step166OmgSzHJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ →
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
        Omg166Sz A Y₀

@[expose] def Step166OmegaThreeOther : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → ¬ IsL3TwoPow L →
      IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
        Omega166Three A Y₀

@[expose] def Step166OmegaThreeHJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ →
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
        Omega166Three A Y₀

section StepsA5

@[expose] def Omg166NotA5 (A Y₀ : Subgroup G) : Prop :=
  ∀ X ∈ scriptY3Star A (lB A), oPrimeResidualOf 3 X ≠ ⊥ →
    ¬ X ≤ Subgroup.normalizer (Y₀ : Set G) → ∀ X' ∈ scriptY4 A (lB A), X' ≤ X →
      ∀ J ∈ thetaComponentsIn (Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G)),
        J ∈ scriptY0 A (lB A) → X' ≤ J →
          IsEmpty (↥J ⧸ CFSG.pCore 2 ↥J ≃* alternatingGroup (Fin 5)) → omg155 A J

@[expose] def Ctr166A5 (A Y₀ : Subgroup G) : Prop :=
  ∀ X ∈ scriptY3Star A (lB A), ¬ Group.IsSolvable ↥X → Group.IsSolvable ↥(pPrimeCoreOf 3 X) →
    oPrimeResidualOf 3 X ≠ ⊥ → ∀ X' ∈ scriptY4 A (lB A), X' ≤ X →
      ∀ J ∈ thetaComponentsIn (Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G)),
        J ∈ scriptY0 A (lB A) → X' ≤ J →
          Nonempty (↥J ⧸ CFSG.pCore 2 ↥J ≃* alternatingGroup (Fin 5)) →
            X ≤ Subgroup.normalizer (Y₀ : Set G)

@[expose] def Omega166A5 (A Y₀ : Subgroup G) : Prop :=
  ∀ K₀ Z : Subgroup G, K₀ = delta A (lB A) K₀ →
    (∃ m : ℕ, CFSG.Blueprint.SuzukiModel (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) 2 m) → K₀ ≤ Z →
      Z ∈ scriptY3Star A (lB A) → oPrimeResidualOf 3 Z ≠ ⊥ →
        ∀ X' ∈ scriptY4 A (lB A), X' ≤ Z →
          ∀ J ∈ thetaComponentsIn (Subgroup.normalizer (CFSG.Open.pCoreOf 2 Z : Set G)),
            J ∈ scriptY0 A (lB A) → X' ≤ J →
              Nonempty (↥J ⧸ CFSG.pCore 2 ↥J ≃* alternatingGroup (Fin 5)) →
                Z ≤ Subgroup.normalizer (Y₀ : Set G)

end StepsA5

@[expose] def Step166OmgNotA5HJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ →
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
        Omg166NotA5 A Y₀

@[expose] def Step166CtrA5HJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ →
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
        Ctr166A5 A Y₀

@[expose] def Step166OmegaA5HJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ →
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
        Omega166A5 A Y₀

namespace Proof166Res3

variable {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem le_M_of_y4 (h : Sec17Std G A c L Y₀) (h155 : Item155 A (lB A)) {X : Subgroup G}
    (hX : X ∈ scriptY3 A (lB A)) {Y' : Subgroup G} (hY' : Y' ∈ scriptY3 A (lB A))
    (hY'N : Y' ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G))
    (hY'eq : Y' = oPrimeResidualOf 3 Y' ⊔ CFSG.Open.pCoreOf 2 Y')
    (hK4 : oPrimeResidualOf 3 Y' ∈ scriptY4 A (lB A)) (hΩ : omg155 A (oPrimeResidualOf 3 Y')) :
    X ≤ Subgroup.normalizer (Y₀ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hne, h2⟩ := h155 Y' hY' hK4 hY'eq
  obtain ⟨K', hK'⟩ := hne hΩ
  have hK'Y₀ : K' = Y₀ := h.eq_of_mem_y0Star hK'.1
  set P := CFSG.Open.pCoreOf 2 X with hP
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have hloc : IsPLocal 2 (Subgroup.normalizer (P : Set G)) :=
    CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup hP2 hX.1.2
  obtain ⟨M', hNM', hM'⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge hloc
  have hXN : X ≤ Subgroup.normalizer (P : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hAN : A ≤ Subgroup.normalizer (P : Set G) :=
    hX.1.1.2.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)
  have hmem : M' ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ Y' : Subgroup G) : Set G) :=
    ⟨hM', fun x hx => hNM' (sup_le hAN hY'N hx)⟩
  have hΔ := h2 K' hK' (Or.inl hΩ) M' hmem
  rw [hK'Y₀] at hΔ
  calc X = delta A (lB A) X := hX.2
    _ ≤ delta A (lB A) M' := delta_mono (hXN.trans hNM')
    _ ≤ _ := hΔ

theorem le_M_of_omg (h : Sec17Std G A c L Y₀) (h152 : Item152 A (lB A))
    (h155 : Item155 A (lB A)) {X : Subgroup G} (hX : X ∈ scriptY3 A (lB A)) {X' : Subgroup G}
    (hX'4 : X' ∈ scriptY4 A (lB A)) (hX'X : X' ≤ X)
    (hΩ : ∀ J ∈ thetaComponentsIn (Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G)),
      J ∈ scriptY0 A (lB A) → X' ≤ J → omg155 A J) :
    X ≤ Subgroup.normalizer (Y₀ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) with hN
  have hN2 : N ∈ scriptY2 A := normalizer_pCoreOf_mem_scriptY2 h.isSimpleGroup h.nonabelian hX.1
  have hXN : X ≤ N := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hloc : IsPLocal 2 N :=
    CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) X) hX.1.2
  have hF : generalizedFitting ↥N = CFSG.pCore 2 ↥N :=
    (isCharacteristicP_iff_generalizedFitting_eq_pCore ↥N 2).mp
      (CFSG.CGT.PushingUp.isCharacteristicP_of_isPLocal h.toTheoremFourHyp.charTwoType hloc)
  obtain ⟨J, hJN, hX'J, hJ0⟩ := h152 X' hX'4 N hN2 (hX'X.trans hXN) hF
  have hΩJ := hΩ J hJN hJ0 hX'J
  obtain ⟨hJ4, hJ2⟩ := hJ0
  have hJeq : oPrimeResidualOf 3 J = J := hJ4.2.1.symm
  have hJ3 : J ∈ scriptY3 A (lB A) := ⟨hJ2, hJ4.2.2.1⟩
  refine le_M_of_y4 h h155 hX hJ3 (mem_thetaComponentsIn_iff.mp hJN).1 ?_ (by rw [hJeq]; exact hJ4)
    (by rw [hJeq]; exact hΩJ)
  rw [hJeq]
  exact (sup_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 J)).symm

end Proof166Res3

open Proof166Res3

theorem omg166Ctr_of_omg166 {A Y₀ : Subgroup G} (hΩ : Omg166 A Y₀) : Omg166Ctr A Y₀ :=
  fun X hX _ _ hK hXM => hΩ X hX hK hXM

theorem omg166Sz_of_omg166 {A Y₀ : Subgroup G} (hΩ : Omg166 A Y₀) : Omg166Sz A Y₀ :=
  fun _ Z _ _ _ hZ hO hZM => hΩ Z hZ hO hZM

theorem omg166Ctr_of_a5 {A Y₀ : Subgroup G} (hN : Omg166NotA5 A Y₀) (hA5 : Ctr166A5 A Y₀) :
    Omg166Ctr A Y₀ := by
  intro X hX hns hsol hK hXM X' hX'4 hX'X J hJ hJ0 hX'J
  by_cases h5 : Nonempty (↥J ⧸ CFSG.pCore 2 ↥J ≃* alternatingGroup (Fin 5))
  · exact absurd (hA5 X hX hns hsol hK X' hX'4 hX'X J hJ hJ0 hX'J h5) hXM
  · exact hN X hX hK hXM X' hX'4 hX'X J hJ hJ0 hX'J (not_nonempty_iff.mp h5)

theorem omg166Sz_of_a5 {A Y₀ : Subgroup G} (hN : Omg166NotA5 A Y₀) (hA5 : Omega166A5 A Y₀) :
    Omg166Sz A Y₀ := by
  intro K₀ Z hK₀ hSz hK₀Z hZ hO hZM X' hX'4 hX'Z J hJ hJ0 hX'J
  by_cases h5 : Nonempty (↥J ⧸ CFSG.pCore 2 ↥J ≃* alternatingGroup (Fin 5))
  · exact absurd (hA5 K₀ Z hK₀ hSz hK₀Z hZ hO X' hX'4 hX'Z J hJ hJ0 hX'J h5) hZM
  · exact hN Z hZ hO hZM X' hX'4 hX'Z J hJ hJ0 hX'J (not_nonempty_iff.mp h5)

end CFSG.RankThree.PartTwo.Sec16
