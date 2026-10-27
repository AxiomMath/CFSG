module

public import CFSG.RankThree.PartTwo.Sec15.Item15More
public import CFSG.RankThree.PartTwo.Sec15.Item153

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

noncomputable abbrev n155 (A K : Subgroup G) : Subgroup G :=
  Subgroup.normalizer
    (oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (K : Set G))) : Set G)

@[expose] noncomputable def IsY155 (A Y : Subgroup G) : Prop :=
  Y ∈ scriptY3 A (lB A) ∧ oPrimeResidualOf 3 Y ∈ scriptY4 A (lB A) ∧
    Y = oPrimeResidualOf 3 Y ⊔ CFSG.Open.pCoreOf 2 Y

@[expose] noncomputable def One155 (A Y : Subgroup G) : Prop :=
  omg155 A (oPrimeResidualOf 3 Y) → (gam155 A (lB A) Y (oPrimeResidualOf 3 Y)).Nonempty

@[expose] noncomputable def Two155 (A Y : Subgroup G) : Prop :=
  ∀ K ∈ gam155 A (lB A) Y (oPrimeResidualOf 3 Y),
    (omg155 A (oPrimeResidualOf 3 Y) ∨ K = oPrimeResidualOf 3 Y ⊔ CFSG.Open.pCoreOf 2 K) →
    ∀ M ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ Y : Subgroup G) : Set G),
      delta A (lB A) M ≤ Subgroup.normalizer (K : Set G)

theorem item155_iff {A : Subgroup G} :
    Item155 A (lB A) ↔ ∀ Y, IsY155 A Y → One155 A Y ∧ Two155 A Y :=
  ⟨fun h Y hY => h Y hY.1 hY.2.1 hY.2.2, fun h Y hY hX hYX => h Y ⟨hY, hX, hYX⟩⟩

structure Ctx155 (A X K Y M T : Subgroup G) : Prop where
  isY : IsY155 A Y
  res : oPrimeResidualOf 3 Y = X
  mem_k : K ∈ scriptY0Star A (lB A)
  le_k : X ≤ K
  hyp : omg155 A X ∨ K = X ⊔ CFSG.Open.pCoreOf 2 K
  norm_k : Y ≤ Subgroup.normalizer (K : Set G)
  mem_m : M ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ Y : Subgroup G) : Set G)
  not_le : ¬ delta A (lB A) M ≤ n155 A K
  mem_t : T ∈ scriptQPiStar A (lB A) Y (piOf 2)

@[expose] noncomputable def MaxT155 (A X K T : Subgroup G) : Prop :=
  ∀ Y' M' T' : Subgroup G, Ctx155 A X K Y' M' T' → Nat.card T' ≤ Nat.card T

@[expose] noncomputable def Claim155 (A K Y : Subgroup G) : Prop :=
  ∀ C : Subgroup G, C ≠ ⊥ → C ≤ CFSG.Open.pCoreOf 2 Y →
    (C.subgroupOf (CFSG.Open.pCoreOf 2 Y)).Characteristic →
      delta A (lB A) (Subgroup.normalizer (C : Set G)) ≤ n155 A K

@[expose] noncomputable def Case154Two (L Y X : Subgroup G) : Prop :=
  ∃ n m : ℕ, 1 ≤ n ∧ 1 ≤ m ∧
    Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 (2 * n * m))) ∧
    IsLThreeEpsAt (↥X ⧸ CFSG.pCore 2 ↥X) 2 n ∧
    L ≠ (L ⊓ X) ⊔ CFSG.Open.pCoreOf 2 L

@[expose] noncomputable def Case154Three (A L Y X R : Subgroup G) : Prop :=
  Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
    Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* alternatingGroup (Fin 5)) ∧
    (centralizerSection Y (CFSG.Open.pCoreOf 2 Y)).relIndex R = 4 ∧
    (∀ r ∈ R, r ^ 2 ∈ centralizerSection Y (CFSG.Open.pCoreOf 2 Y)) ∧
    ∀ d ∈ A, d ≠ 1 → IsThreeCentralIn L d →
      R ⊓ Subgroup.centralizer ({d} : Set G) ≤ centralizerSection Y (CFSG.Open.pCoreOf 2 Y)

@[expose] noncomputable def Hyp322 (H R : Subgroup G) : Prop :=
  R ≤ H ∧ generalizedFitting ↥H = CFSG.pCore 2 ↥H ∧
    Nonempty (↥H ⧸ CFSG.pCore 2 ↥H ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
    Nonempty ((R.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ≃*
      Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧
    Nonempty (Subgroup.centralizer
        (((R.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) :
          Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) : Set (↥H ⧸ CFSG.pCore 2 ↥H)) ≃*
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) × alternatingGroup (Fin 5))

@[expose] noncomputable def Hyp315 (H S : Subgroup G) : Prop :=
  S ≤ H ∧ generalizedFitting ↥H = CFSG.pCore 2 ↥H ∧
    ((∃ n : ℕ, 1 ≤ n ∧ Even n ∧ Nonempty (oResidual 2 (↥H ⧸ CFSG.pCore 2 ↥H) ≃*
          CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 n))) ∨
      Sec4.IsTripleCover (oResidual 2 (↥H ⧸ CFSG.pCore 2 ↥H)) (alternatingGroup (Fin 6)) ∨
      Nonempty (oResidual 2 (↥H ⧸ CFSG.pCore 2 ↥H) ≃* alternatingGroup (Fin 7))) ∧
    ∃ A' : Subgroup ↥H, CFSG.Assembly.IsElemAbelian 3 A' ∧
      (∀ B : Subgroup ↥H, CFSG.Assembly.IsElemAbelian 3 B → A' ≤ B → B = A') ∧
      S.subgroupOf H ∈ maxInvariantPiSubgroups ⊤ A' (piOf 2)

noncomputable abbrev u155 (A M X : Subgroup G) : Subgroup G :=
  delta A (lB A) M ⊓ centralizerSection X (CFSG.Open.pCoreOf 2 X)

noncomputable abbrev b155 (A M X : Subgroup G) : Subgroup G :=
  oPrimeResidualOf 3 (u155 A M X)

@[expose] noncomputable def Step155Up (A : Subgroup G) (c : G) (L : Subgroup G) : Prop :=
  Sec14Std G A c L → ∀ Y, IsY155 A Y →
    (¬ ∃ n : ℕ, 1 ≤ n ∧ Sec4.IsoLThreePi (↥(oPrimeResidualOf 3 Y) ⧸
      CFSG.pCore 2 ↥(oPrimeResidualOf 3 Y)) 2 n) →
    IsEmpty (↥(oPrimeResidualOf 3 Y) ⧸ CFSG.pCore 2 ↥(oPrimeResidualOf 3 Y) ≃*
      alternatingGroup (Fin 5)) →
    (¬ ∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧ L' ∈ lA A c' ∧
      L' = (L' ⊓ oPrimeResidualOf 3 Y) ⊔ CFSG.Open.pCoreOf 2 L') →
    ∀ M ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ Y : Subgroup G) : Set G),
    ∀ J ∈ thetaComponentsIn M, J ∈ scriptY0 A (lB A) → oPrimeResidualOf 3 Y < J →
    ∀ K ∈ scriptY0Star A (lB A), J ≤ K → omg155 A J ∨ K = J ⊔ CFSG.Open.pCoreOf 2 K

@[expose] noncomputable def Step155N (A : Subgroup G) (c : G) (L : Subgroup G) : Prop :=
  Sec14Std G A c L → ∀ K ∈ scriptY0Star A (lB A),
    delta A (lB A) (n155 A K) ≤ Subgroup.normalizer (K : Set G)

theorem step155N_of_claim153Normal {A : Subgroup G} {c : G} {L : Subgroup G}
    (h149 : Item149 A (lB A)) (hn : Claim153Normal A (lB A)) : Step155N A c L := by
  intro h K hK
  have heq := normalizer_x_eq_of_normal h h149 hn hK
  change delta A (lB A) (Subgroup.normalizer
    (oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (K : Set G))) : Set G)) ≤ _
  rw [heq]
  exact delta_le _

end CFSG.RankThree.PartTwo.Sec15
