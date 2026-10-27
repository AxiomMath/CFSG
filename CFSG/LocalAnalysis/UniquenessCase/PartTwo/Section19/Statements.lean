module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Defs
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12
open CFSG.LocalAnalysis.UniquenessCase.UC22.F10 (LieAutVocab10)
open CFSG.LocalAnalysis.RankThreeUC
open CFSG.LocalAnalysis.UniquenessCase.UCK (omegaOne)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def Concl19_1 (L : Subgroup G) : Prop :=
  ¬ IsL2 (Bar2 L) 2 ∧ ¬ IsU3 (Bar2 L) 2

@[expose] def R19_1At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp19 D V₀ V p L) : Prop :=
  Concl19_1 L

@[expose] def Concl19_2 (D : Data G) (L K : Subgroup G) : Prop :=
  Opp 3 D.M = L ⊔ K

@[expose] def R19_2At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L K : Subgroup G)
    (h : Ctx19_1 D V₀ V p L K) : Prop :=
  Concl19_2 D L K

@[expose] def Concl19_3 (V₀ L K : Subgroup G) : Prop :=
  ⁅L ⊔ K, V₀⁆ = ⊥

@[expose] def R19_3At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L K : Subgroup G)
    (h : Ctx19_1 D V₀ V p L K) : Prop :=
  Concl19_3 V₀ L K

@[expose] def Concl19_4 (V₀ : Subgroup G) : Prop :=
  mSub V₀ ≤ 4

@[expose] def R19_4At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L K : Subgroup G)
    (h : Ctx19_1 D V₀ V p L K) : Prop :=
  Concl19_4 V₀

@[expose] def Concl19_5 (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ v ∈ V, v ∉ V₀ →
    ∃ Q : Sylow 5 ↥(centModInM D V₀ v),
      (Q : Subgroup ↥(centModInM D V₀ v)).map (centModInM D V₀ v).subtype ≤
        centralizer ({v} : Set G)

@[expose] def R19_5At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L K : Subgroup G)
    (h : Ctx19_1 D V₀ V p L K) : Prop :=
  Concl19_5 D V₀ V

@[expose] def Concl19_6 (D : Data G) (V₀ : Subgroup G) : Prop :=
  ∀ Y : Subgroup G, Y ≤ D.M → Odd (Nat.card Y) → ⁅V₀, Y⁆ ≠ ⊥ →
    normalizer (Y : Set G) ≤ D.M

@[expose] def R19_6At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L K : Subgroup G)
    (h : Ctx19_1 D V₀ V p L K) : Prop :=
  Concl19_6 D V₀

@[expose] def Concl19_7 (D : Data G) (V₀ V : Subgroup G) : Prop :=
  MBarGT D.M V₀ V 3

@[expose] def R19_7At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L K : Subgroup G)
    (h : Ctx19_1 D V₀ V p L K) : Prop :=
  Concl19_7 D V₀ V

@[expose] def Concl19_8_1 (D : Data G) (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) : Prop :=
  ((mSub V₀ + mBar D.M V₀ V hV : ℕ) : ℕ∞) ≤ rMV D.M V ∧
    S18.Concl18_1_2 D V₀ V hV ∧ S18.Concl18_1_3 D V₀ V hV

@[expose] def Concl19_8_2 (D : Data G) (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) : Prop :=
  mBar D.M V₀ V hV = 4

@[expose] def Concl19_8_3 (D : Data G) (V₀ V : Subgroup G) : Prop :=
  gammaN 2 D.M V ≤ ((2 + mSub V₀ : ℕ) : ℕ∞) ∧ 2 + mSub V₀ ≤ 6

@[expose] def Concl19_8_4 (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∃ v ∈ V, v ∉ V₀ ∧ 5 ∉ piSet (centModInM D V₀ v)

@[expose] def R19_8_1At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L K : Subgroup G)
    (h : Ctx19_1 D V₀ V p L K) : Prop :=
  Concl19_8_1 D V₀ V h.hyp.isElemAbelian

@[expose] def R19_8_2At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L K : Subgroup G)
    (h : Ctx19_1 D V₀ V p L K) : Prop :=
  Concl19_8_2 D V₀ V h.hyp.isElemAbelian

@[expose] def R19_8_3At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L K : Subgroup G)
    (h : Ctx19_1 D V₀ V p L K) : Prop :=
  Concl19_8_3 D V₀ V

@[expose] def R19_8_4At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L K : Subgroup G)
    (h : Ctx19_1 D V₀ V p L K) : Prop :=
  Concl19_8_4 D V₀ V

@[expose] def R19_8At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L K : Subgroup G)
    (h : Ctx19_1 D V₀ V p L K) : Prop :=
  R19_8_1At D V₀ V p L K h ∧ R19_8_2At D V₀ V p L K h ∧
    R19_8_3At D V₀ V p L K h ∧ R19_8_4At D V₀ V p L K h

@[expose] def Concl19_9 (L : Subgroup G) : Prop :=
  ¬ IsU5 (Bar2 L) 2 ∧ ¬ IsU4 (Bar2 L) (S17.nOf L)

@[expose] def R19_9At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp19 D V₀ V p L) : Prop :=
  Concl19_9 L

@[expose] def Concl19_10 (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G) : Prop :=
  Setting1910 D V₀ V p L

@[expose] def R19_10At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp19 D V₀ V p L) : Prop :=
  Concl19_10 D V₀ V p L

@[expose] def Concl19_11 (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L A : Subgroup G)
    (t : G) (B : Subgroup G) (r : ℕ) : Prop :=
  ∀ R : Subgroup G, InNM2 D (IOf D p L) B R →
    CFSG.LocalAnalysis.UniquenessCase.UC6.calCGS R ≤ D.M ∧
      UniqueMax D.M (D.M ⊓ normalizer (R : Set G))

@[expose] def R19_11At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L A : Subgroup G)
    (t : G) (B : Subgroup G) (r : ℕ) (h : Ctx19_10 D V₀ V p L A t B r) : Prop :=
  Concl19_11 D V₀ V p L A t B r

@[expose] def Concl19_12 (D : Data G) (A : Subgroup G) (r : ℕ) : Prop :=
  ∀ E : Subgroup G, E ≤ A → IsElemAbelian r E → Nat.card E = r ^ 2 →
    E ∈ uniqueSet D.M

@[expose] def R19_12At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L A : Subgroup G)
    (t : G) (B : Subgroup G) (r : ℕ) (h : Ctx19_10 D V₀ V p L A t B r) : Prop :=
  Concl19_12 D A r

@[expose] def Concl19_13 (D : Data G) (A : Subgroup G) : Prop :=
  3 ∈ piSet A → ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P D.M →
    CFSG.ABGLocalTools.IsSylowOf 3 P ⊤ ∧ IsMulCommutative (omegaOne 3 P)

@[expose] def R19_13At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L A : Subgroup G)
    (t : G) (B : Subgroup G) (r : ℕ) (h : Ctx19_10 D V₀ V p L A t B r) : Prop :=
  Concl19_13 D A

@[expose] def Concl19_14 (D : Data G) (B : Subgroup G) : Prop :=
  muSet D B = ∅

@[expose] def R19_14At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L A : Subgroup G)
    (t : G) (B : Subgroup G) (r : ℕ) (h : Ctx19_10 D V₀ V p L A t B r) : Prop :=
  Concl19_14 D B

@[expose] def Concl19_15 (N : Subgroup G) : Prop :=
  ∀ Lb : Subgroup ↥N, ¬ CFSG.RankThree.PartOne.IsBlockInX Lb

@[expose] def R19_15At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L A : Subgroup G)
    (t : G) (B : Subgroup G) (r : ℕ) (Y N Dsub H S : Subgroup G)
    (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S) : Prop :=
  Concl19_15 N

@[expose] def Concl19_16 (D : Data G) (Dsub : Subgroup G) : Prop :=
  P19_16 D Dsub

@[expose] def R19_16At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L A : Subgroup G)
    (t : G) (B : Subgroup G) (r : ℕ) (Y N Dsub H S : Subgroup G)
    (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S) : Prop :=
  Concl19_16 D Dsub

@[expose] def Concl19_17 (A Dsub : Subgroup G) : Prop :=
  A ≤ normalizer (Dsub : Set G)

@[expose] def R19_17At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L A : Subgroup G)
    (t : G) (B : Subgroup G) (r : ℕ) (Y N Dsub H S : Subgroup G)
    (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S) : Prop :=
  Concl19_17 A Dsub

@[expose] def Concl19_18 (D : Data G) (p : ℕ) (L Dsub : Subgroup G) : Prop :=
  (((P19_16_1 D Dsub ∨ P19_16_2 D Dsub ∨ P19_16_3 D Dsub ∨ P19_16_4 D Dsub) →
      S17.oUpperTwo (Opp 2 (Dsub ⊓ D.M)) ≤ IOf D p L) ∧
    (P19_16_5 D Dsub →
      ∃ (d : ℕ) (K J : Fin d → Subgroup G),
        IsDynkinComponentFamily D Dsub d K J ∧ ∃ i : Fin d, J i ≤ IOf D p L))

@[expose] def R19_18At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L A : Subgroup G)
    (t : G) (B : Subgroup G) (r : ℕ) (Y N Dsub H S : Subgroup G)
    (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S) : Prop :=
  Concl19_18 D p L Dsub

@[expose] def Concl19_19 (D : Data G) (p : ℕ) (L A Dsub : Subgroup G) : Prop :=
  (((P19_16_1 D Dsub ∨ P19_16_2 D Dsub ∨ P19_16_3 D Dsub ∨ P19_16_4 D Dsub) →
      S17.oUpperTwo (Opp 2 (Dsub ⊓ D.M)) ≤ IOf D p L →
        P19_19 D p L A Dsub (S17.oUpperTwo (Opp 2 (Dsub ⊓ D.M)))) ∧
    (P19_16_5 D Dsub →
      ∀ (d : ℕ) (K J : Fin d → Subgroup G), IsDynkinComponentFamily D Dsub d K J →
        ∀ i : Fin d, J i ≤ IOf D p L → P19_19 D p L A Dsub (J i)))

@[expose] def R19_19At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L A : Subgroup G)
    (t : G) (B : Subgroup G) (r : ℕ) (Y N Dsub H S : Subgroup G)
    (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S) : Prop :=
  Concl19_19 D p L A Dsub

@[expose] def Concl19_20_1 (D : Data G) (Dsub : Subgroup G) : Prop :=
  P19_16_5 D Dsub

@[expose] def Concl19_20_2 (D : Data G) (p : ℕ) (L Dsub : Subgroup G) : Prop :=
  ∀ (d : ℕ) (K J : Fin d → Subgroup G), IsDynkinComponentFamily D Dsub d K J →
    ∀ i : Fin d, J i ≤ IOf D p L → P19_19_1 D p L (J i)

@[expose] def R19_20_1At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L A : Subgroup G)
    (t : G) (B : Subgroup G) (r : ℕ) (Y N Dsub H S : Subgroup G)
    (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S) : Prop :=
  Concl19_20_1 D Dsub

@[expose] def R19_20_2At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L A : Subgroup G)
    (t : G) (B : Subgroup G) (r : ℕ) (Y N Dsub H S : Subgroup G)
    (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S) : Prop :=
  Concl19_20_2 D p L Dsub

@[expose] def R19_20At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L A : Subgroup G)
    (t : G) (B : Subgroup G) (r : ℕ) (Y N Dsub H S : Subgroup G)
    (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S) : Prop :=
  R19_20_1At D V₀ V p L A t B r Y N Dsub H S h ∧
    R19_20_2At D V₀ V p L A t B r Y N Dsub H S h

@[expose] def Concl19_21 (D : Data G) (p : ℕ) (L Dsub : Subgroup G) : Prop :=
  ∀ (d : ℕ) (K J : Fin d → Subgroup G) (i : Fin d),
    IsDynkinComponentFamily D Dsub d K J → J i ≤ IOf D p L →
      ¬ P19_19_1 D p L (J i)

@[expose] def R19_21At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L A : Subgroup G)
    (t : G) (B : Subgroup G) (r : ℕ) (Y N Dsub H S : Subgroup G)
    (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S) : Prop :=
  Concl19_21 D p L Dsub

@[expose] def Concl19_22 (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L A : Subgroup G)
    (t : G) (B : Subgroup G) (r : ℕ) : Prop :=
  ∃ A₀ : Subgroup G, Ctx19_22 D V₀ V p L A t B r A₀

@[expose] def R19_22At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L A : Subgroup G)
    (t : G) (B : Subgroup G) (r : ℕ) (h : Ctx19_10 D V₀ V p L A t B r) : Prop :=
  Concl19_22 D V₀ V p L A t B r

@[expose] def Concl19_23 (A₀ : Subgroup G) : Prop :=
  pCoreOf 2 (centralizer (A₀ : Set G)) = ⊥

@[expose] def R19_23At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L A : Subgroup G)
    (t : G) (B : Subgroup G) (r : ℕ) (A₀ : Subgroup G)
    (h : Ctx19_22 D V₀ V p L A t B r A₀) : Prop :=
  Concl19_23 A₀

@[expose] def Concl19_24_1 (V₀ H : Subgroup G) : Prop :=
  ⁅V₀, Oodd H⁆ = ⊥

@[expose] def Concl19_24_2 (V₀ H : Subgroup G) : Prop :=
  ∀ K : Subgroup G, K ≤ H → CFSG.IsComponent (K.subgroupOf H) →
    V₀ ≤ normalizer (K : Set G)

@[expose] def R19_24_1At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L A : Subgroup G)
    (t : G) (B : Subgroup G) (r : ℕ) (A₀ H : Subgroup G)
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H) : Prop :=
  Concl19_24_1 V₀ H

@[expose] def R19_24_2At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L A : Subgroup G)
    (t : G) (B : Subgroup G) (r : ℕ) (A₀ H : Subgroup G)
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H) : Prop :=
  Concl19_24_2 V₀ H

@[expose] def Concl19_25 (D : Data G) (p : ℕ) (L A H : Subgroup G) : Prop :=
  ((A ⊔ pCoreOf 2 (H ⊓ IOf D p L)).subgroupOf (H ⊓ D.M)).Normal

@[expose] def R19_25At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L A : Subgroup G)
    (t : G) (B : Subgroup G) (r : ℕ) (A₀ H : Subgroup G)
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H) : Prop :=
  Concl19_25 D p L A H

@[expose] def Concl19_26 (L : Subgroup G) : Prop :=
  Odd (S17.nOf L)

@[expose] def R19_26At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L A : Subgroup G)
    (t : G) (B : Subgroup G) (r : ℕ) (A₀ H : Subgroup G)
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H) : Prop :=
  Concl19_26 L

@[expose] def Concl19_27 (A H : Subgroup G) : Prop :=
  ∀ K : Subgroup G, K ≤ H → CFSG.IsComponent (K.subgroupOf H) →
    A ≤ normalizer (K : Set G)

@[expose] def R19_27At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L A : Subgroup G)
    (t : G) (B : Subgroup G) (r : ℕ) (A₀ H : Subgroup G)
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H) : Prop :=
  Concl19_27 A H

@[expose] def Concl19_28 (D : Data G) (A H : Subgroup G) : Prop :=
  ∀ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 S (H ⊓ D.M) →
    Permutes A S ∧ (pCoreOf 2 (A ⊔ S)).relIndex S ≤ 2 ∧
      CFSG.ABGLocalTools.IsSylowOf 2 S H

@[expose] def R19_28At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L A : Subgroup G)
    (t : G) (B : Subgroup G) (r : ℕ) (A₀ H : Subgroup G)
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H) : Prop :=
  Concl19_28 D A H

@[expose] def Concl19_29 (V : LieAutVocab10) (D : Data G) (V₀ A H E K A₀ S : Subgroup G)
    (r : ℕ) : Prop :=
  E ≤ A → IsElemAbelian r E → Nat.card E = r ^ 2 →
    K ≤ H → CFSG.IsComponent (K.subgroupOf H) → ActsFaithfullyOn V₀ K →
      CFSG.ABGLocalTools.IsSylowOf 2 S (H ⊓ D.M) → P19_29 V K E A₀ S

@[expose] def R19_29At (V : LieAutVocab10) (D : Data G) (V₀ Vsub : Subgroup G) (p : ℕ)
    (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ) (A₀ H E K S : Subgroup G)
    (h : Ctx19_23 D V₀ Vsub p L A t B r A₀ H) : Prop :=
  Concl19_29 V D V₀ A H E K A₀ S r

@[expose] def R19_glue_1At (D : Data G) (V₀ V : Subgroup G) (h : Hyp125 D V₀ V)
    (hbig : 1 < mSub V₀) (hσ : D.sig.Nonempty) : Prop :=
  ∃ p L, Hyp19 D V₀ V p L

@[expose] def R19_glue_1 (D : Data G) : Prop :=
  ∀ V₀ V (h : Hyp125 D V₀ V) (hbig : 1 < mSub V₀) (hσ : D.sig.Nonempty),
    R19_glue_1At D V₀ V h hbig hσ

@[expose] def R19_glue_2At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp19 D V₀ V p L) (hshape : IsL2 (Bar2 L) 2 ∨ IsU3 (Bar2 L) 2) : Prop :=
  ∃ K, Ctx19_1 D V₀ V p L K

@[expose] def R19_glue_4At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp19 D V₀ V p L) (h1910 : Setting1910 D V₀ V p L) : Prop :=
  ∃ A t B r, Ctx19_10 D V₀ V p L A t B r

@[expose] def R19_glue_5At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L A : Subgroup G)
    (t : G) (B : Subgroup G) (r : ℕ) (h : Ctx19_10 D V₀ V p L A t B r)
    (Y N : Subgroup G) (hY : Y ∈ muStarSet D B) (hN : N ∈ calMOf Y ∧ N ≠ D.M) : Prop :=
  ∃ Dsub, Dsub ∈ calC N ∧ ¬ Dsub ≤ D.M ∧ pCoreOf 2 Dsub ≤ D.M

@[expose] def R19_glue_6At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L A : Subgroup G)
    (t : G) (B : Subgroup G) (r : ℕ) (A₀ H : Subgroup G)
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H) : Prop :=
  ∃ K : Subgroup G, K ≤ H ∧ CFSG.IsComponent (K.subgroupOf H) ∧ ActsFaithfullyOn V₀ K

@[expose] def R19_glue_6 (D : Data G) : Prop :=
  ∀ V₀ V p L A t B r A₀ H (h : Ctx19_23 D V₀ V p L A t B r A₀ H),
    R19_glue_6At D V₀ V p L A t B r A₀ H h

@[expose] def R19_glue_7At (V : LieAutVocab10) (D : Data G) (V₀ Vsub : Subgroup G) (p : ℕ)
    (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ) (A₀ H E K S : Subgroup G)
    (h : Ctx19_23 D V₀ Vsub p L A t B r A₀ H)
    (hE : E ≤ A) (hEel : IsElemAbelian r E) (hEcard : Nat.card E = r ^ 2)
    (hK : K ≤ H) (hKcomp : CFSG.IsComponent (K.subgroupOf H))
    (hfaith : ActsFaithfullyOn V₀ K) (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (H ⊓ D.M))
    (h29 : P19_29 V K E A₀ S) : Prop :=
  False

@[expose] def Sec19Contra (D : Data G) : Prop :=
  ∀ V₀ V : Subgroup G, Hyp125 D V₀ V → 1 < mSub V₀ → False

@[expose] def Sec19ContraOf1669 (D : Data G) : Prop :=
  ∀ V₀ V : Subgroup G, Hyp125 D V₀ V → 2 < Nat.card V₀ →
    (Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) → False

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
