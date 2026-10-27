module

public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofHJ

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] noncomputable def Step1515HJD : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ Y ∈ scriptY0Star A (lB A), MeetsY4 A (lB A) L Y →
      Y = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y → L = (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 L →
      omegaA A ≠ {Subgroup.zpowers c} →
        ∃ d ∈ A, d ≠ 1 ∧
          (∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 S L ∧
            (Subgroup.center S).map S.subtype = Subgroup.zpowers d) ∧
          ⁅CFSG.Open.pCoreOf 2 Y, Subgroup.zpowers c⁆ ≤ Subgroup.centralizer ({d} : Set G) ∧
          Odd (Nat.card ↥(Subgroup.normalizer (Y : Set G) ⊓
            pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G))))

@[expose] noncomputable def Step1515HJVTail : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ Y ∈ scriptY0Star A (lB A), MeetsY4 A (lB A) L Y →
      Y = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y → L = (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 L →
      omegaA A ≠ {Subgroup.zpowers c} →
      ∀ d ∈ A, d ≠ 1 →
        (∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 S L ∧
          (Subgroup.center S).map S.subtype = Subgroup.zpowers d) →
        ⁅CFSG.Open.pCoreOf 2 Y, Subgroup.zpowers c⁆ ≤ Subgroup.centralizer ({d} : Set G) →
        Odd (Nat.card ↥(Subgroup.normalizer (Y : Set G) ⊓
          pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)))) →
          CFSG.Open.pCoreOf 2 Y ≤ Subgroup.centralizer ({c} : Set G)

@[expose] noncomputable def Step1515HJEndTail : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ Y ∈ scriptY0Star A (lB A), MeetsY4 A (lB A) L Y →
      Y = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y → L = (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 L →
      omegaA A ≠ {Subgroup.zpowers c} →
      ∀ d ∈ A, d ≠ 1 →
        (∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 S L ∧
          (Subgroup.center S).map S.subtype = Subgroup.zpowers d) →
        Odd (Nat.card ↥(Subgroup.normalizer (Y : Set G) ⊓
          pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)))) →
          ¬ Y ≤ Subgroup.centralizer ({c} : Set G)

theorem step1515HJV_of_tail (hD : Step1515HJD) (hT : Step1515HJVTail) : Step1515HJV := by
  intro G _ _ A c L h hJ Y hY hm hYL hLY hΩ
  obtain ⟨d, hdA, hd1, hdS, hVd, hP⟩ := hD G A c L h hJ Y hY hm hYL hLY hΩ
  exact hT G A c L h hJ Y hY hm hYL hLY hΩ d hdA hd1 hdS hVd hP

theorem step1515HJEnd_of_tail (hD : Step1515HJD) (hT : Step1515HJEndTail) :
    Step1515HJEnd := by
  intro G _ _ A c L h hJ Y hY hm hYL hLY hΩ
  obtain ⟨d, hdA, hd1, hdS, -, hP⟩ := hD G A c L h hJ Y hY hm hYL hLY hΩ
  exact hT G A c L h hJ Y hY hm hYL hLY hΩ d hdA hd1 hdS hP

theorem step1515HJ_of_tails (hD : Step1515HJD) (hVT : Step1515HJVTail)
    (hET : Step1515HJEndTail) : Step1515HJ :=
  step1515HJ_of (step1515HJV_of_tail hD hVT) (step1515HJEnd_of_tail hD hET)

end CFSG.RankThree.PartTwo.Sec15
