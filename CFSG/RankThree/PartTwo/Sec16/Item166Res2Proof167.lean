module

public import CFSG.RankThree.PartTwo.Sec16.Item167StepsProof
public import CFSG.RankThree.PartTwo.Sec16.Item169GeneralDefs
import CFSG.RankThree.PartTwo.Sec16.Item169General

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Steps

variable (A : Subgroup G) (LB : Subgroup G → Subgroup G) (c : G) (L : Subgroup G)

@[expose] noncomputable def Step167EmptyCent : Prop :=
  ∀ Y ∈ scriptY1Star A LB, Hyp1673 A LB c L Y → scriptY0 A LB = ∅ →
    generalizedFitting ↥Y ≠ CFSG.pCore 2 ↥Y → pPrimeCoreOf 2 Y ≠ ⊥ →
      A ≤ Subgroup.centralizer (pPrimeCoreOf 2 Y : Set G) →
        Y ⊓ Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer (pPrimeCoreOf 2 Y : Set G)

end Steps

@[expose] noncomputable def Step167EmptyCentR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step167EmptyCent A (lB A) c L

@[expose] noncomputable def Step167O2LocNot2nR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ¬ IsL3TwoPow L → Step167O2Loc A (lB A) c L

namespace Proof167Res2

variable {A : Subgroup G} {c : G} {L : Subgroup G}

theorem step167O2Loc_of_l3TwoPow (h : Sec15R G A c L) (h163 : Item163 A (lB A) c L)
    (h164 : Item164 A (lB A) c) (hM : Claim17M A (lB A)) (hMeets : Step163Meets)
    (h1514 : Item1514 A (lB A) c L) (h1510 : Item1510 A) (hBr : Step169TwoBridge)
    (h165 : Item165S17) (hL : IsL3TwoPow L) : Step167O2Loc A (lB A) c L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro Y hY _ _ Y₀ hY₀ _ _ _
  have hne : (scriptY0 A (lB A)).Nonempty := ⟨Y₀, hY₀.prop⟩
  have hL34 := rank3II_16_9_2_of h hne h163 hMeets h1514 h1510 hBr
  obtain ⟨Y₁, hs⟩ := exists_sec17Std h ⟨hne, hL34⟩ h163 h164 hM
  have hYM : Y ≤ Subgroup.normalizer (Y₀ : Set G) := h165 G A c L Y₁ hs hL Y₀ hY₀ Y hY.prop.1
  have hMT : Subgroup.normalizer (Y₀ : Set G) ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y₀ : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀
  refine ⟨CFSG.Open.pCoreOf 2 Y₀, hY₀.prop.2.2, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y₀,
    sup_le (sup_le (hY₀.prop.1.1.2.trans hMT) ?_) (hYM.trans hMT)⟩
  exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₀

theorem step167Empty_of_cent (h : Sec15R G A c L) (h149 : Item149 A (lB A))
    (h146 : Item146 A (lB A)) (hcent : Step167EmptyCent A (lB A) c L) :
    Step167Empty A (lB A) c L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro Y hY hH h0 hF
  obtain ⟨hY3s, hsol, hX, hhyp⟩ := id hH
  obtain ⟨hZ1, hYAX, hZX, hZA⟩ := facts1673 h h149 h146 hY hsol hF
  have hA3 : IsPGroup 3 A := h.toSec14Std.isE27.isPGroup
  obtain ⟨⟨hY2, -⟩, hYo⟩ := hY.prop
  have hY3' : ¬ 3 ∣ Nat.card Y := not_three_dvd_of_oPrimeResidualOf_eq_bot hYo
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY2.1.2
  set X := deltaZero A (lB A) Y with hXdef
  set Z := pPrimeCoreOf 2 Y with hZdef
  have hXY : X ≤ Y := deltaZero_le Y
  have hYZ : Y ≤ Subgroup.normalizer (Z : Set G) := le_normalizer_pPrimeCoreOf 2 Y
  have hXZ : X ≤ Subgroup.centralizer (Z : Set G) := by
    have hAZ : ⁅A, Z⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hZA
    have h1 : ⁅⁅A, Z⁆, X⁆ = ⊥ := by rw [hAZ, Subgroup.commutator_bot_left]
    have h2 : ⁅⁅Z, X⁆, A⁆ = ⊥ := by
      have hZXZ : ⁅Z, X⁆ ≤ Z :=
        Subgroup.le_normalizer_iff_commutator_le_left.mp (hXY.trans hYZ)
      have hZA' : ⁅Z, A⁆ = ⊥ := by rw [Subgroup.commutator_comm, hAZ]
      exact le_bot_iff.mp (hZA' ▸ Subgroup.commutator_mono hZXZ le_rfl)
    have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
    rw [← deltaZero_eq_commutator Y] at h3
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3
  have hCA := hcent Y hY hH h0 hF hZ1 hZA
  have hYC : Y ≤ Subgroup.centralizer (Z : Set G) := by
    rw [CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization 3
      Nat.prime_three A Y hA3 hY3' hAY]
    exact sup_le (hYAX.trans hXZ) hCA
  have hZcen : CFSG.pPrimeCore 2 ↥Y ≤ Subgroup.center ↥Y := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hzZ : (z : G) ∈ Z := ⟨z, hz, rfl⟩
    exact (Subgroup.mem_centralizer_iff.mp (hYC y.2) z hzZ).symm
  exact generalizedFitting_eq_pCore_sup_center hZcen

end Proof167Res2

theorem step167O2LocR_of_not2n (h163 : Item163R) (h164 : Item164R) (hM : Claim17MR)
    (hMeets : Step163Meets) (h1514 : Item1514R) (h1510 : Item1510R) (hBr : Step169TwoBridge)
    (h165 : Item165S17) (hNot : Step167O2LocNot2nR) : Step167O2LocR := by
  intro G _ _ A c L h
  by_cases hL : IsL3TwoPow L
  · exact Proof167Res2.step167O2Loc_of_l3TwoPow h (h163 G A c L h) (h164 G A c L h)
      (hM G A c L h) hMeets (h1514 G A c L h) (h1510 G A c L h) hBr h165 hL
  · exact hNot G A c L h hL

theorem step167EmptyR_of_cent (h149 : Item149S14) (h146 : Sec14.Item146S14)
    (hcent : Step167EmptyCentR) : Step167EmptyR := fun G _ _ A c L h =>
  Proof167Res2.step167Empty_of_cent h (h149 G A c L h.toSec14Std) (h146 G A c L h.toSec14Std)
    (hcent G A c L h)

end CFSG.RankThree.PartTwo.Sec16
