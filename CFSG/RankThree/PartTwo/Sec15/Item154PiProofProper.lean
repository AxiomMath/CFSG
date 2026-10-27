module

public import CFSG.RankThree.PartTwo.Sec15.Item155RProof
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorSupLeOfCommutatorLeAndNormalize

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

@[expose] noncomputable def Item154ProperR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y ∈ scriptY0 A (lB A), ∀ X ∈ scriptY4 A (lB A), X ≤ Y →
      Y ≠ X ⊔ CFSG.Open.pCoreOf 2 Y →
      ∀ R ∈ invariantPiSubgroups (Subgroup.normalizer (Y : Set G)) (A ⊔ X) (piOf 2),
        ⁅R, Y⁆ ≤ CFSG.Open.pCoreOf 2 Y ∨ Case154Two L Y X ∨ Case154Three A L Y X R

variable {G : Type} [Group G] [Finite G]

theorem commutator_le_pCoreOf_of_eq_sup {X Y R : Subgroup G} (hXY : X ≤ Y)
    (hY : Y = X ⊔ CFSG.Open.pCoreOf 2 Y) (hRY : R ≤ Subgroup.normalizer (Y : Set G))
    (hR2 : IsPGroup 2 R) (hXR : X ≤ Subgroup.normalizer (R : Set G)) :
    ⁅R, Y⁆ ≤ CFSG.Open.pCoreOf 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := CFSG.Open.pCoreOf 2 Y with hP
  have hPY : P ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  have hYP : Y ≤ Subgroup.normalizer (P : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hRP : R ≤ Subgroup.normalizer (P : Set G) :=
    hRY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  have hRX : ⁅R, X⁆ ≤ R ⊓ Y := by
    rw [Subgroup.commutator_le]
    intro r hr x hx
    refine ⟨?_, ?_⟩
    · have h1 : x * r⁻¹ * x⁻¹ ∈ R :=
        (Subgroup.mem_normalizer_iff.mp (hXR hx) r⁻¹).mp (R.inv_mem hr)
      have e : ⁅r, x⁆ = r * (x * r⁻¹ * x⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact R.mul_mem hr h1
    · have h1 : r * x * r⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hRY hr) x).mp (hXY hx)
      rw [commutatorElement_def]
      exact Y.mul_mem h1 (Y.inv_mem (hXY hx))
  have hSP : R ⊓ Y ≤ P := by
    have hD : (R ⊓ Y) ⊔ P ≤ Y := sup_le inf_le_right hPY
    have hD2 : IsPGroup 2 ↥((R ⊓ Y) ⊔ P) :=
      IsPGroup.to_sup_of_normal_right' (hR2.to_le inf_le_left) hP2 (inf_le_right.trans hYP)
    have hXD : X ≤ Subgroup.normalizer (((R ⊓ Y) ⊔ P : Subgroup G) : Set G) :=
      le_normalizer_sup (Late.le_normalizer_inf hXR (hXY.trans Subgroup.le_normalizer))
        (hXY.trans hYP)
    have hPD : P ≤ Subgroup.normalizer (((R ⊓ Y) ⊔ P : Subgroup G) : Set G) :=
      (le_sup_right : P ≤ (R ⊓ Y) ⊔ P).trans Subgroup.le_normalizer
    have hnorm : Y ≤ Subgroup.normalizer (((R ⊓ Y) ⊔ P : Subgroup G) : Set G) :=
      hY.le.trans (sup_le hXD hPD)
    exact le_sup_left.trans
      (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hD hnorm hD2)
  have hXR' : ⁅X, R⁆ ≤ P := by
    rw [Subgroup.commutator_comm]
    exact hRX.trans hSP
  have hPR : ⁅P, R⁆ ≤ P := by
    rw [Subgroup.commutator_le]
    intro p hp r hr
    have h1 : r * p⁻¹ * r⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hRP hr) p⁻¹).mp (P.inv_mem hp)
    have e : ⁅p, r⁆ = p * (r * p⁻¹ * r⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact P.mul_mem hp h1
  have h := CFSG.GorensteinWalter.commutator_sup_le_of_commutator_le_and_normalize X P R P hXR' hPR
    (hXY.trans hYP) Subgroup.le_normalizer
  rw [Subgroup.commutator_comm]
  exact (Subgroup.commutator_mono hY.le le_rfl).trans h

theorem item154R_of_proper (h : Item154ProperR) : Item154R := by
  intro G _ _ A c L hR Y hY X hX hXY R hRm
  by_cases hYX : Y = X ⊔ CFSG.Open.pCoreOf 2 Y
  · refine Or.inl (commutator_le_pCoreOf_of_eq_sup hXY hYX hRm.1 ?_
      (hRm.2.2.trans' le_sup_right))
    exact (isPiSubgroup_piOf_iff Nat.prime_two R).mp hRm.2.1
  · exact h G A c L hR Y hY X hX hXY hYX R hRm

end CFSG.RankThree.PartTwo.Sec15
