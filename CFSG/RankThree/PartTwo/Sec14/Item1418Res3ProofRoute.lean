module

public import CFSG.RankThree.PartTwo.Sec14.Item1418Res3ProofDefs
public import CFSG.RankThree.PartTwo.Sec14.Item1418Res2Proof1418
import CFSG.RankThree.PartTwo.Sec14.Item1418Res3ProofPL
import CFSG.RankThree.PartTwo.Sec14.Item1418Res3ProofOff
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS
open scoped commutatorElement

namespace Proof1418Res3

variable {G : Type} [Group G] [Finite G]

theorem commutator_zpowers_eq {A B U : Subgroup G} {c' : G} (hc'A : c' ∈ A)
    (hBA : B ≤ A) (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hAa : A = Subgroup.zpowers c' ⊔ B)
    (hUB : U ≤ Subgroup.centralizer (B : Set G)) (hUA : ⁅U, A⁆ = U) :
    ⁅U, Subgroup.zpowers c'⁆ = U := by
  refine le_antisymm ((Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hc'A)).trans
    hUA.le) ?_
  conv_lhs => rw [← hUA]
  rw [Subgroup.commutator_le]
  intro u hu a ha
  have hle : Subgroup.zpowers c' ≤ Subgroup.normalizer (B : Set G) := by
    refine Subgroup.zpowers_le.mpr (mem_normalizer_of_conj_mem fun x hx => ?_)
    rw [hAab c' hc'A x (hBA hx), mul_inv_cancel_right]
    exact hx
  have ha' : a ∈ ((Subgroup.zpowers c' ⊔ B : Subgroup G) : Set G) := by
    rw [← hAa]
    exact ha
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle] at ha'
  obtain ⟨y, hy, d, hd, rfl⟩ := ha'
  dsimp only
  have hdu : d * u = u * d := Subgroup.mem_centralizer_iff.mp (hUB hu) d hd
  have hdu' : d * u⁻¹ = u⁻¹ * d := (Commute.inv_right hdu).eq
  have e : ⁅u, y * d⁆ = ⁅u, y⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc u * (y * d) * u⁻¹ * (y * d)⁻¹ = u * y * (d * u⁻¹) * d⁻¹ * y⁻¹ := by group
      _ = u * y * (u⁻¹ * d) * d⁻¹ * y⁻¹ := by rw [hdu']
      _ = u * y * u⁻¹ * y⁻¹ := by group
  rw [e]
  exact Subgroup.commutator_mem_commutator hu hy

end Proof1418Res3

open Proof1418Res3

theorem step1418OffR_of_layer (h : Step1418OffLayerR) : Step1418OffR := by
  intro G _ _ A c L hR hfail S hS B hB hSB b hbB hbΓ huniq hall hW hWL E hE hEΩ R hRE hR2 hAR hRb
  have hD := hR.toSec14Std.toSec13Data
  have hA : IsE27 A := hR.toSec14Std.isE27
  obtain ⟨hA3, hAab, hAmax⟩ := max_of_sec13 hD
  have hbA : b ∈ A := hB.1 hbB
  have hbE : b ∉ E := fun hbE => hEΩ _ hbΓ.1 (Subgroup.zpowers_le.mpr hbE)
  exact le_pPrimeCoreOf_of_centralizes_layer hA3 hAab hAmax hE.1 hbA
    (Proof1418Res2.eq_sup_zpowers_of_not_mem hA hE hbA hbE) hRE hR2 (hAR hbA) hRb
    (h G A c L hR hfail S hS B hB hSB b hbB hbΓ huniq hall hW hWL E hE hEΩ R hRE hR2 hAR hRb)

theorem step1422IQBR_of_layer
    (h131 : Item131) (h : Step1422IQBLayerR) : Step1422IQBR := by
  intro G _ _ A c L hR hfail c' hc'Γ L' hL' hφ hBW hTr U hUB hU2 hAU hUA
  obtain ⟨φ⟩ := id hφ
  have hS' := Proof1413.sec14Std_at hR.toSec14Std hc'Γ.1 hL'
  have hD' := hS'.toSec13Data
  obtain ⟨hc'L, -, hAa, -⟩ := Proof1413Res2.m22_point h131 hD' φ
  obtain ⟨hA3, hAab, hAmax⟩ := max_of_sec13 hD'
  have hc'A : c' ∈ A := hD'.mem_A
  have hAEb : A = (A ⊓ L') ⊔ Subgroup.zpowers c' := by
    rw [sup_comm]
    exact hAa
  have hUc := commutator_zpowers_eq hc'A inf_le_left hAab hAa hUB hUA
  exact le_pPrimeCoreOf_of_centralizes_layer hA3 hAab hAmax inf_le_left hc'A hAEb hUB hU2
    (hAU hc'A) hUc (h G A c L hR hfail c' hc'Γ L' hL' hφ hBW hTr U hUB hU2 hAU hUA)

end CFSG.RankThree.PartTwo.Sec14
