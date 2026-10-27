module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKUnitary
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Comparator.Defs
import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
import CFSG.LieType.Steinberg.CentralExt.SUTwo
import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6Quot
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Open CFSG.LocalAnalysis.WeakClosure81.SevenK

theorem nonempty_mulEquiv_psl2Model_of_isUnitaryTransvection_two {X : Type} [Group X]
    (hZ : Subgroup.center X = ⊥) {f : ℕ} (hf : 2 ≤ f) {s : X}
    (h : IsUnitaryTransvection X 2 f s) : Nonempty (X ≃* CFSG.Theory.Comparator.PSL2Model f) := by
  obtain ⟨F, _, _, hF, e, -⟩ := h
  have : CharP F 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := f) hF
  have hbot : (StatedScalars (Fin 2) F).subgroupOf (StatedSU 2 (2 ^ f) F) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨(x : GL (Fin 2) F), StatedAPI.statedSU_le_statedSL 2 (2 ^ f) F x.2⟩ :
        StatedSL 2 F) ∈ (StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F) :=
      Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hx)
    rw [StatedAPI.statedScalars_subgroupOf_statedSL_two_eq_bot, Subgroup.mem_bot] at hx'
    exact Subtype.ext (congrArg (fun y : StatedSL 2 F => (y : GL (Fin 2) F)) hx')
  obtain ⟨ζ, hζ0, hζ⟩ := CFSG.LieType.BorelTits.exists_unitaryInvolution_eq_neg hF
  let eSU : Matrix.SpecialLinearGroup (Fin 2) (CFSG.LieType.Steinberg.fixedSubfield F 2 f) ≃*
      StatedSU 2 (2 ^ f) F :=
    (CFSG.LieType.Steinberg.hypEquiv hζ0 hζ).trans
      (CFSG.LieType.Universal.Unitary.equivStatedSU hF 2)
  obtain ⟨eL⟩ := CFSG.ComponentClassification.GMS78.nonempty_SL2_equiv_galois
    (CFSG.LieType.Steinberg.fixedSubfield F 2 f) (by omega)
    (CFSG.LieType.Steinberg.card_fixedSubfield hF)
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans
    (e.trans ((QuotientGroup.quotientMulEquivOfEq hbot).trans
      (QuotientGroup.quotientBot.trans (eSU.symm.trans eL))))⟩

theorem isBenderGroup_of_isUnitaryTransvection_two {X : Type} [Group X]
    (hZ : Subgroup.center X = ⊥) {f : ℕ} (hf : 2 ≤ f) {s : X}
    (h : IsUnitaryTransvection X 2 f s) : CFSG.BenderSuzuki.IsBenderGroup X :=
  let ⟨e⟩ := nonempty_mulEquiv_psl2Model_of_isUnitaryTransvection_two hZ hf h
  .isPSL2 f hf e

theorem nonempty_mulEquiv_psu3Model_of_isUnitaryTransvection_three {X : Type} [Group X]
    (hZ : Subgroup.center X = ⊥) {f : ℕ} (hf : 2 ≤ f) {s : X}
    (h : IsUnitaryTransvection X 3 f s) : Nonempty (X ≃* CFSG.Theory.Comparator.PSU3Model f) := by
  obtain ⟨F, _, _, hF, e, -⟩ := h
  have hcard : Nat.card F = 2 ^ (2 * f) := by rw [hF, ← pow_mul, mul_comm]
  let e' : X ⧸ Subgroup.center X ≃* GLAProj (GLASUGroup (Fin 3) F (2 ^ f)) := e
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans
    ((e'.trans (CFSG.ShultStronglyClosedTI.glaSU3EquivNative f hf hcard)).trans
      (MulEquiv.subgroupCongr (show PSU3 2 f = CFSG.Theory.Comparator.PSU3Model f from rfl)))⟩

theorem isBenderGroup_of_isUnitaryTransvection_three {X : Type} [Group X]
    (hZ : Subgroup.center X = ⊥) {f : ℕ} (hf : 2 ≤ f) {s : X}
    (h : IsUnitaryTransvection X 3 f s) : CFSG.BenderSuzuki.IsBenderGroup X :=
  let ⟨e⟩ := nonempty_mulEquiv_psu3Model_of_isUnitaryTransvection_three hZ hf h
  .isPSU3 f hf e

end CFSG.OddTranspositions.PartFour
