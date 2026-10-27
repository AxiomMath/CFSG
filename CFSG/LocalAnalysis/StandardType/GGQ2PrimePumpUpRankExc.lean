module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimePumpUpRank
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTorus
public import CFSG.Adapters.TauCetiExceptional.EvenBridgeE6E7
public import CFSG.Adapters.TauCetiExceptional.EvenBridgeE8
public import CFSG.LieType.Chevalley.AdjointCenter

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open CFSG.Models CFSG.Assembly CFSG.StandardType

theorem pumpUpE7Input_holds :
    PumpUpE7Input := by
  intro K _ _ W Wk ζ ξ Q A h hmodel
  obtain ⟨-, hcl | ⟨-, ⟨⟨idx, hv⟩, hnames, ⟨e⟩⟩⟩⟩ := hmodel
  · exact hcl.2.elim
  · cases idx with
    | E7 q =>
      obtain ⟨hp, hf⟩ := hnames
      have hK : Nat.card (ZMod 2) = q.card := by
        rw [Nat.card_zmod, TauCeti.PrimePower.card_def, hp, hf, pow_one]
      obtain ⟨φ⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_E7 q hv hp (ZMod 2) hK
      let eA : CFSG.Blueprint.AdjointQuotient .E7 (ZMod 2) ≃*
          CFSG.Blueprint.Chevalley.adjointGroup .E7 (ZMod 2) :=
        (QuotientGroup.quotientMulEquivOfEq CFSG.LieType.Chevalley.center_adjointGroup_eq_bot).trans
          QuotientGroup.quotientBot
      exact h.false_of_ggTorusLift ((e.trans φ.symm).trans eA) le_rfl
        (TableBExcTwo.ggTorusLift_of_frame (K := ZMod 2) TableBExcTwo.frameE7)
    | _ => simp [NamesTag] at hnames

theorem pumpUpE8Input_holds :
    PumpUpE8Input := by
  intro K _ _ W Wk ζ ξ Q A h hmodel
  obtain ⟨-, hcl | ⟨-, ⟨⟨idx, hv⟩, hnames, ⟨e⟩⟩⟩⟩ := hmodel
  · exact hcl.2.elim
  · cases idx with
    | E8 q =>
      obtain ⟨hp, hf⟩ := hnames
      have hK : Nat.card (ZMod 2) = q.card := by
        rw [Nat.card_zmod, TauCeti.PrimePower.card_def, hp, hf, pow_one]
      obtain ⟨φ⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_E8 q hv hp (ZMod 2) hK
      let eA : CFSG.Blueprint.AdjointQuotient .E8 (ZMod 2) ≃*
          CFSG.Blueprint.Chevalley.adjointGroup .E8 (ZMod 2) :=
        (QuotientGroup.quotientMulEquivOfEq CFSG.LieType.Chevalley.center_adjointGroup_eq_bot).trans
          QuotientGroup.quotientBot
      exact h.false_of_ggTorusLift ((e.trans φ.symm).trans eA) (by norm_num)
        (TableBExcTwo.ggTorusLift_of_frame (K := ZMod 2) TableBExcTwo.frameE8)
    | _ => simp [NamesTag] at hnames

end CFSG.GGQ2Prime
