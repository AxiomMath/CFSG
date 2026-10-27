module

public import CFSG.Monster.B.GSide.BT2MoveList
public import CFSG.Monster.B.GSide.BT2Block
public import CFSG.Monster.B.GSide.MuFourOmega
public meta import CFSG.Monster.B.GSide.BT2MoveList
public meta import CFSG.Monster.B.GSide.MuFourOmega
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.GSide.BT2BridgeDataInputs
public import CFSG.Monster.B.GSide.BT2BridgeDataWalk
public import Certificates.Certificate3178
public import Certificates.Certificate3179

public section

namespace CFSG.Monster.B.GSide

open SimpleGraph

theorem codeGraph_adj_iff {a b : ℕ} :
    codeGraph.Adj a b ↔ a ≠ b ∧ bWcode a b = 0 ∧ bWcode b a = 0 ∧
      Co2.Native.vectors.contains a = true ∧ Co2.Native.vectors.contains b = true := by
  show codeAdj a b = true ↔ _
  simp only [codeAdj, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, and_assoc]

theorem walkSteps_bridge :
    walkSteps CodeT bridgeWalk bridgeSteps = some .nil :=
  Certificates.certificate3179

theorem homotopicT_bridgeWalk :
    HomotopicT CodeT bridgeWalk .nil :=
  homotopicT_of_walkSteps CodeT walkSteps_bridge

theorem triRel_bridge :
    TriRel codeGraph CodeT 6144 6175 24606 2652785 := by
  intro h₁ h₂ h₃ h₂' h₃'
  have e₁ : HomotopicT CodeT ((triLoop h₁ h₂ h₃).reverse.append (triLoop h₁ h₂' h₃')) .nil := by
    refine HomotopicT.trans ?_ homotopicT_bridgeWalk
    simp only [triLoop, Walk.reverse_cons, Walk.reverse_nil, Walk.nil_append, Walk.cons_append]
    exact HomotopicT.cons _ (HomotopicT.cons _ (homotopicT_cons_cons h₁.symm _))
  have e₂ := HomotopicT.append_left (triLoop h₁ h₂ h₃) e₁
  rw [Walk.append_nil, Walk.append_assoc] at e₂
  have e₃ : HomotopicT CodeT (((triLoop h₁ h₂ h₃).append (triLoop h₁ h₂ h₃).reverse).append
      (triLoop h₁ h₂' h₃')) (triLoop h₁ h₂' h₃') := by
    simpa using HomotopicT.append_right (homotopicT_append_reverse (T := CodeT)
      (triLoop h₁ h₂ h₃)) (triLoop h₁ h₂' h₃')
  exact e₂.symm.trans e₃

end CFSG.Monster.B.GSide
