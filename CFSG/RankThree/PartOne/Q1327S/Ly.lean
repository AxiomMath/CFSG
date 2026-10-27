module

public import CFSG.RankThree.PartOne.Q1327S.Core
public import CFSG.RankThree.PartOne.KS.LyFiveCore
public import CFSG.RankThree.PartOne.Q1327T.Defs

public section

namespace CFSG.RankThree.PartOne.Q1327S

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Q1327T CFSG.Blueprint

theorem false_Ly
    {Q : Type} [Group Q] [Finite Q]
    (e : Q ≃* NativeSporadic.Carrier .Ly) {g : ℕ} {Ē : Subgroup Q} (h : Row8Conf 5 g Q Ē) :
    False := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have := h.elem
  obtain ⟨c, hcE, hc1, Kb, x, hKbc, hKbN, hmodel, hxK, hxo, hgen⟩ := h.conf
  have hcp : c ^ 5 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (A := Ē) c hcE
  have hco : orderOf c = 5 := orderOf_eq_prime hcp hc1
  let e' : Q ≃* CFSG.Sporadic.Ly.J := e.trans CFSG.Sporadic.Ly.lyEquivJ
  have hF := @LyFive.fiveCoreAt'_of_equiv Q CFSG.Sporadic.Ly.J _ inferInstance e'
    LyFive.fiveCore_J c hco
  obtain ⟨hs, hnab⟩ := simple_of_model hmodel
  have hF' : FiveCoreAt' c := hF
  have hKbc' : Kb ≤ Subgroup.centralizer ({c} : Set Q) := hKbc
  exact false_of_fiveCoreAt' hF' hKbc' hKbN hs hnab

end CFSG.RankThree.PartOne.Q1327S
