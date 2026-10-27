module

public import CFSG.RankThree.PartOne.K133B.Defs
public import CFSG.RankThree.PartOne.Q1327S.Conf
public import CFSG.RankThree.PartOne.Q1327S.Cube
public import CFSG.RankThree.PartOne.Census3.NativeForm
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartOne.CTP.SporadicNoncomm
public import CFSG.RankThree.PartOne.CTP.SporadicOrders

public section

namespace CFSG.RankThree.PartOne.K133B

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Q1327T CFSG.Blueprint TauCeti

section Sporadic

theorem row8OddItem_five : Row8OddItem 5 := by
  intro Q _ _ p g Ē hp11 hZ hS h hW
  exfalso
  obtain ⟨s, hs, ⟨e0⟩⟩ := hS
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hsimple : IsSimpleGroup (Q ⧸ Subgroup.center Q) := h.quasisimple.2.1
  have : IsSimpleGroup (CFSGIndex.sporadic s).Group := e0.symm.isSimpleGroup
  obtain ⟨e1⟩ := Census3.nonempty_carrier_mulEquiv_of_mem hs
  let e : Q ⧸ Subgroup.center Q ≃* NativeSporadic.Carrier s := e0.trans e1.symm
  let eQ : Q ≃* NativeSporadic.Carrier s :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e
  have hsq : p ^ 2 ∣ Nat.card (NativeSporadic.Carrier s) := by
    rw [← Nat.card_congr eQ.toEquiv]
    exact Q1327S.p_sq_dvd_card h
  have := h.elem
  have hcen : ∀ P : Subgroup Q, IsPGroup p P → Ē ≤ P → P ≤ Subgroup.centralizer (Ē : Set Q) :=
    fun P hP hEP => Q1327S.le_centralizer_of_weyl_coprime
      (fun y hy hyp => Q1327S.mem_of_pow_eq_one h hZ hy hyp) hW hP hEP
  rcases CTP.sporadicPair_of_sq_dvd hs hp h.five_le hsq with hNC | hAb
  · rcases hNC with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hJ : StrongP.HasNoncommPair 11 (NativeSporadic.Carrier .J4) := CTP.hasNoncommPair_J4
      have hN : StrongP.HasNoncommPair 11 Q := hJ.map eQ.symm.toMonoidHom eQ.symm.injective
      have hcard : Nat.card Q = Nat.card (NativeSporadic.Carrier .J4) := Nat.card_congr eQ.toEquiv
      have h3 : 11 ^ 3 ∣ Nat.card (NativeSporadic.Carrier .J4) := by
        rw [show Nat.card (NativeSporadic.Carrier .J4) = 86775571046077562880 from
          CFSG.Sporadic.J4.card_J4]
        norm_num
      have h4 : ¬ 11 ^ 4 ∣ Nat.card (NativeSporadic.Carrier .J4) := by
        rw [show Nat.card (NativeSporadic.Carrier .J4) = 86775571046077562880 from
          CFSG.Sporadic.J4.card_J4]
        norm_num
      exact Q1327S.false_of_noncomm_cube hp h.card (by rw [hcard]; exact h3)
        (by rw [hcard]; exact h4) hN hcen
    all_goals omega
  · rcases hAb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega

end Sporadic

end CFSG.RankThree.PartOne.K133B
