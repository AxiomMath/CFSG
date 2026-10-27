module

public import CFSG.RankThree.GF2n.Smith81.S81E5Uni
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.E7Rep
public import CFSG.RankThree.PartOne.S11c.Sec66TModels

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.E7Model

open CFSG.Blueprint CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors


variable (K : Type) [Field K]

@[expose] def eGrpEquivEAut : ↥(EGrp K) ≃* ↥(EAut K) :=
  (EGrp K).equivMapOfInjective (vAut K).toMonoidHom (vAut K).injective

variable [Finite K] [CharP K 2]

@[expose] def adjointE7EquivEGrp : AdjointQuotient .E7 K ≃* ↥(EGrp K) :=
  ((QuotientGroup.quotientMulEquivOfEq CFSG.LieType.Chevalley.center_adjointGroup_eq_bot).trans
    QuotientGroup.quotientBot).trans (e7Equiv (K := K)).symm

theorem exists_equiv_EGrp_of_lieModel {G : Type} [Group G] {f : ℕ}
    (h : LieModel G .E7 0 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ f ∧
      Nonempty (G ≃* ↥(EGrp K)) := by
  obtain ⟨-, -, L, _, _, hL, ⟨e⟩⟩ :=
    (CFSG.RankThree.PartOne.Sec66T.lieModel_untwisted_iff (G := G) (t := .E7) (τ := .E7) rfl).1 h
  have : CharP L 2 := by
    have := Fintype.ofFinite L
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hL])
  exact ⟨L, inferInstance, inferInstance, this, hL, ⟨e.trans (adjointE7EquivEGrp L)⟩⟩

end CFSG.RankThree.GF2n.Smith81.E7Model
