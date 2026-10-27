module

public import CFSG.RankThree.PartTwo.Sec4.E27.D4Main
public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxMain

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.Seitz CFSG.Open TauCeti CFSG.RankThree.PartOne.CTP
open CFSG.RankThree.PartTwo.Sec19 CFSG.RankThree.PartTwo.Sec11
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec4.E27

section StepALayer


variable {n : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

theorem layer_le_closure_fixed (P : D4Par n X σ) (hn : 2 ≤ n)
    {E : Subgroup (MulAut (C0 σ))} (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 27)
    (hno : ∀ φ : MulAut (C0 σ), tauAut σ ∉ E.map (MulAut.congr φ).toMonoidHom)
    {x : C0 σ} (hx : MulAut.conj x ∈ E) (hx1 : x ≠ 1) :
    ⁅Subgroup.centralizer ({x} : Set (C0 σ)), Subgroup.centralizer ({x} : Set (C0 σ))⁆ ≤
      Subgroup.closure
        {l | l ∈ ⁅Subgroup.centralizer ({x} : Set (C0 σ)), Subgroup.centralizer ({x} : Set (C0 σ))⁆ ∧
          ∃ y ∈ E, y ∉ Subgroup.zpowers (MulAut.conj x : MulAut (C0 σ)) ∧ y l = l} :=
  layer_le_closure_fixed_aux CFSG.Goldschmidt.topStatement P hn hE hcard hno hx hx1

theorem stepALayerAll : StepALayerAll := fun _ _ _ _ _ P hn E hE hcard hno x hx hx1 =>
  layer_le_closure_fixed P hn hE hcard hno hx hx1

theorem seitz27_trialityD4_final_layer :
    ∀ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 2 →
      2 ≤ q.exponent → ∀ (Y : Type) [Group Y] [Finite Y],
        Nonempty (Y ≃* Cat ⟨TauCeti.LieTypeIndex.trialityD4 q, hq⟩) → Seitz27 Y :=
  seitz27_trialityD4_layer_of_stepA stepALayerAll

end StepALayer

end CFSG.RankThree.PartTwo.Sec4.E27
