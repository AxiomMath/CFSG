module

public import CFSG.Monster.B.TwoA.Sp8.LagrangianRadical
public import CFSG.Quasithin.Background.SimsD1Two
public import CFSG.GroupTheory.ElementaryAbelianTransport

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open Module CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.Short
  CFSG.Monster.B.TwoA CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA.Co2Inv CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open scoped commutatorElement


theorem card_le_of_le_Xgrp {T : Subgroup Dfull} (hTX : T ≤ Xgrp) (hA8 : A8 ≤ T)
    {Λ : Submodule (ZMod 2) V8} (hΛ : IsTotallyIsotropic b0 Λ) (hd : finrank (ZMod 2) Λ = 4)
    (hP : ∀ E : Subgroup Dfull, E ≤ PLam Λ → IsElemAbelian 2 E → Nat.card E ≤ 2 ^ 14) :
    ∀ E : Subgroup Dfull, E ≤ T → IsElemAbelian 2 E → Nat.card E ≤ 2 ^ 14 := by
  intro E hET hE
  obtain ⟨A, hA⟩ := CFSG.Quasithin.exists_isMaxElemAbelian T
  have hEA : Nat.card E ≤ Nat.card A := hA.2.2 E hET hE
  by_cases hAL : A ≤ Lgrp
  · exact hEA.trans (hP A (hAL.trans (Lgrp_le_PLam Λ)) hA.2.1)
  · have hnc : ¬ A ≤ Subgroup.centralizer (A8 : Set Dfull) := by
      rw [Lgrp] at hAL
      exact hAL
    have hU : IsElemAbelian 2 A8 := isElemAbelian_of_isElementaryAbelian
    have hAN : A ≤ Subgroup.normalizer (A8 : Set Dfull) :=
      (hA.1.trans hTX).trans Xgrp_le_normalizer
    obtain ⟨A', hA', hA'le, hq, -⟩ :=
      CFSG.Quasithin.SimsD1.exists_quadratic_replacement (G := Dfull) hU hA8 hAN hA hnc
    have hA'X : A' ≤ Xgrp :=
      hA'le.trans (sup_le (hA.1.trans hTX) (hA8.trans hTX))
    obtain ⟨x, -, hxle⟩ := exists_conj_le_PLam_of_quadratic hA'X hq hΛ hd
    have hA'card : Nat.card A' = Nat.card A :=
      le_antisymm (hA.2.2 A' hA'.1 hA'.2.1) (hA'.2.2 A hA.1 hA.2.1)
    have hCcard : Nat.card (A'.map (MulAut.conj x).toMonoidHom) = Nat.card A' :=
      Subgroup.card_map_of_injective (MulAut.conj x).injective
    have hCe : IsElemAbelian 2 (A'.map (MulAut.conj x).toMonoidHom) :=
      IsElemAbelian.map hA'.2.1 (MulAut.conj x).toMonoidHom
    calc Nat.card E ≤ Nat.card A := hEA
      _ = Nat.card A' := hA'card.symm
      _ = Nat.card (A'.map (MulAut.conj x).toMonoidHom) := hCcard.symm
      _ ≤ 2 ^ 14 := hP _ hxle hCe

end CFSG.Monster.B.TwoA.Sp8
