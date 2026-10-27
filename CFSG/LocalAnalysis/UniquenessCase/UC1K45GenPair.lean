module

public import CFSG.HardMathSupport.RichardWeiss.Proving.AltFivePairConj
public import TauCeti.GroupTheory.Perm.Recognition

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

open Equiv Equiv.Perm
open CFSG.HardMathSupport.RichardWeiss.Proving

theorem a5_order_three_conj (a b : ↥(alternatingGroup (Fin 5))) (ha : orderOf a = 3)
    (hb : orderOf b = 3) : ∃ g : ↥(alternatingGroup (Fin 5)), g * a * g⁻¹ = b := by
  have ha3 : IsThreeCycle (a : Perm (Fin 5)) :=
    isThreeCycle_of_orderOf_eq_three (by decide) (by rw [Subgroup.orderOf_coe, ha])
  have hb3 : IsThreeCycle (b : Perm (Fin 5)) :=
    isThreeCycle_of_orderOf_eq_three (by decide) (by rw [Subgroup.orderOf_coe, hb])
  exact isConj_iff.mp (alternatingGroup.isThreeCycle_isConj (by simp) ha3 hb3)

@[expose] def a5GenPairSigma : ↥(alternatingGroup (Fin 5)) := altFiveU

@[expose] def a5GenPairG0 : ↥(alternatingGroup (Fin 5)) :=
  ⟨Equiv.swap 1 3 * Equiv.swap 2 4,
    mul_mem_alternatingGroup_of_isSwap
      (swap_isSwap_iff.mpr (by decide)) (swap_isSwap_iff.mpr (by decide))⟩

@[expose] def a5GenPairTau : ↥(alternatingGroup (Fin 5)) :=
  ⟨Equiv.swap 0 3 * Equiv.swap 3 4,
    IsThreeCycle.mem_alternatingGroup (card_support_eq_three_iff.mp (by decide))⟩

theorem a5GenPair_g0_conj :
    a5GenPairG0 * a5GenPairSigma * a5GenPairG0⁻¹ = a5GenPairTau := by
  apply Subtype.ext
  decide

theorem a5GenPair_supports :
    ((a5GenPairSigma : Perm (Fin 5)).support ∩
      (a5GenPairTau : Perm (Fin 5)).support).card = 1 := by
  decide

theorem a5GenPair_closure_eq_top :
    Subgroup.closure ({a5GenPairSigma, a5GenPairTau} : Set ↥(alternatingGroup (Fin 5))) = ⊤ := by
  have hσ : (a5GenPairSigma : Perm (Fin 5)).support.card = 3 := by decide
  have hτ : (a5GenPairTau : Perm (Fin 5)).support.card = 3 := by decide
  have hclosPerm : Subgroup.closure ({(a5GenPairSigma : Perm (Fin 5)),
      (a5GenPairTau : Perm (Fin 5))} : Set (Perm (Fin 5))) = alternatingGroup (Fin 5) :=
    closure_pair_threeCycles_eq_alt5 _ _ hσ hτ a5GenPair_supports
  have himg : (alternatingGroup (Fin 5)).subtype '' ({a5GenPairSigma, a5GenPairTau} :
      Set ↥(alternatingGroup (Fin 5))) =
      ({(a5GenPairSigma : Perm (Fin 5)), (a5GenPairTau : Perm (Fin 5))} :
        Set (Perm (Fin 5))) := by
    rw [Set.image_pair]; rfl
  apply Subgroup.map_subtype_inj.mp
  rw [MonoidHom.map_closure, himg, hclosPerm, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem a5_conj_gen (a : ↥(alternatingGroup (Fin 5))) (ha : orderOf a = 3) :
    ∃ g : ↥(alternatingGroup (Fin 5)), Subgroup.closure {a, g * a * g⁻¹} = ⊤ := by
  have hσ3 : IsThreeCycle (a5GenPairSigma : Perm (Fin 5)) :=
    card_support_eq_three_iff.mp (by decide)
  have hσ0ord : orderOf a5GenPairSigma = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact hσ3.orderOf
  obtain ⟨h, hh⟩ := a5_order_three_conj a5GenPairSigma a hσ0ord ha
  let g : ↥(alternatingGroup (Fin 5)) := h * a5GenPairG0 * h⁻¹
  refine ⟨g, ?_⟩
  have hga : g * a * g⁻¹ = h * a5GenPairTau * h⁻¹ := by
    show (h * a5GenPairG0 * h⁻¹) * a * (h * a5GenPairG0 * h⁻¹)⁻¹ =
      h * a5GenPairTau * h⁻¹
    rw [← hh, ← a5GenPair_g0_conj]
    group
  let φ : ↥(alternatingGroup (Fin 5)) →* ↥(alternatingGroup (Fin 5)) := MulAut.conj h
  have hσ0conj : φ a5GenPairSigma = a := by
    change h * a5GenPairSigma * h⁻¹ = a
    exact hh
  have hτ0conj : φ a5GenPairTau = g * a * g⁻¹ := by
    change h * a5GenPairTau * h⁻¹ = g * a * g⁻¹
    exact hga.symm
  have hset : φ '' ({a5GenPairSigma, a5GenPairTau} :
      Set ↥(alternatingGroup (Fin 5))) = ({a, g * a * g⁻¹} :
        Set ↥(alternatingGroup (Fin 5))) := by
    rw [Set.image_pair, hσ0conj, hτ0conj]
  have hmain : Subgroup.closure ({a, g * a * g⁻¹} : Set ↥(alternatingGroup (Fin 5))) = ⊤ := by
    rw [← hset, ← MonoidHom.map_closure φ, a5GenPair_closure_eq_top]
    exact Subgroup.map_equiv_top (MulAut.conj h)
  exact hmain

end CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

end
