module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LOrder60
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2FamLieOrd
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieEnd
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG.HardMathSupport.Solomon.Coordinator

theorem not_alt5_isLie (hb : LieOrderBridge) (d : TauCeti.ValidLieTypeIndex) :
    ¬ Nonempty (alternatingGroup (Fin 5) ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  intro hf
  have h1 := hb d (alternatingGroup (Fin 5)) hf
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin] at h1
  exact lieOrderFormula_ne_60 d.2 (by rw [← h1]; decide)

theorem not_isChevSimple_alt5 (hb : LieOrderBridge) {q : ℕ} (hq2 : q ≠ 2) (hq5 : q ≠ 5) :
    ¬ CFSG.Yardstones.Md0ec50421ce4.IsChevSimple q (alternatingGroup (Fin 5)) := by
  rintro (⟨i, hi, hf⟩ | ⟨i, hi, hf⟩)
  · cases i with
    | lie d => exact not_alt5_isLie hb d hf
    | _ => exact False.elim hi
  · cases i with
    | lie d => exact not_alt5_isLie hb d hf
    | alternating n hn =>
      obtain ⟨f⟩ := hf
      have hc : Nat.card (alternatingGroup (Fin 5)) = Nat.card (alternatingGroup (Fin n)) :=
        Nat.card_congr f.toEquiv
      rcases hi with ⟨rfl, h25⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
      · rcases h25 with h | h
        · exact hq2 h
        · exact hq5 h
      all_goals
        rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin,
          Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin] at hc
        norm_num [Nat.factorial] at hc
    | _ => exact False.elim hi

theorem not_ON_isLie (hb : LieOrderBridge)
    (d : TauCeti.ValidLieTypeIndex) :
    ¬ Nonempty (CFSG.Blueprint.NativeSporadic.ON ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  intro hf
  have hcard := CFSG.Sporadic.ON.card_ON_eq
  have hfin : Finite CFSG.Blueprint.NativeSporadic.ON :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have h1 := hb d CFSG.Blueprint.NativeSporadic.ON hf
  rw [hcard] at h1
  exact GFR2Lie.lieOrderFormula_ne_onOrd d.2 (by rw [← h1]; rfl)

theorem not_isChevSimple_ON (hb : LieOrderBridge) {q : ℕ} :
    ¬ CFSG.Yardstones.Md0ec50421ce4.IsChevSimple q CFSG.Blueprint.NativeSporadic.ON := by
  have hcard := CFSG.Sporadic.ON.card_ON_eq
  rintro (⟨i, hi, hf⟩ | ⟨i, hi, hf⟩)
  · cases i with
    | lie d => exact not_ON_isLie hb d hf
    | _ => exact False.elim hi
  · cases i with
    | lie d => exact not_ON_isLie hb d hf
    | alternating n hn =>
      obtain ⟨f⟩ := hf
      have hc : Nat.card CFSG.Blueprint.NativeSporadic.ON =
          Nat.card (alternatingGroup (Fin n)) := Nat.card_congr f.toEquiv
      rw [hcard] at hc
      rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
      · rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin] at hc
        norm_num [Nat.factorial] at hc
    | _ => exact False.elim hi

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
