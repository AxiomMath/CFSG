module

public import CFSG.OddTranspositions.O4PairF25FieldData
public import CFSG.OddTranspositions.PSL2FieldAutFixed
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.OddTranspositions.QZ

open CFSG.GorensteinWalter

theorem three_mem_fixedSubfield : (3 : K25) ∈ fixedSubfield := by
  change (3 : K25) ∈ (fixedSubfield : Set K25)
  rw [fixedSubfield_eq_primeField]
  exact ⟨(3 : ZMod 5), by exact map_ofNat _ 3⟩

theorem sqrt3_sq_mem_fixedSubfield : sqrt3 ^ 2 ∈ fixedSubfield := by
  rw [sqrt3_sq]
  exact three_mem_fixedSubfield

theorem card_fix_psl2_frob25 :
    Nat.card {q : PSL225 // q = psl2FieldAut K25 frob25 q} = 120 := by
  have hEq : {q : PSL225 | psl2FieldAut K25 frob25 q = q} =
      (CFSG.Glauberman.Dickson.MaxSubfield.subfieldSubgroup fixedSubfield : Set PSL225) :=
    fix_psl2FieldAut_eq_subfieldSubgroup frob25 frob25_mul_self fixedSubfield
      (fun x => mem_fixedSubfield) sqrt3 sqrt3_sq_mem_fixedSubfield
      sqrt3_not_mem_fixedSubfield
  calc Nat.card {q : PSL225 // q = psl2FieldAut K25 frob25 q}
      = Nat.card {q : PSL225 // psl2FieldAut K25 frob25 q = q} :=
        Nat.card_congr (Equiv.subtypeEquivRight fun q => eq_comm)
    _ = Nat.card (CFSG.Glauberman.Dickson.MaxSubfield.subfieldSubgroup fixedSubfield) :=
        Nat.card_congr (Equiv.subtypeEquivProp hEq)
    _ = 120 := card_subfieldSubgroup_fixedSubfield

end CFSG.OddTranspositions.QZ
