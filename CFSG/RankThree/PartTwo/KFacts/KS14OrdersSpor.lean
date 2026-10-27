module

public import CFSG.RankThree.PartTwo.KFacts.KS14Orders

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS14

open CFSG CFSG.Blueprint

theorem isEmpty_mulEquiv_M22_M12 : IsEmpty (NativeSporadic.M22 ≃* NativeSporadic.M12) :=
  ⟨fun e => by
    have h := Nat.card_congr e.toEquiv
    rw [card_nativeM22, card_nativeM12] at h
    norm_num at h⟩

theorem isEmpty_mulEquiv_M22_J2 : IsEmpty (NativeSporadic.M22 ≃* NativeSporadic.J2) :=
  ⟨fun e => by
    have h := Nat.card_congr e.toEquiv
    rw [card_nativeM22, card_nativeJ2] at h
    norm_num at h⟩

theorem isEmpty_mulEquiv_M12_M22 : IsEmpty (NativeSporadic.M12 ≃* NativeSporadic.M22) :=
  ⟨fun e => isEmpty_mulEquiv_M22_M12.false e.symm⟩

theorem isEmpty_mulEquiv_M12_J2 : IsEmpty (NativeSporadic.M12 ≃* NativeSporadic.J2) :=
  ⟨fun e => by
    have h := Nat.card_congr e.toEquiv
    rw [card_nativeM12, card_nativeJ2] at h
    norm_num at h⟩

end CFSG.RankThree.PartTwo.KFacts.KS14
