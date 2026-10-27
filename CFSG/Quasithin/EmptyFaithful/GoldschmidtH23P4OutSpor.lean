module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4OutBase
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Sporadic.Schreier.M11
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAut
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22
public import CFSG.Sporadic.Schreier.M23
public import CFSG.Sporadic.Schreier.MathieuOddCoreM24
public import CFSG.Sporadic.Schreier.PairHePairs

public section

namespace CFSG.Quasithin.H23Out

section M11


theorem noFiveOut_of_isSporadic_M11 {X : Type} [Group X] [Finite X]
    (h : IsSporadic .M11 X) : NoFiveOut X := by
  obtain ⟨e⟩ := h
  exact NoFiveOut.of_equiv_card_outer_le e
    (CFSG.Sporadic.Schreier.at_m11_schreier.1.trans (by norm_num))

theorem out5Pow_of_isSporadic_M11 {X : Type} [Group X] [Finite X]
    (h : IsSporadic .M11 X) : Out5Pow X :=
  Out5Pow.of_noFiveOut (noFiveOut_of_isSporadic_M11 h)

end M11

section M12


theorem noFiveOut_of_isSporadic_M12 {X : Type} [Group X] [Finite X]
    (h : IsSporadic .M12 X) : NoFiveOut X := by
  obtain ⟨e⟩ := h
  exact NoFiveOut.of_equiv_card_outer_le e
    (CFSG.ComponentClassification.M12Cover.card_outer.le.trans (by norm_num))

theorem out5Pow_of_isSporadic_M12 {X : Type} [Group X] [Finite X]
    (h : IsSporadic .M12 X) : Out5Pow X :=
  Out5Pow.of_noFiveOut (noFiveOut_of_isSporadic_M12 h)

end M12

section M22


theorem noFiveOut_of_isSporadic_M22 {X : Type} [Group X] [Finite X]
    (h : IsSporadic .M22 X) : NoFiveOut X := by
  obtain ⟨e⟩ := h
  exact NoFiveOut.of_equiv_card_mulAut_le e CFSG.Sporadic.Schreier.m22_center_eq_bot'
    (CFSG.Sporadic.Schreier.m22_mulAut_card.trans (Nat.mul_le_mul_right _ (by norm_num)))

theorem out5Pow_of_isSporadic_M22 {X : Type} [Group X] [Finite X]
    (h : IsSporadic .M22 X) : Out5Pow X :=
  Out5Pow.of_noFiveOut (noFiveOut_of_isSporadic_M22 h)

end M22

section M23


theorem noFiveOut_of_isSporadic_M23 {X : Type} [Group X] [Finite X]
    (h : IsSporadic .M23 X) : NoFiveOut X := by
  obtain ⟨e⟩ := h
  exact NoFiveOut.of_equiv_card_outer_le e
    (CFSG.Sporadic.Schreier.at_m23_schreier.1.trans (by norm_num))

theorem out5Pow_of_isSporadic_M23 {X : Type} [Group X] [Finite X]
    (h : IsSporadic .M23 X) : Out5Pow X :=
  Out5Pow.of_noFiveOut (noFiveOut_of_isSporadic_M23 h)

end M23

section M24


theorem noFiveOut_of_isSporadic_M24 {X : Type} [Group X] [Finite X]
    (h : IsSporadic .M24 X) : NoFiveOut X := by
  obtain ⟨e⟩ := h
  exact NoFiveOut.of_equiv_card_mulAut_le e CFSG.Sporadic.Schreier.m24_center_eq_bot'
    (CFSG.Sporadic.Schreier.m24_mulAut_card.trans
      (Nat.le_mul_of_pos_left _ (by norm_num)))

theorem out5Pow_of_isSporadic_M24 {X : Type} [Group X] [Finite X]
    (h : IsSporadic .M24 X) : Out5Pow X :=
  Out5Pow.of_noFiveOut (noFiveOut_of_isSporadic_M24 h)

end M24

section He


theorem noFiveOut_of_isSporadic_He {X : Type} [Group X] [Finite X]
    (h : IsSporadic .He X) : NoFiveOut X := by
  obtain ⟨e⟩ := h
  exact NoFiveOut.of_equiv_card_outer_le e
    (CFSG.Sporadic.Schreier.AT_He_Schreier.1.trans (by norm_num))

theorem out5Pow_of_isSporadic_He {X : Type} [Group X] [Finite X]
    (h : IsSporadic .He X) : Out5Pow X :=
  Out5Pow.of_noFiveOut (noFiveOut_of_isSporadic_He h)

end He

end CFSG.Quasithin.H23Out
