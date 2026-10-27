module

public import CFSG.LieType.SteinbergBRTwoRankBound
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveKBasic
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s1611e3_card_le_four_mulAut_l3 {S : Type} [Group S] (hS : IsL3 S 1)
    {E : Subgroup (MulAut S)} (hE : IsElemAbelian 2 E) : Nat.card E ≤ 4 := by
  obtain ⟨e⟩ := CFSG.SeitzReduction.LinearPilot.nonempty_equiv_GL32_of_lieModel hS
  set Φ := MulAut.congr e
  haveI : Finite (MulAut S) := Finite.of_equiv _ Φ.symm.toEquiv
  have hcard : Nat.card (MulAut S) = 336 := by
    rw [Nat.card_congr Φ.toEquiv, CFSG.LieType.SteinbergBR.AutGL32.card_mulAut_GL32]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CFSG.IsElementaryAbelian 2 E :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 E).mpr hE
  have h := CFSG.LieType.SteinbergBR.card_le_sq_of_orderOf
    (g := Φ.symm CFSG.LieType.SteinbergBR.AutGL32.alphaAut) (k := 3)
    (by rw [MulEquiv.orderOf_eq, CFSG.LieType.SteinbergBR.AutGL32.orderOf_alphaAut])
    (by rw [hcard]; norm_num) E
  simpa using h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
