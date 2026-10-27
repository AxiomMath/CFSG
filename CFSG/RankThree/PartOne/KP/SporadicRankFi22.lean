module

public import CFSG.RankThree.PartOne.KP.SporadicDefs
public import CFSG.Monster.B.Fischer.Fi22Model
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingOuterBound

public section

namespace CFSG.RankThree.PartOne

open CFSG
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem card_outer_fi22_carrier : Nat.card (Outer Blueprint.NativeSporadic.Fi22) = 2 := by
  obtain ⟨⟨e, -⟩, -⟩ := @CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism
    Blueprint.NativeSporadic.Fi22 Monster.B.Fischer.fi22P Units.instGroup _
    Monster.B.Fischer.fi22PermEquiv
  obtain ⟨f⟩ := Monster.B.Fischer.CTUC_Fi22_full_automorphism_permutation_model.2.2.2.2.2.2.2
  rw [Nat.card_congr e.toEquiv]
  change Nat.card (MulAut Monster.B.Fischer.fi22P ⧸
    (MulAut.conj : Monster.B.Fischer.fi22P →* MulAut Monster.B.Fischer.fi22P).range) = 2
  rw [Nat.card_congr f.toEquiv]
  simp

theorem sporadicCoprimeRank_Fi22 : SporadicCoprimeRank .Fi22 :=
  sporadicCoprimeRank_of_card_outer_le (k := 2) (by norm_num) card_outer_fi22_carrier.le

end CFSG.RankThree.PartOne
