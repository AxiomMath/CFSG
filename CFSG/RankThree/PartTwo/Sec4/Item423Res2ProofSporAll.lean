module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofSporM12
public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofSporFix
public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofAlt
public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofSpor

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.Blueprint
open Res423Two

@[expose] def K423SporJ3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* NativeSporadic.Carrier .J3) → Census423 X

@[expose] def K423SporJ4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* NativeSporadic.Carrier .J4) → Census423 X

@[expose] def K423SporMcL : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* NativeSporadic.Carrier .McL) → Census423 X

theorem k423Inner46FiveSimple_of
    (hθ : K423SporThetaCent) (hJ3 : K423SporJ3) (hJ4 : K423SporJ4) (hMcL : K423SporMcL) :
    K423Inner46FiveSimple := by
  rintro X _ _ ⟨s, hs, ⟨e⟩⟩ hJ - hZ -
  simp only [sporadics46, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact census423_of_m11 hZ e
  · exact census423_of_m12 hZ e
  · exact census423_of_m22 e
  · exact census423_of_m23 hθ hZ e
  · exact census423_of_m24 hθ hZ e
  · exact census423_of_j1 e
  · exact absurd ⟨e⟩ hJ
  · exact hJ3 X ⟨e⟩
  · exact hJ4 X ⟨e⟩
  · exact hMcL X ⟨e⟩
  · exact census423_of_hs hθ hZ e
  · exact census423_of_he hθ hZ e
  · exact census423_of_ru hθ hZ e

theorem k423InnerCensus_of_spor
    (h3 : K423Inner46Three) (hθ : K423SporThetaCent) (hJ3 : K423SporJ3) (hJ4 : K423SporJ4)
    (hMcL : K423SporMcL) (h6 : K423Inner46SixRest) (h7 : K423Inner46Seven)
    (h8 : K423Inner46Eight) : K423InnerCensus :=
  k423InnerCensus_of_open h3 k423Inner46FourAlt (k423Inner46FiveSimple_of hθ hJ3 hJ4 hMcL) h6 h7 h8

end CFSG.RankThree.PartTwo.Sec4
