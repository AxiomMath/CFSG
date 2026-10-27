module

public import CFSG.LocalAnalysis.WeakClosure81.OddTranspCompFactorDerivedCases
public import CFSG.OddTranspositions.PartFour.Fourteen.Statements
import CFSG.OddTranspositions.PartFour.ThirteenCompFactorModels
import CFSG.OddTranspositions.PartFour.ThirteenList
import CFSG.OddTranspositions.PartFour.Fourteen.Assembly
import CFSG.OddTranspositions.PartFour.Fourteen.UnitaryShapeRigid
public import CFSG.LocalAnalysis.WeakClosure81.OddTranspCompFactorDerivedEq

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge.Asc72
open CFSG.LocalAnalysis.WeakClosure81 CFSG.LocalAnalysis.WeakClosure81.SevenK CFSG.Open

theorem oddTranspositionCompFactorDerivedEq_of_main (hMain : AscMainTheorem)
    (h3 : OddTranspCompFactorThreeTransp) (h5 : OddTranspCompFactorOFive) :
    OddTranspositionCompFactorDerivedEq := by
  intro X _ _ s hord hodd hncl hrad hder T _ hT hnab
  have hS := setup_setOf_isConj hodd hncl
  by_cases h3T : ∀ d ∈ {x : X | IsConj s x}, ∀ e ∈ {x : X | IsConj s x},
      orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)
  · exact h3 X s hord hodd hncl hrad hder h3T T hT hnab
  suffices hX : OddTranspFactors X from hX T hT hnab
  have hZ : OddTranspFactors (X ⧸ Subgroup.center X) → OddTranspFactors X := fun h =>
    OddTranspFactors.of_normal (Subgroup.center X) (OddTranspFactors.of_commute fun a b =>
      Subtype.ext (Subgroup.mem_center_iff.mp b.2 a.1)) h
  rcases hypEShape_of_ascList hS hder (hMain X _ hS hrad hder) h3T with
    ⟨t, -, m, f, hm, hf, hSp | hU | hO⟩ | ⟨n, hn, b, hb1, hb2, φ, -⟩ | ⟨t, -, f, m, -, hW⟩ |
      ⟨f, hSz⟩
  · obtain ⟨k, -, F, _, _, hF, e, -⟩ := hSp
    exact hZ ((oddTranspFactors_statedSp k hF hf).of_mulEquiv e.symm)
  · rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | hm3
    · obtain ⟨k, -, F, _, _, hF, e, -⟩ := isSymplecticTransvection_of_isUnitaryTransvection_two hU
      exact hZ ((oddTranspFactors_statedSp k hF hf).of_mulEquiv e.symm)
    · obtain ⟨F, _, _, hF, e, -⟩ := hU
      exact hZ ((oddTranspFactors_statedProj_statedSU hm3 hF hf).of_mulEquiv e.symm)
  · rcases hO with ⟨k, hk, -, F, _, _, hF, e, -⟩ | ⟨k, hk, -, F, _, _, hF, b, c, hbc, e, -⟩
    · exact hZ ((oddTranspFactors_orthogonalPlus hk hF hf).of_mulEquiv e.symm)
    · exact hZ ((oddTranspFactors_orthogonalMinus hk hF hf hbc).of_mulEquiv e.symm)
  · refine OddTranspFactors.of_mulEquiv φ.symm ?_
    exact OddTranspFactors.of_surjective (QuotientGroup.mk' (Subgroup.center _))
      (QuotientGroup.mk'_surjective _) (h5 n hn b hb1 hb2)
  · obtain ⟨hf, F, _, _, hF, e, -⟩ := hW
    exact hZ ((oddTranspFactors_wreathSym_sl2 hF hf m).of_mulEquiv e.symm)
  · exact oddTranspFactors_of_isSz hSz

end CFSG.OddTranspositions.PartFour
