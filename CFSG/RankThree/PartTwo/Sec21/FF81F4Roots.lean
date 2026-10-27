module

public import CFSG.RankThree.PartTwo.Sec21.FF81F4InvCheck
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcF4Classes
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107F3SF4DatumBits
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoInputsEndNode

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.F4

open CFSG.LieType.Simplicity.TitsBits CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree
open CFSG.ComponentClassification.RankTwoExceptional.F4Sec8
open CFSG.StandardType.TableBF4TwoInputs CFSG.LieType.Chevalley.RootOps
open CFSG.LocalAnalysis.GLTheoremA.F4Sym (hasBits_pinnedX_one)

@[expose] def certPos (p : ℕ) : ℕ :=
  [3, 2, 10, 1, 8, 17, 7, 25, 15, 0, 5, 16, 24, 13, 31, 22, 21, 36, 30, 40, 44, 35, 39,
    43].getD (p - 24) 0

theorem certPos_spec : ∀ p : Fin 24, certPos (24 + p) <
      ReeTag.F4.tag.rootCertificate.roots.length ∧
    ReeTag.F4.tag.rootCertificate.root (certPos (24 + p)) =
      orbitCertRoot ReeTag.F4.tag (24 + p) := by
  decide +kernel

section Bits

variable
  {K : Type} [Field K] [CharP K 2]

theorem hasBits_f4Rep_single (p : ℕ) (hp : 24 ≤ p ∧ p ≤ 47) :
    HasBits K (f4Rep K [p]) (rb (certPos p)) := by
  have h := certPos_spec ⟨p - 24, by omega⟩
  have e : 24 + (p - 24) = p := by omega
  simp only [e] at h
  have hr := f4_isRoot_pos hp
  have hb := hasBits_pinnedX_one (K := K) hr.1 h.1 h.2
  have e' : f4Rep K [p] =
      ⟨pinnedX ReeTag.F4.tag K (orbitCertRoot ReeTag.F4.tag p) 1, pinnedX_mem_adjointGroup _ 1⟩ :=
    Subtype.ext (by rw [coe_f4Rep_singleton]; rfl)
  rw [e']
  exact hb

end Bits

end CFSG.RankThree.PartTwo.Sec21.FF81.F4
