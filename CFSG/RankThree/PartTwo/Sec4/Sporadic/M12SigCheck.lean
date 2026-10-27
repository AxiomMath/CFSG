module

public import CFSG.RankThree.PartTwo.Sec4.Sporadic.M12SigData
public import CFSG.RankThree.PartTwo.Toolkit.M12Local
public meta import CFSG.RankThree.PartTwo.Sec4.Sporadic.M12SigData
public meta import CFSG.RankThree.PartTwo.Toolkit.M12Local
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.M12SigCheckInputs
public import Certificates.Certificate8170
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.RankThree.PartTwo.Sec4.Sporadic.M12Sig

open CFSG.GH74.M12.Hyp CFSG.RankThree.PartTwo.Toolkit.M12 CFSG.RankThree.PartTwo Subgroup
open scoped commutatorElement

theorem sig_invariant_E :
    invariantPiSubgroups ⊤ basisE.sub (piOf 2) = {⊥} :=
  Certificates.certificate8170.1

theorem sig_invariant_F :
    invariantPiSubgroups ⊤ basisF.sub (piOf 2) = {⊥} :=
  Certificates.certificate8170.2.1

theorem sig_mem_C {i : ℕ} (hi : i < 3) {g : G12}
    (hg : g * (⁅x, y⁆ ^ i * (x * y)) = ⁅x, y⁆ ^ i * (x * y) * g) :
    ∃ k ∈ idxC i, tbl g.1 = prodT k :=
  Certificates.certificate8170.2.2.1 i hi g hg

theorem sig_le_V {Y : Subgroup G12}
    (hY : Y ∈ invariantPiSubgroups ⊤ basisA.sub (piOf 2)) (hne : Y ≠ ⊥) :
    ∃ i < 3, ∀ y ∈ Y, tbl y.1 ∈ VT i :=
  Certificates.certificate8170.2.2.2.1 Y hY hne

theorem sig_inner (α : MulAut G12)
    (hα : ∀ f ∈ basisA.sub, α f = f) : α ∈ (MulAut.conj : G12 →* MulAut G12).range :=
  Certificates.certificate8170.2.2.2.2.1 α hα

theorem sig_small :
    chkNormal = true ∧ chkVStruct = true ∧ chkGamma = true ∧ CFSG.KC.M12Sig.centL = true :=
  Certificates.certificate8170.2.2.2.2.2

end CFSG.RankThree.PartTwo.Sec4.Sporadic.M12Sig
