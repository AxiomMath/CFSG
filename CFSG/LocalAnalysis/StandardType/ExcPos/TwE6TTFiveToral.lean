module

public import CFSG.LocalAnalysis.StandardType.GGFinModelRootCompatDefs
public import CFSG.LocalAnalysis.StandardType.GGTwE6KGA1Defs
public import Certificates.Certificate115
public import Certificates.Certificate116
import CFSG.LocalAnalysis.StandardType.GGLieCoreToralInd
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcToralityFive
import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
import CFSG.RankThree.PartOne.KE.E7FiveBlock
import CFSG.RankThree.PartOne.KE.SLnShape
import CFSG.RankThree.PartOne.KE.ThreeA1Group

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType.GGFinModel
  CFSG.Open
open CFSG.StandardType.NoOffTwE6Three (IsToralE6)

theorem isToralE6_of_le_ggFixGp_five
    {f : ℕ} {E : Subgroup (ModGL (langTag .twistedE6) GGL)} (hE : E ≤ ggFixGp .twistedE6 f)
    (hel : IsElemAbelian 5 E) (hfin : Finite E) : IsToralE6 GGL E := by
  have halg : letI := ZMod.algebra GGL 2; Algebra.IsAlgebraic (ZMod 2) GGL := by
    have h : ZMod.algebra GGL 2 = (inferInstance : Algebra (ZMod 2) GGL) := Subsingleton.elim _ _
    rw [h]
    exact AlgebraicClosure.isAlgebraic (ZMod 2)
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact CFSG.StandardType.LieCore.isToralSubgroup_of_familyStabilizer_le (τ := Tag.E6) (p := 5)
    (L := GGL) (ℓ := 2)
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.monomialToralAt_E6_five (by decide) halg
    (fun _ _ _ ha => CFSG.HardMathSupport.C14Lattice.familyStabilizer_le_reflection Nat.prime_five
      (Or.inr CFSG.HardMathSupport.C14Lattice.sylowCert_E6_5) ha)
    (fun x hx => (hE hx).1) hfin
    (fun x hx y hy => congrArg Subtype.val (hel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)) hel.2

end CFSG.StandardType.LieKnownR2.ExcPos
