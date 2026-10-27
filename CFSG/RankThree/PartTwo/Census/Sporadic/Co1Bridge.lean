module

public import CFSG.Sporadic.Co1
public import CFSG.Sporadic.Bridge.VecSurj
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.SimpleTrick
public import Certificates.Data.CFSGNative.Bridge.SurjD
public meta import Certificates.Data.CFSGNative.Bridge.SurjD
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate8154
public import Certificates.Certificate3024
public import CFSG.Open.Defs
public import CFSG.Sporadic.Co1Base
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.Bridge.SurjD.Native TauCeti

theorem co1_bridge_check : co1Check () = true :=
  Certificates.certificate8154

theorem nonempty_mulEquiv_Co1_of_eq
    (P : GroupPresentation) (hP : P = Sporadic.co1Presentation)
    [IsSimpleGroup P.Group] : Nonempty (P.Group ≃* Blueprint.NativeSporadic.Co1) := by
  subst hP
  let e : Blueprint.NativeSporadic.Co1 ≃* J CFSG.Sporadic.Co1.Native.co1Data :=
    seedEquiv CFSG.Sporadic.Co1.co1Facts.toBaseFacts
  have : Nontrivial (J CFSG.Sporadic.Co1.Native.co1Data) :=
    QuasithinUnique.SQTK.nontrivial_of_two_le_natCard (k := 4157776806543360000) (by norm_num)
      (le_of_eq (by rw [← Nat.card_congr e.toEquiv, CFSG.Sporadic.Co1.card_Co1]))
  obtain ⟨φ, hφ⟩ := CFSG.Sporadic.Bridge.VecSurj.exists_surjective CFSG.Sporadic.Co1.co1Facts
    (CFSG.Perm.pairG (gs CFSG.Sporadic.Co1.Native.co1Data))
    (CFSG.Sporadic.Bridge.VecSurj.rep_chainLetters CFSG.Sporadic.Co1.co1Facts)
    (show Sporadic.co1Presentation.generatorCount = co1Spec.m by
      simp [GroupPresentation.generatorCount, co1Spec])
    (show Sporadic.co1Presentation.relatorLetters = co1Spec.rels by
      rw [Sporadic.co1Presentation_relatorLetters]; rfl)
    co1_bridge_check
  exact ⟨(QuasithinUnique.SQTK.mulEquivOfSurjective φ hφ).trans e.symm⟩

theorem nonempty_mulEquiv_Co1
    [IsSimpleGroup SporadicName.Co1.Group] :
    Nonempty (SporadicName.Co1.Group ≃* Blueprint.NativeSporadic.Co1) :=
  nonempty_mulEquiv_Co1_of_eq SporadicName.Co1.presentation rfl

end CFSG.RankThree.PartTwo.Census
