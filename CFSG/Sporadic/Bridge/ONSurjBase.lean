
module

public import CFSG.Sporadic.ON.SimpleBase
public import CFSG.Sporadic.Bridge.Common
public import CFSG.Sporadic.Presentation.ONan
public import Certificates.Data.CFSGNative.Bridge.ONGPL
public meta import Certificates.Data.CFSGNative.Bridge.ONGPL
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Sporadic.Presentation.ONanInputs
public import Certificates.Data.CFSGNative.ON.Certificate
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Perm.ChainComplete
public import CFSG.Sporadic.HS.Chain
public import CFSG.Sporadic.ON.ActionBase
public import CFSG.Sporadic.ON.CertificateBase
public import CFSG.Sporadic.ON.ChainBase
public import CFSG.Sporadic.ON.LinesBase
public import CFSG.Sporadic.ON.PrimitiveBase
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.Sporadic.Bridge.ON

open CFSG.Sporadic.ON CFSG.Sporadic.ON.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Perm.Native CFSG.Sporadic.Bridge.ONGPL.Native TauCeti

noncomputable abbrev imgT : Array Table := imgWords.map (wordT nPts (genT orb))

noncomputable abbrev imgTv : Array Table := imgT.map (invT nPts)

structure BridgeFacts : Prop where
  sizeImg : imgWords.size = 7
  sizeSurj : surjWords.size = 2
  letters : ∀ w ∈ surjWords, ∀ z ∈ w, z ≠ 0 ∧ z.natAbs ≤ 7
  inv : ∀ k < 7, invOK nPts imgT[k]! imgTv[k]! = true
  rels : ∀ r ∈ rels,
    tupleEq (apT (wordT nPts (imgLetter imgT imgTv) (r.map letterOf)) chainQ) chainQ = true
  surjA : tupleEq (apT (wordT nPts (imgLetter imgT imgTv) surjWords[0]!) chainQ)
    (apT orb.alpha chainQ) = true
  surjB : tupleEq (apT (wordT nPts (imgLetter imgT imgTv) surjWords[1]!) chainQ)
    (apT orb.beta chainQ) = true

theorem seedLetter_four (A IA B IB : Table) : seedLetter #[A, IA, B, IB] =
    fun z => if z = 1 then A else if z = -1 then IA else if z = 2 then B else IB :=
  rfl

theorem seedLetter_eq :
    seedLetter #[orb.alpha, invT nPts orb.alpha, orb.beta, invT nPts orb.beta] = genT orb := by
  rw [seedLetter_four]
  funext z
  rfl

theorem letterOf_natAbs (l : ℕ × Bool) : (letterOf l).natAbs = l.1 + 1 := by
  unfold letterOf; split <;> omega

private theorem presentation_eq : SporadicName.ONan.presentation = Sporadic.onanPresentation :=
  rfl

theorem relatorLetters_eq : Sporadic.onanPresentation.relatorLetters = rels := by
  rw [Sporadic.onanPresentation_relatorLetters]
  rfl

theorem generatorCount_eq : Sporadic.onanPresentation.generatorCount = 7 := by
  simp [GroupPresentation.generatorCount]

@[expose] noncomputable def presLetter (z : ℤ) : Sporadic.onanPresentation.Group :=
  if 0 < z then presGen Sporadic.onanPresentation (z - 1).toNat
  else (presGen Sporadic.onanPresentation (-z - 1).toNat)⁻¹

end CFSG.Sporadic.Bridge.ON
