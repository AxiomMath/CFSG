module

public import Certificates.Data.E6ThreeTwD4T2Gen
public meta import Certificates.Data.E6ThreeTwD4T2Gen
public meta import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeCharData
public meta import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeChar
public meta import CFSG.Blueprint.ChevalleyRootsInputs
public meta import CFSG.Blueprint.Chevalley

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.CrossChar

@[expose] def twD4T2PosOK (c : Fin Tag.E6.rank → ZMod 3) (sig : List ℕ) (t : List ℕ) : Bool :=
  sig.all fun p =>
    !(decide (triPairing c (e6Certificate.root p) = 0) &&
        decide (0 < height (e6Certificate.root p))) ||
      decide (0 < height (e6Certificate.tupleVec t (e6Certificate.root p)))

@[expose] def twD4T2StabCheck (_ : Unit := ()) : Bool :=
  let sig := twD4T2Sig ()
  (List.range (3 ^ Tag.E6.rank)).all fun k =>
    let c := vec3OfIndex (τ := .E6) k
    twD4T2Elems.all fun e =>
      let t := decodeT Tag.E6.rank e.1
      !(twD4T2Fixes c t && twD4T2PosOK c sig t) || t == List.range Tag.E6.rank

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
