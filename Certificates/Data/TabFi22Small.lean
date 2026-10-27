module

public import Certificates.Data.Fi22Pump
public meta import Certificates.Data.Fi22Pump

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabFi22Small

open CFSG.RankThree.Native CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.Certificates.Native CFSG.HardMathSupport.Solomon.Coordinator.Fi22Pump

set_option compiler.extract_closed false

@[expose] def hex : String := include_str "TabFi22Small.txt"

@[expose] def uArr (k : ℕ) : Array ℕ := hexTable3 3510 (3510 * k) hex

@[expose] def uCheckAt (L : Array Level) (k q f : ℕ) : Bool :=
  validA 3510 (uArr k) && siftA 3510 L fi22BaseArr 0 (uArr k) &&
    eqA 3510 (powA 3510 (uArr k) q) (idA 3510) && !(eqA 3510 (uArr k) (idA 3510)) &&
    fi22FixCount (uArr k) == f

@[expose] def tabFi22SmallCheck (_ : Unit := ()) : Bool :=
  let L := rawLevels 3510 fi22StrongArrs fi22BaseArr
  uCheckAt L 0 7 3 && uCheckAt L 1 11 1 && uCheckAt L 2 13 0

end CFSG.HardMathSupport.Dickson.I271.TabFi22Small
