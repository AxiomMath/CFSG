module

public import Certificates.Data.SmithD6RhoCheck

public noncomputable section

namespace CFSG.SmithD6

@[expose] def chkKcMeet : Bool :=
  (List.range 75735).all fun j => j == 0 || decide (meetCnt 0 j ≤ 16)

opaque chkKcThroughSeal : {x : Bool // x = (((List.range 75735).filter fun i =>
    memR pbArr[i]! ppArr[i]! 64 && memR pbArr[i]! ppArr[i]! 128).length == 135)} :=
  ⟨((List.range 75735).filter fun i =>
    memR pbArr[i]! ppArr[i]! 64 && memR pbArr[i]! ppArr[i]! 128).length == 135, rfl⟩

@[expose] def chkKcThrough : Bool := chkKcThroughSeal.1

theorem chkKcThrough_def : chkKcThrough = (((List.range 75735).filter fun i =>
    memR pbArr[i]! ppArr[i]! 64 && memR pbArr[i]! ppArr[i]! 128).length == 135) :=
  chkKcThroughSeal.2

attribute [irreducible] chkKcThrough

end CFSG.SmithD6
