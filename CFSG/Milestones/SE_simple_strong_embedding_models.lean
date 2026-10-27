module

public import CFSG.StronglyEmbedded

public section

universe u v w

namespace CFSG.BenderSuzuki

open Matrix in
theorem _root_.CFSG.Milestones.bender_suzuki {X : Type*} [Group X] [Finite X] [IsSimpleGroup X]
    (M : Subgroup X) (h : CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M) :
    CFSG.BenderSuzuki.IsBenderGroup X :=
  _root_.CFSG.BenderSuzuki.bender_suzuki M h

end CFSG.BenderSuzuki
