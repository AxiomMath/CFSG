module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.B3FaithfulPart2
public import CFSG.LieType.Chevalley.NativeHolds

@[expose] public section

public section

namespace CFSG.StandardType.F4ExplicitPos.B3Unconditional

open CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag

noncomputable def f4_exceptionalEndo
    (K : Type) [Field K] [Finite K] [CharP K 2] :
    adjointGroup ReeTag.F4.tag K →* adjointGroup ReeTag.F4.tag K :=
  CFSG.StandardType.F4ExplicitPos.B3Exact.Narrow.exceptionalEndoNarrow (t := ReeTag.F4) K
    (CFSG.StandardType.F4ExplicitPos.B3Exact.Narrow.F4_prime_cast_eq_zero K)
    (CFSG.StandardType.F4ExplicitPos.B3Faithful.f4_shortFaithful K)

theorem f4_exceptionalEndo_bijective
    (K : Type) [Field K] [Finite K] [CharP K 2] :
    Function.Bijective (f4_exceptionalEndo K) :=
  CFSG.StandardType.F4ExplicitPos.B3Exact.Narrow.exceptionalEndoNarrow_F4_bijective
    (CFSG.StandardType.F4ExplicitPos.B3Faithful.f4_shortFaithful K)

noncomputable def f4_exceptionalAut
    (K : Type) [Field K] [Finite K] [CharP K 2] :
    MulEquiv (adjointGroup ReeTag.F4.tag K) (adjointGroup ReeTag.F4.tag K) :=
  MulEquiv.ofBijective (f4_exceptionalEndo K) (f4_exceptionalEndo_bijective K)

@[simp] theorem f4_exceptionalAut_apply
    (K : Type) [Field K] [Finite K] [CharP K 2]
    (g : adjointGroup ReeTag.F4.tag K) :
    f4_exceptionalAut K g = f4_exceptionalEndo K g :=
  rfl

end CFSG.StandardType.F4ExplicitPos.B3Unconditional

namespace CFSG.StandardType.F4ExplicitPos.B3Pinned

open CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.StandardType.F4ExplicitPos.B3Unconditional

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem f4_exceptionalEndo_xElement
    (i : Fin F4.tag.rank) (c : K) :
    f4_exceptionalEndo K (xElement i c) = xElement (F4.perm i) (c ^ F4.exponent i) :=
  CFSG.StandardType.F4ExplicitPos.B3Exact.Narrow.exceptionalEndoNarrow_xElement
    (CFSG.StandardType.F4ExplicitPos.B3Exact.Narrow.F4_prime_cast_eq_zero K)
    (CFSG.StandardType.F4ExplicitPos.B3Faithful.f4_shortFaithful K) i c

theorem f4_exceptionalEndo_yElement
    (i : Fin F4.tag.rank) (c : K) :
    f4_exceptionalEndo K (yElement i c) = yElement (F4.perm i) (c ^ F4.exponent i) :=
  CFSG.StandardType.F4ExplicitPos.B3Exact.Narrow.exceptionalEndoNarrow_yElement
    (CFSG.StandardType.F4ExplicitPos.B3Exact.Narrow.F4_prime_cast_eq_zero K)
    (CFSG.StandardType.F4ExplicitPos.B3Faithful.f4_shortFaithful K) i c

end CFSG.StandardType.F4ExplicitPos.B3Pinned

end

end
