module

public import CFSG.Monster.B.Dyadic.DefsN
public import CFSG.Monster.B.Dyadic.Reduce
public import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data3

public section

namespace CFSG.Monster.B.Dyadic

@[expose] noncomputable def F0row (j t : Fin 4370) : ZMod 2 :=
  if (CFSG.KC.BM.Lat.recOf CFSG.KC.BM.NativePair.F0.rows j).testBit t then 1 else 0

@[expose] def FactA0 : Prop :=
  (MqN (numerAt 28) * MqN (numerAt 1) * MqN (numerAt 2) * MqN (numerAt 4) * MqN (numerAt 5) *
      MqN (numerAt 10) * MqN (numerAt 17) = Mq26) ∧
    ∀ j : Fin 4370, ∃ c : Fin 4371 → ℤ,
      (∀ u : Fin 4371,
        ∑ t : Fin 4371, Bz (pIdx.succAbove j) t * numer26 t u = 8 * ∑ t : Fin 4371, c t * Bz t u) ∧
      ∀ t : Fin 4370,
        (c (pIdx.succAbove t) : ZMod 2) + (c pIdx : ZMod 2) * fvec (pIdx.succAbove t) = F0row j t

end CFSG.Monster.B.Dyadic

end
