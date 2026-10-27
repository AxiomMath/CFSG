
module


public import Certificates.Certificate7229

public section

namespace CFSG.Quasithin.KGC31.Ru

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.RuSchreier CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative
  CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Native

section Reps

end Reps

section Cover

theorem exists_conj_repZ {x : Equiv.Perm (Fin 4060)} (hx : x ∈ ruC) (hx2 : x ^ 2 = 1)
    (hx1 : x ≠ 1) (hxz : x ≠ ruZ) : ∃ r ∈ repsZG, ∃ c ∈ ruC, c * x * c⁻¹ = r :=
  Certificates.certificate7229.1 x hx hx2 hx1 hxz

theorem ncard_fixSet_otherZ : ∀ w ∈ otherZW, (fixSet (wG w)).ncard = 0 :=
  Certificates.certificate7229.2.2.1

theorem exists_conj_repA {x : Equiv.Perm (Fin 4060)} (hx : x ∈ ruL) (hx2 : x ^ 2 = 1)
    (hx1 : x ≠ 1) (hxa : x ≠ ruA0) : ∃ r ∈ repsAG, ∃ c ∈ ruL, c * x * c⁻¹ = r :=
  Certificates.certificate7229.2.1 x hx hx2 hx1 hxa

theorem ncard_fixSet_otherA : ∀ w ∈ otherAW, (fixSet (abG w)).ncard = 92 :=
  Certificates.certificate7229.2.2.2

end Cover

end CFSG.Quasithin.KGC31.Ru

end
