module

public import Certificates.Certificate2290

public section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.PSL3Four.Native
  CFSG.ComponentClassification.PSL3Four

theorem cti_fix0 : (fixList 0).length = 42 :=
  Certificates.certificate2290.1

theorem cti_fix1 : (fixList 1).length = 54 :=
  Certificates.certificate2290.2.1


theorem enumerates_rho0Of (h0 : (fixList 0).length = 42) :
    Enumerates (rho0Of h0).range (enumOf 42 (kGens 0) 40320).tabs.toList :=
  (Certificates.certificate2290.2.2 h0 cti_fix1).1.1

theorem card_range_rho0Of (h0 : (fixList 0).length = 42) : Nat.card (rho0Of h0).range = 40320 :=
  (Certificates.certificate2290.2.2 h0 cti_fix1).1.2.1

theorem card_suzDOf (h0 : (fixList 0).length = 42) : Nat.card (suzDOf h0) = 20160 :=
  (Certificates.certificate2290.2.2 h0 cti_fix1).1.2.2.1

theorem conj_mem_suzDOf (h0 : (fixList 0).length = 42) {k : ℕ} (hk : k < 22)
    {x : Equiv.Perm (Fin 42)} (hx : x ∈ suzDOf h0) :
    kpermOf h0 k * x * (kpermOf h0 k)⁻¹ ∈ suzDOf h0 ∧
      (kpermOf h0 k)⁻¹ * x * kpermOf h0 k ∈ suzDOf h0 :=
  (Certificates.certificate2290.2.2 h0 cti_fix1).1.2.2.2.1 k hk x hx

theorem classFunOf_injective (h0 : (fixList 0).length = 42) :
    Function.Injective (classFunOf h0) :=
  (Certificates.certificate2290.2.2 h0 cti_fix1).1.2.2.2.2.1

theorem classFunOf_surjective (h0 : (fixList 0).length = 42) :
    Function.Surjective (classFunOf h0) :=
  (Certificates.certificate2290.2.2 h0 cti_fix1).1.2.2.2.2.2.1

theorem card_classFunOf (h0 : (fixList 0).length = 42) (l : Fin 10) :
    Nat.card (classFunOf h0 l).carrier = classSizes.getD l 0 :=
  (Certificates.certificate2290.2.2 h0 cti_fix1).1.2.2.2.2.2.2.1 l

theorem enumerates_suzDOf (h0 : (fixList 0).length = 42) :
    Enumerates (suzDOf h0) (enumOf 42 dGens 20160).tabs.toList :=
  (Certificates.certificate2290.2.2 h0 cti_fix1).1.2.2.2.2.2.2.2

theorem card_range_rho1Of (h1 : (fixList 1).length = 54) :
    Nat.card (rho1Of h1).range = 1658880 :=
  (Certificates.certificate2290.2.2 cti_fix0 h1).2.1

theorem card_suzQbarOf (h1 : (fixList 1).length = 54) : Nat.card (suzQbarOf h1) = 64 :=
  (Certificates.certificate2290.2.2 cti_fix0 h1).2.2.1

theorem conj_mem_suzQbarOf (h1 : (fixList 1).length = 54) {k : ℕ} (hk : k < 10)
    {x : Equiv.Perm (Fin 54)} (hx : x ∈ suzQbarOf h1) :
    kperm1Of h1 k * x * (kperm1Of h1 k)⁻¹ ∈ suzQbarOf h1 :=
  (Certificates.certificate2290.2.2 cti_fix0 h1).2.2.2.1 k hk x hx

theorem qpermOf_comm (h1 : (fixList 1).length = 54) {i j : ℕ} (hi : i < 6) (hj : j < 6) :
    qpermOf h1 i * qpermOf h1 j = qpermOf h1 j * qpermOf h1 i :=
  (Certificates.certificate2290.2.2 cti_fix0 h1).2.2.2.2.1 i hi j hj

theorem mem_suzQbarOf_of_comm (h1 : (fixList 1).length = 54) {y : Equiv.Perm (Fin 54)}
    (hy : y ∈ (rho1Of h1).range) (hc : ∀ j < 6, y * qpermOf h1 j = qpermOf h1 j * y) :
    y ∈ suzQbarOf h1 :=
  (Certificates.certificate2290.2.2 cti_fix0 h1).2.2.2.2.2 y hy hc

end CFSG.Sporadic.SuzOddCore
