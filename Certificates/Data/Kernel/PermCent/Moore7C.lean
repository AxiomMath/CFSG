module

public import Certificates.Data.Kernel.PermCent.AllPermsC
public import CFSG.GH74.GLS.C3.Prop121.MooreFinite7Inputs

public section

namespace CFSG.Certificates.Kernel.PkCV

@[expose] noncomputable def m7CB (E2 : List (CV 8)) (s1 s2 s3 s4 : CV 8) : Bool :=
  E2.all fun s5 => !powOneC (s4 * s5) 3 || !powOneC (s2 * s5) 2 || !powOneC (s3 * s5) 2 ||
    powOneC (s1 * s2) 3

@[expose] noncomputable def m7BB (E1 E2 : List (CV 8)) (s1 : CV 8) : Bool :=
  E1.all fun s2 => E2.all fun s3 =>
    !powOneC (s2 * s3) 3 || Nat.beq s2.1 s3.1 || E2.all fun s4 =>
      !powOneC (s3 * s4) 3 || !powOneC (s2 * s4) 2 || Nat.beq s2.1 s4.1 || m7CB E2 s1 s2 s3 s4

@[expose] noncomputable def m7AllB (A O E : List (CV 8)) : Bool :=
  A.all fun s1 => O.all fun sg => !eq22C sg s1 s1 sg ||
    forceCL (E.filter fun s => eq22C sg s s sg) fun E1 =>
      forceCL (E1.filter fun s => eq22C s s1 s1 s) fun E2 => m7BB E1 E2 s1

@[expose] noncomputable def m7Inv (L : List (CV 8 × Bool)) : List (CV 8 × Bool) :=
  L.filter fun x => powOneC x.1 2

@[expose] noncomputable def m7E (J : List (CV 8 × Bool)) (c ci : CV 8) : List (CV 8) :=
  (J.filter fun x => !x.2 && eq22C x.1 c ci x.1).map Prod.fst

@[expose] noncomputable def m7A (J : List (CV 8 × Bool)) (c : CV 8) : List (CV 8) :=
  (J.filter fun x => !x.2 && !powOneC x.1 1 && powOneC (c * x.1) 3).map Prod.fst

@[expose] noncomputable def m7O (J : List (CV 8 × Bool)) (c ci : CV 8) : List (CV 8) :=
  (J.filter fun x => x.2 && eq22C x.1 c ci x.1).map Prod.fst

@[expose] noncomputable def m7F : Bool :=
  forceC (cOf CFSG.GH74.GLS.C3.Prop121.cEnd7) fun c => forceC c⁻¹ fun ci =>
    forcePL (m7Inv (allPermsP 8 inferInstance)) fun J =>
      forceCL (m7E J c ci) fun E => forceCL (m7A J c) fun A => forceCL (m7O J c ci) fun O =>
        m7AllB A O E

end CFSG.Certificates.Kernel.PkCV

end
