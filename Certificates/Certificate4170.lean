
module


public import Certificates.Kernel.A312M23.Final

public section

open scoped Pointwise

public section

namespace Certificates

open scoped Pointwise in
open CFSG.Quasithin.A312Words in
open CFSG.Quasithin.A312M23 CFSG.Quasithin.H.MathieuLat in
theorem certificate4170 :
    M22Facts (Set (Fin 23)) (m23Member 1) ∧ L34Facts (m23Member 2) ∧
      E2Facts (Set (Fin 23)) (m23Member 3) 4 6 360 false false ∧
      E2Facts (Set (Fin 23)) (m23Member 4) 4 7 168 false true ∧
      E2Facts (Set (Fin 23)) (m23Member 5) 4 7 2520 false false ∧
      E2Facts (Set (Fin 23)) (m23Member 6) 3 7 168 true true ∧
      E2Facts (Set (Fin 23)) (m23Member 7) 4 5 60 true false ∧
      E2Facts (Set (Fin 23)) (m23Member 9) 4 5 60 true false ∧
      TriFacts (Set (Fin 23)) (m23Member 8) :=
  CFSG.KD.A312M23.m23_4170

end Certificates
