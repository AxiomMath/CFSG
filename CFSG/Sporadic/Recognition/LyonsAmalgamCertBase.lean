
module

public import Certificates.Certificate6111
public import Certificates.Certificate6112

@[expose] public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm Subgroup

theorem yOK_of_certificate : Ly1080.YOK :=
  Certificates.certificate6111

theorem trCheck_eq_true : Ly243.trCheck = true := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -⟩ := Certificates.certificate6112
  simp only [Ly243.trCheck, h1, h2, h3, h4, h5, h6, h7, h8, h9, Bool.and_self]

theorem tauOK_eq_true : Tau.tauOK = true :=
  (Certificates.certificate6112).2.2.2.2.2.2.2.2.2

end CFSG.Sporadic.Recognition.LyonsSims
