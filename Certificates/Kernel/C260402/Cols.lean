module

public import Certificates.Data.Kernel.B45M22.Defs
public import Certificates.Data.SmithB45MatM22Mod
public import Certificates.Kernel.C260402.Pins

public section

namespace CFSG.KD.C260402

open CFSG.KC.B45M22 CFSG.Quasithin.B45Mat.M22 CFSG.Quasithin.H.Mathieu CFSG.Sporadic.Mathieu

theorem cols10aA : colsK 10 (act10 (psiArr (m22a : Equiv.Perm (Fin 22)))) C10aA = true := by
  decide +kernel

theorem cols10aB : colsK 10 (act10 (psiArr (m22b : Equiv.Perm (Fin 22)))) C10aB = true := by
  decide +kernel

theorem cols10aG7 : colsK 10 (act10 (psiArr (g7 : Equiv.Perm (Fin 22)))) C10aG7 = true := by
  decide +kernel

theorem cols10bA : colsK 10 (actC10 (psiArr (m22a : Equiv.Perm (Fin 22)))) C10bA = true := by
  decide +kernel

theorem cols10bB : colsK 10 (actC10 (psiArr (m22b : Equiv.Perm (Fin 22)))) C10bB = true := by
  decide +kernel

theorem cols10bG7 : colsK 10 (actC10 (psiArr (g7 : Equiv.Perm (Fin 22)))) C10bG7 = true := by
  decide +kernel

theorem cols10bG11 : colsK 10 (actC10 (psiArr (g11 : Equiv.Perm (Fin 22)))) C10bG11 = true := by
  decide +kernel

end CFSG.KD.C260402

end
