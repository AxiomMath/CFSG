module

public import Certificates.Data.Kernel.PermCent.U43QuatEls

public section

namespace CFSG.ComponentClassification.HarrisLit.P1.U43.Quat

@[expose] def cS01 : ℕ := 7625740974300

@[expose] def cY0 : ℕ := 1189732679211162

@[expose] def qc (j : ℕ) : ℕ := (quatEls.getD j (0, false)).1

end CFSG.ComponentClassification.HarrisLit.P1.U43.Quat

end
