module

public import Certificates.Data.Kernel.B45J2.Defs
public import Certificates.Data.SmithB45J2Mod

public section

namespace CFSG.KD.C260411

open CFSG.KC.B45M12 CFSG.KC.B45J2 CFSG.Quasithin.J2Mod

@[expose] noncomputable def A6 : List (ℕ × ℕ) := colsF4 6 tA6Rows

@[expose] noncomputable def B6 : List (ℕ × ℕ) := colsF4 6 tB6Rows

@[expose] noncomputable def B14c : List (ℕ × ℕ) := colsL 36 14 B14Limbs

@[expose] noncomputable def P14c : List (ℕ × ℕ) := colsL 14 36 P14Limbs

@[expose] noncomputable def B64c : List (ℕ × ℕ) := colsL 84 64 B64Limbs

@[expose] noncomputable def P64c : List (ℕ × ℕ) := colsL 64 84 P64Limbs

@[expose] noncomputable def B160c : List (ℕ × ℕ) := colsL 196 160 B160Limbs

@[expose] noncomputable def P160c : List (ℕ × ℕ) := colsL 160 196 P160Limbs

end CFSG.KD.C260411

end
