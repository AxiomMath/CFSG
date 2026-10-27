module

public import Certificates.Kernel.LocalQT.Tc.Gen
public import Certificates.Kernel.SporSch.Ru.Gens
public import Certificates.Data.Kernel.B45Perm.TGen
public import Certificates.Data.Kernel.LocalQT.SylV
public import Certificates.Data.Kernel.SporSch.IntLines
public import Certificates.Data.SmithB45ExcRuData
public import CFSG.Certificates.Kernel.Common.StrChars
meta import Certificates.Data.SmithB45ExcRuData

namespace CFSG.KD.B45.C260393

open CFSG.Quasithin.B45Exc.Ru CFSG.Quasithin.B45Exc.Tab CFSG.QuasithinUnique.Setup.X1

meta def sgM : List (Array Nat × Array Nat) := ruTGens

meta def parM : List Nat := parseNats ruTParStr

meta def labM : List Nat := parseNats ruTLabStr

meta def tabM : List Nat := parseNats ruTTabStr

end CFSG.KD.B45.C260393

public section

set_option maxRecDepth 400000

#ks_chars_of CFSG.KD.B45.C260393.C0 (CFSG.Quasithin.B45Exc.Ru.ruTWordStrs.getD 0 "")
#ks_chars_of CFSG.KD.B45.C260393.C1 (CFSG.Quasithin.B45Exc.Ru.ruTWordStrs.getD 1 "")
#ks_chars_of CFSG.KD.B45.C260393.C2 (CFSG.Quasithin.B45Exc.Ru.ruTWordStrs.getD 2 "")
#ks_chars_of CFSG.KD.B45.C260393.C3 (CFSG.Quasithin.B45Exc.Ru.ruTWordStrs.getD 3 "")
#ks_chars_of CFSG.KD.B45.C260393.C4 (CFSG.Quasithin.B45Exc.Ru.ruTWordStrs.getD 4 "")
#ks_chars_of CFSG.KD.B45.C260393.C5 (CFSG.Quasithin.B45Exc.Ru.ruTWordStrs.getD 5 "")
#ks_chars_of CFSG.KD.B45.C260393.C6 (CFSG.Quasithin.B45Exc.Ru.ruTWordStrs.getD 6 "")

#ks_chars CFSG.KD.B45.C260393.CP CFSG.Quasithin.B45Exc.Ru.ruTParStr
#ks_chars CFSG.KD.B45.C260393.CL CFSG.Quasithin.B45Exc.Ru.ruTLabStr
#ks_chars CFSG.KD.B45.C260393.CT CFSG.Quasithin.B45Exc.Ru.ruTTabStr

#kqb_syl CFSG.KD.B45.C260393.SY 4060 12 256 CFSG.KD.B45.C260393.sgM CFSG.KD.B45.C260393.parM
  CFSG.KD.B45.C260393.labM CFSG.KD.B45.C260393.tabM

namespace CFSG.KD.B45.C260393

open CFSG.KC.Enum CFSG.KC.IntLines CFSG.KC.B45P CFSG.KC.LQT.SV CertificateChecks.KernelSporSch.RuG

@[expose] noncomputable def wsK : List (List Int) :=
  [lineInts C0.chars, lineInts C1.chars, lineInts C2.chars, lineInts C3.chars, lineInts C4.chars,
   lineInts C5.chars, lineInts C6.chars]

@[expose] noncomputable def ckW (s : Nat) : Bool :=
  tGenK 4060 12 [A0, A1] [A0I, A1I] A0 A0I (SY.G.getD s 0) (wsK.getD s [])

@[expose] noncomputable def ckSY (s : Nat) : Bool :=
  chunkSV 4060 12 256 7 SY.G SY.E SY.PT SY.LT SY.TB (Nat.mul s 8) 8

end CFSG.KD.B45.C260393

end
