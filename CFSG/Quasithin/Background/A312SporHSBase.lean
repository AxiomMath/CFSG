
module

public import CFSG.Quasithin.Background.A312SporShapes
public import CFSG.Quasithin.Background.A312SporHSInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHSBase
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFamilies
public import CFSG.Quasithin.Background.A312SporHSKInputs
import Certificates.Kernel.HSA312.Y1
import Certificates.Kernel.HSA312.Y2
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHSBase

public section

namespace CFSG.Quasithin.A312S

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.QuasithinUnique.Ch1.SporLat.HS
open CFSG.Sporadic.SmallF2 CFSG.Quasithin.A312S.HS
open CFSG.Sporadic.HS.Native (hsData)
open Matrix

section HS

theorem hsMat_det (l : ℕ) : (hsMat l).det = 1 := by
  rcases l with _ | _ | _ | _ | l
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Matrix.det_one

@[expose] def hsSL (l : ℕ) : SpecialLinearGroup (Fin 3) (ZMod 2) := ⟨hsMat l, hsMat_det l⟩

end HS

end CFSG.Quasithin.A312S
