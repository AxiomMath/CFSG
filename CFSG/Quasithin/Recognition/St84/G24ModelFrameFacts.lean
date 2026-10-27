module

public import CFSG.Quasithin.Recognition.St84.G24Model
public import CFSG.Quasithin.Vol2.KGFactC31EBasis
public import Certificates.Data.G24ModelFrameData

public section

noncomputable section

namespace CFSG.Quasithin.F112R.St84.G24M

open CFSG.Quasithin.KGC31 (eElt)


@[expose] def frame1 (i : Fin 8) : Y := pc1Y (Fin.castAdd 2 i)

@[expose] def zb1 (t : Fin 2) : Y := pc1Y (Fin.natAdd 8 t)

@[expose] def frame2 (i : Fin 6) : Y := pc2Y (Fin.castAdd 4 i)

@[expose] def zb2 (t : Fin 4) : Y := pc2Y (Fin.natAdd 6 t)

structure FrameFacts : Prop where
  act1 : ∀ (g : Fin 3) (j : Fin 8), ∃ c : Fin 2 → ZMod 2,
    A1img g * frame1 j * (A1img g)⁻¹ =
      eElt frame1 (fun i => CFSG.Quasithin.St84.G24MF.matV1 g i j) * eElt zb1 c
  actZ1 : ∀ (g : Fin 3) (t : Fin 2),
    A1img g * zb1 t * (A1img g)⁻¹ = eElt zb1 (fun s => CFSG.Quasithin.St84.G24MF.matZ1 g s t)
  act2 : ∀ (g : Fin 3) (j : Fin 6), ∃ c : Fin 4 → ZMod 2,
    A2img g * frame2 j * (A2img g)⁻¹ =
      eElt frame2 (fun i => CFSG.Quasithin.St84.G24MF.matV2 g i j) * eElt zb2 c
  actZ2 : ∀ (g : Fin 3) (t : Fin 4),
    A2img g * zb2 t * (A2img g)⁻¹ = eElt zb2 (fun s => CFSG.Quasithin.St84.G24MF.matZ2 g s t)

end CFSG.Quasithin.F112R.St84.G24M
