module

public import CFSG.Quasithin.Background.A312SporHSInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHSDcInputs
public import Certificates.Data.Kernel.HSA312.Data

public noncomputable section

namespace CFSG.Quasithin.A312S.HS

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.HS
open CFSG.Sporadic.HS.Native (hsData)

@[expose] def hsL1K : List (Array Nat) := hsLatK.sTabs ++ hsLatK.mt[1]!

@[expose] def hsZ4K : Array Nat := wordTabA hsL1K.toArray hsData.n hsZ4Word

@[expose] def hsEK : List (Array Nat) := hsEWords.map (wordTabA hsL1K.toArray hsData.n)

@[expose] def hsEEnumK : Array (List Nat) × Array Nat × Array Nat :=
  (CFSG.KD.HSA312.J.ETs, CFSG.KD.HSA312.J.Epar, CFSG.KD.HSA312.J.Ecl)

@[expose] def hsV1EnumK : Array (List Nat) × Array Nat × Array Nat :=
  (CFSG.KD.HSA312.J.VTs, CFSG.KD.HSA312.J.Vpar, CFSG.KD.HSA312.J.Vcl)

@[expose] def A312HS1K : Prop :=
  hsL1K.length = 4 ∧ GensIn ptAct hsDelta hsLatK 4 1 ∧
    ((hsZ4K :: hsEK).all fun t => CFSG.Quasithin.A312S.fixLabs t hsLatK.Om[1]!.lbl.toList) = true ∧
    CFSG.Quasithin.A312S.Z4StarOK hsData.n hsB hsZ4K hsEK hsEEnumK.1 hsEEnumK.2.1 hsEEnumK.2.2
      hsV1EnumK.1 hsV1EnumK.2.1 hsV1EnumK.2.2

@[expose] def hsL2K : List (Array Nat) := hsLatK.sTabs ++ hsLatK.mt[2]!

@[expose] def hsWK : List (Array Nat) := hsWWords.map (wordTabA hsL2K.toArray hsData.n)

@[expose] def hsWEnumK : Array (List Nat) × Array Nat × Array Nat :=
  (CFSG.KD.HSA312.J.WTs, CFSG.KD.HSA312.J.Wpar, CFSG.KD.HSA312.J.Wcl)

@[expose] def hsVTabsK : Array (Array Nat) :=
  (hsVWords.map (wordTabA hsL2K.toArray hsData.n)).toArray

@[expose] def hsKerEnumK : Array (List Nat) × Array Nat × Array Nat :=
  (CFSG.KD.HSA312.J.KTs, CFSG.KD.HSA312.J.Kpar, CFSG.KD.HSA312.J.Kcl)

@[expose] def A312HS2K : Prop :=
  hsL2K.length = 4 ∧ CFSG.Quasithin.A312S.e8Check hsData.n hsVTabsK hsL2K.toArray hsVMats = true ∧
    CFSG.Quasithin.A312S.KerOK hsData.n hsB hsL2K hsQuot2 hsKer hsVTabsK hsKerEnumK.1
      hsKerEnumK.2.1 hsKerEnumK.2.2 64 ∧
    (hsWK.all fun t => CFSG.Quasithin.A312S.fixLabs t hsLatK.Om[2]!.lbl.toList) = true ∧
    CFSG.Quasithin.A312S.Z4CubedOK hsData.n hsB hsWK hsWEnumK.1 hsWEnumK.2.1 hsWEnumK.2.2

end CFSG.Quasithin.A312S.HS
