module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRows
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicMathieuInputs
public import CFSG.Quasithin.Background.HSporLatInputs
public import Certificates.Data.CFSGNative.SporLat.Build
public import Certificates.Data.CFSGNative.SporLat.Code
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatQuot

public section

namespace CFSG.Quasithin.H13.KGSporLat

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat

@[expose] def m11Sets : List (List ℕ) :=
  [[0, 1], [1, 2], [1, 3], [1, 4], [1, 6], [1, 7], [1, 9], [1, 10]]

@[expose] def m11Delta : List ℕ := sortN (m11Sets.map (encodeSet 11))

@[expose] def m11STabs : List (Array ℕ) := m11Qp.map fun p => m11SLP[p.1]!

@[expose] def m11Mems : List Mem := [⟨16, 16, 16⟩, ⟨720, 1, 720⟩, ⟨144, 1, 144⟩, ⟨48, 8, 48⟩]

@[expose] def m12Mems : List Mem := [⟨64, 64, 64⟩, ⟨192, 32, 192⟩, ⟨192, 32, 192⟩]

@[expose] def m22Mems : List Mem :=
  [⟨128, 128, 128⟩, ⟨5760, 16, 5760⟩, ⟨384, 64, 384⟩, ⟨1920, 16, 1920⟩, ⟨384, 64, 384⟩]

@[expose] def m23Mems : List Mem :=
  [⟨128, 128, 128⟩, ⟨443520, 1, 443520⟩, ⟨40320, 1, 40320⟩, ⟨5760, 16, 5760⟩,
    ⟨2688, 16, 2688⟩, ⟨40320, 16, 40320⟩, ⟨2688, 16, 2688⟩, ⟨1920, 16, 1920⟩,
    ⟨5760, 16, 5760⟩, ⟨1920, 16, 1920⟩, ⟨384, 64, 384⟩, ⟨384, 64, 384⟩, ⟨384, 64, 384⟩,
    ⟨384, 64, 384⟩, ⟨384, 64, 384⟩, ⟨1152, 64, 1152⟩]

end CFSG.Quasithin.H13.KGSporLat
