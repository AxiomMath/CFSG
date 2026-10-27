
module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312HsPCore
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312HsKInputs
import Certificates.Kernel.HSA312.Struct
import Certificates.Kernel.HSQuot.Final
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatIncl
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHSBase
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHSBase

@[expose] public section

namespace CFSG.Quasithin.A312Hs

open CFSG.Quasithin
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.HS
open CFSG.Sporadic.HS.Native (hsData)

section Rows

variable {Γ : Type} [Group Γ]

theorem card_pCore_of_card_pCoreOf {Y : Subgroup Γ} {k : ℕ}
    (h : Nat.card (CFSG.Open.pCoreOf 2 Y) = k) : Nat.card (CFSG.pCore 2 ↥Y) = k := by
  have h1 : CFSG.Open.pCoreOf 2 Y = (CFSG.pCore 2 ↥Y).map Y.subtype := by
    unfold CFSG.Open.pCoreOf
    try with_reducible rfl
  rwa [h1, Subgroup.card_map_of_injective Y.subtype_injective] at h

end Rows

end CFSG.Quasithin.A312Hs
