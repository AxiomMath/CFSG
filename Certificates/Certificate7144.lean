module

public import CFSG.Quasithin.Vol2.KGFactSporLatInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatExport
public import CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate2197
public import Certificates.Certificate4075
import Certificates.Kernel.M23Dc.O2

public section

namespace Certificates

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat CFSG.Quasithin.H13.KGSporLat in
open CFSG.Open (pCoreOf) in
theorem certificate7144 : ∀ {X : Type} [Group X]
    [Finite X], Nonempty (X ≃* ↥CFSG.Blueprint.NativeSporadic.M23) →
    ∀ {T Y : Subgroup X}, IsSylowTwoOf T ⊤ → T ≤ Y →
      Y = ⊤ ∨ ∃ m ∈ m23Mems, Nat.card Y = m.order ∧ Nat.card (pCoreOf 2 Y) = m.o2 ∧
        ∀ (N : Subgroup Y) [N.Normal], IsPGroup 2 (Y ⧸ N) → Nat.card (Y ⧸ N) ≤ m.quot2 :=
  fun hX _ _ hT hTY => CFSG.KD.M23Dc.m23K_overgroups hX hT hTY

end Certificates
