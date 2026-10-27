module

public import Certificates.Kernel.CoPair.Gens
public import CFSG.Certificates.Kernel.CoPairSound
public import Certificates.Data.CFSGNative.MonsterAxis.CoPairData
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCoPair

open CFSG.KC.CoPair CFSG.Monster.Existence.CoPair.Native

@[expose] def W2PText : String := include_str "w2p.hex"

@[expose] def W2EText : String := include_str "w2e.hex"

@[expose] noncomputable def W2P : Nat := by hex_nat W2PText 27600 9989267341649362001

@[expose] noncomputable def W2E : Nat := by hex_nat W2EText 73598 17188208299167459126

@[expose] noncomputable def W2D : OrbData := ⟨MX, MY, TX, TY, W2P, W2E, 11⟩

theorem w2c0 : allR 0 1000 (orbPt TX TY W2P W2E 4600 11) = true := by quickRfl
theorem w2c1 : allR 1000 1000 (orbPt TX TY W2P W2E 4600 11) = true := by quickRfl
theorem w2c2 : allR 2000 1000 (orbPt TX TY W2P W2E 4600 11) = true := by quickRfl
theorem w2c3 : allR 3000 1000 (orbPt TX TY W2P W2E 4600 11) = true := by quickRfl
theorem w2c4 : allR 4000 600 (orbPt TX TY W2P W2E 4600 11) = true := by quickRfl

theorem w2seed : Nat.beq (f24 W2P 11) (seedW2 ()) = true := by quickRfl

theorem w2_ok : orbOK xWordN yWordN seedW2 4600 W2D = true :=
  orbOK_intro rowsX rowsY tabX tabY (by decide) (Nat.eq_of_beq_eq_true w2seed)
    (all_of_allR (all_of_allR (all_of_allR (all_of_allR (all_of_allR
      (fun i hi => absurd hi (Nat.not_lt_zero i)) w2c0) w2c1) w2c2) w2c3) w2c4)

end CertificateChecks.KernelCoPair

end
