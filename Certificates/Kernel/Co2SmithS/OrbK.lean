module

public import Certificates.Kernel.Co2SmithS.OrbData
public import Certificates.Kernel.Co2SmithS.Lets
public import Certificates.Data.Kernel.Co2SmithS.Orb
public import Certificates.Data.Kernel.Co2SmithS.Rows
public import Certificates.Data.Kernel.M1F2
public import Certificates.Data.Kernel.Co1F2
public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.CFSGNative.Co2Smith.Check
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo2SmithS

open CFSG.KC.Co2SmithS CFSG.KC.Co2InvS CFSG.KC.Enum CFSG.Sporadic.Co2Smith.Native

@[expose] noncomputable def PT (g i : Nat) : Nat := pg (nat_lit 44) (nat_lit 17592186044415) (OPT g) i

@[expose] noncomputable def PI (g j i : Nat) : Nat :=
  pg (nat_lit 16) (nat_lit 65535) (OPI (Nat.add (Nat.mul (nat_lit 16) g) j)) i

@[expose] noncomputable def abT (l : Nat) : Nat :=
  if l = 0 then CFSG.KC.Co1F2.trK 22 (mulV (LT 2) IDP) else CFSG.KC.Co1F2.trK 22 (mulV (LT 3) IDP)

@[expose] noncomputable def pairStepK (l x : Nat) : Nat :=
  CFSG.KC.M1F2.vmF 22 (abT l) (x / 4194304) * 4194304 + CFSG.KC.M1F2.vmF 22 (abT l) (x % 4194304)

@[expose] noncomputable def chT (k l : Nat) : Nat :=
  CFSG.KC.Co1F2.trK 22 (wK LT (((chainGens ())[k]!)[l]!))

@[expose] noncomputable def chainStepK (k l x : Nat) : Nat := CFSG.KC.M1F2.vmF 22 (chT k l) x

@[expose] noncomputable def zT : Nat := CFSG.KC.Co1F2.trK 22 (LT 0)

theorem pair_ok : ∀ i < 7560, orbRecK pairStepK 2 7560 (pairU * 4194304 + pairV) (PT 0) (PI 0 0)
    (PI 0 1) (PI 0 2) (PI 0 3) (fun i l => PI 0 (4 + l) i) i = true := by
  kc_cover 512

theorem pairX_ok : (Nat.beq (PI 0 2 7560) 7560 &&
    (List.range 7560).all (fun i => !Nat.beq (PT 0 i)
      (CFSG.KC.M1F2.vmF 22 zT pairU * 4194304 + CFSG.KC.M1F2.vmF 22 zT pairV)) &&
    decide (pairU < 4194304) && decide (pairV < 4194304)) = true := by
  decide +kernel

@[expose] noncomputable def chainRecOK (k : Nat) : Bool :=
  (List.range (chainOrb[k]!)).all (fun i => orbRecK (chainStepK k) ((chainGens ())[k]!.size)
    (chainOrb[k]!) chainBase[k]! (PT (k + 1)) (PI (k + 1) 0) (PI (k + 1) 1) (PI (k + 1) 2)
    (PI (k + 1) 3) (fun i l => PI (k + 1) (4 + l) i) i) &&
  Nat.beq (PI (k + 1) 2 (chainOrb[k]!)) (chainOrb[k]!) && decide (0 < chainOrb[k]!) &&
  decide (chainOrb[k]! ≤ 100)

theorem chain_ok : ((chainGens ()).size == 6 && chainBase.length == 6 && chainOrb.length == 6 &&
    (List.range 6).all (fun k => chainRecOK k && (chainGens ())[k]!.toList.all
      (fun w => w.all (· < 4)) &&
      (List.range k).all fun j => (List.range ((chainGens ())[k]!.size)).all fun l =>
        Nat.beq (chainStepK k l chainBase[j]!) chainBase[j]!)) = true := by
  decide +kernel

theorem orb_neg : (!orbRecK pairStepK 2 7560 (pairU * 4194304 + pairV + 1) (PT 0) (PI 0 0) (PI 0 1)
    (PI 0 2) (PI 0 3) (fun i l => PI 0 (4 + l) i) 0 &&
    !orbRecK (chainStepK 0) 2 63 chainBase[1]! (PT 1) (PI 1 0) (PI 1 1) (PI 1 2) (PI 1 3)
      (fun i l => PI 1 (4 + l) i) 0) = true := by
  decide +kernel

end CertificateChecks.KernelCo2SmithS

end
