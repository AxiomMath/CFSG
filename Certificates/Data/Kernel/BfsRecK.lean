module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.BfsRecK

open CFSG.KC.Enum

@[expose] noncomputable def recOK (k cnt : Nat) (P L POS K sig sinv : Nat → Nat)
    (stEq : Nat → Nat → Nat → Bool) : Bool :=
  Nat.beq (P 0) 0 && Nat.beq (L 0) 0 &&
    allN cnt (fun i => Nat.beq i 0 ||
      (Nat.blt (P i) i && Nat.blt (L i) k && stEq (L i) (P i) i)) &&
    allN cnt (fun i => Nat.beq i 0 || !Nat.blt (i + 1) cnt ||
      Nat.blt (k * P i + L i) (k * P (i + 1) + L (i + 1))) &&
    allN (k * cnt) (fun e => Nat.blt (POS e) cnt && stEq (e % k) (e / k) (POS e) &&
      (Nat.beq (POS e) 0 || Nat.ble (k * P (POS e) + L (POS e)) e)) &&
    allN cnt (fun j => Nat.blt (sig j) cnt && Nat.beq (sinv (sig j)) j &&
      Nat.blt (sinv j) cnt && Nat.beq (sig (sinv j)) j &&
      (!Nat.blt (j + 1) cnt || Nat.blt (K (sig j)) (K (sig (j + 1)))))

end CFSG.KC.BfsRecK

end
