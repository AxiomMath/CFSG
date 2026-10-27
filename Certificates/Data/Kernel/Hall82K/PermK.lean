module

public import Certificates.Data.Kernel.Hall82K.Affine
public import Certificates.Data.Kernel.LocalQT.Perm

public section

namespace CFSG.KC.Hall82K

open CFSG.KC.Ord CFSG.KC.LQT.P

@[expose] noncomputable def permK (c : Nat) : Bool :=
  andB (Nat.beq (compL c idK) c)
    (CFSG.KC.LQT.P.allN 64 fun i => andB (Nat.blt (apL c i) 64)
      (CFSG.KC.LQT.P.allN 64 fun j => andB (impB (Nat.beq (apL c i) (apL c j)) (Nat.beq i j))
        (Nat.beq (apL c (Nat.xor i j)) (Nat.xor (apL c i) (apL c j)))))

end CFSG.KC.Hall82K
