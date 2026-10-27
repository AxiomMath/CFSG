module

public import Certificates.Data.Kernel.KDense.Init

public section

namespace CFSG.KC.KDense

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop

@[expose] noncomputable def keyPlane (F : Fix) (b : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (plane SX (Nat.sub b (nat_lit 12)) F.keyD) (plane SX b F.keyA) (Nat.blt b (nat_lit 12))

@[expose] noncomputable def keysDistinctOK (F : Fix) (NK : Nat) : Bool :=
  andB (netOK (nat_lit 17) NK) (andB (Nat.beq (netP SX (nat_lit 17) (nat_lit 1) NK validX) (ones (nat_lit 98280)))
    (Prod.rec (motive := fun _ => Bool) (fun lt _ => Nat.beq (Nat.land lt (ones (nat_lit 98279))) (ones (nat_lit 98279)))
      (Nat.rec (motive := fun _ => Nat × Nat) (nat_lit 0, ones SX)
        (fun j ih => Prod.rec (motive := fun _ => Nat × Nat) (fun lt eq =>
          (fun x => (fun y => (Nat.lor lt (Nat.land eq (Nat.land (Nat.xor (ones SX) x) y)),
              Nat.land eq (Nat.xor (ones SX) (Nat.xor x y))))
            (Nat.land (Nat.shiftRight x (nat_lit 1)) (ones (Nat.sub SX (nat_lit 1)))))
          (netP SX (nat_lit 17) (nat_lit 1) NK (keyPlane F (Nat.sub (nat_lit 23) j)))) ih)
        (nat_lit 24))))

end CFSG.KC.KDense

end
