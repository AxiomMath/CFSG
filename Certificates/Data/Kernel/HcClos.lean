module

public import Certificates.Data.Kernel.HcReplay

public section

namespace CFSG.KC.HcPack

@[expose] noncomputable def posG (q : ℕ → ℕ → ℕ → Bool) (get : ℕ → ℕ) (n x : ℕ) (gs : List ℕ)
    (k : List ℕ → Bool) : List ℕ → Bool :=
  List.rec (motive := fun _ => List ℕ → Bool) k
    (fun g _ ih ds => List.rec (motive := fun _ => Bool) false
      (fun d ds' _ => andB (Nat.blt d n) (andB (q (get d) x g) (ih ds'))) ds) gs

@[expose] noncomputable def posB (q : ℕ → ℕ → ℕ → Bool) (get : ℕ → ℕ) (n : ℕ) (gs xs : List ℕ) :
    List ℕ → Bool :=
  List.rec (motive := fun _ => List ℕ → Bool) (fun _ => true)
    (fun x _ ih => posG q get n x gs ih) xs

@[expose] noncomputable def closB (mul : ℕ → ℕ → ℕ) (get : ℕ → ℕ) (n : ℕ) (gs xs ds : List ℕ) :
    Bool :=
  posB (fun e x g => Nat.beq e (mul x g)) get n gs xs ds

end CFSG.KC.HcPack

end
