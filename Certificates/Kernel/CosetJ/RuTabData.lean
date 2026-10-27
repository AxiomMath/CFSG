module

public import Init
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

namespace CertificateChecks.KernelCosetJ.RuTab

#kc_repo #kc_nat_items_gz CertificateChecks.KernelCosetJ.RuTab
  "Certificates/Kernel/CosetJ/data/RuTabData.items.gz" 5902 4359731871632806012
  (G 1 11)

#kc_repo #kc_json_gz CertificateChecks.KernelCosetJ.RuTab
  "Certificates/Kernel/CosetJ/data/RuTabData.json.gz" 60054 15410069550640573302
  (RI : List (List (Nat × Bool))) (RT : List (List (Nat × Bool)))

@[expose] noncomputable def RG (k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (G10) (G9) (Nat.blt k (nat_lit 10))) (G8) (Nat.blt k (nat_lit 9))) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (G7) (G6) (Nat.blt k (nat_lit 7))) (G5) (Nat.blt k (nat_lit 6))) (Nat.blt k (nat_lit 8))) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (G4) (G3) (Nat.blt k (nat_lit 4))) (G2) (Nat.blt k (nat_lit 3))) (Bool.rec (motive := fun _ => Nat) (G1) (nat_lit 0) (Nat.blt k (nat_lit 1))) (Nat.blt k (nat_lit 2))) (Nat.blt k (nat_lit 5))) (Nat.blt k (nat_lit 11))

end CertificateChecks.KernelCosetJ.RuTab

end
