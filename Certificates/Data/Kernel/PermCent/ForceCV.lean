module

public import Certificates.Data.Kernel.PermCent.CV
public import Certificates.Data.Kernel.PermCent.SmallB
public import Certificates.Data.Kernel.PermCent.SmallK
public import Certificates.Data.Kernel.Census.CatFacts.PkWord

public section

namespace CFSG.Certificates.Kernel.PkCV

open CFSG.Certificates.Kernel.PkEnum

instance smallF4 : Small 4 := ⟨by decide⟩

variable {n : Nat}

@[expose] def forceC {β : Sort _} (a : CV n) (k : CV n → β) : β :=
  forceD a.1 fun p hp => k ⟨p, hp ▸ a.2⟩

@[expose] def forceCL {β : Sort _} : List (CV n) → (List (CV n) → β) → β
  | [], k => k []
  | a :: l, k => forceC a fun a => forceCL l fun l => k (a :: l)

@[expose] def memC (p : Nat) (L : List (CV n)) : Bool := L.any fun c => Nat.beq p c.1

variable [Small n]

@[expose] noncomputable def groupF (L : List (CV n)) : Bool :=
  forceCL L fun L => decide L.Nodup &&
    (L.all fun a => L.all fun b => forceD (a * b).1 fun p _ => memC p L) &&
    L.all fun a => forceD a⁻¹.1 fun p _ => memC p L

end CFSG.Certificates.Kernel.PkCV

end
