module

public import Certificates.Data.Kernel.PermCent.Ok122C

public section

namespace CFSG.Certificates.Kernel.PkCV

instance smallC6 : Small 6 := ⟨by decide⟩

variable {n : Nat}

@[expose] def forceOL {β : Sort _} : List (CV n × List (CV n)) → (List (CV n × List (CV n)) → β) → β
  | [], k => k []
  | a :: l, k => forceC a.1 fun c => forceCL a.2 fun L => forceOL l fun l => k ((c, L) :: l)

@[expose] noncomputable def gWC (a1 a2 a12 c : CV 6) : Bool :=
  forceC c fun c => cmC c a1 && !powOneC c 1 && !Nat.beq c.1 a1.1 && !Nat.beq c.1 a2.1 &&
    !Nat.beq c.1 a12.1

@[expose] noncomputable def c6B (I : List (CV 6)) (OC : List (CV 6 × List (CV 6))) : Bool :=
  I.all fun a1 => I.all fun a2 =>
    !(cmC a1 a2 && !Nat.beq a1.1 a2.1) ||
    forceC (a1 * a2) fun a12 =>
    OC.all fun p =>
      !((eq22C p.1 a1 a2 p.1 || eq22C p.1 a1 a12 p.1) &&
        (eq22C p.1 a2 a1 p.1 || eq22C p.1 a2 a2 p.1 || eq22C p.1 a2 a12 p.1)) ||
      forceC p.1⁻¹ fun τi =>
      p.2.all fun b =>
        !(!powOneC b 1 && !Nat.beq b.1 p.1.1 && !Nat.beq b.1 τi.1) ||
        forceC b⁻¹ fun bi =>
          gWC a1 a2 a12 (b * a2 * bi * a1 * a2 * b) || gWC a1 a2 a12 (b * a1 * bi * a1 * b) ||
            gWC a1 a2 a12 (b * a1 * a2 * bi * a2 * b)

@[expose] noncomputable def inv6P (L : List (CV 6 × Bool)) : List (CV 6) :=
  (L.filter fun x => !x.2 && powOneC x.1 2 && !powOneC x.1 1).map Prod.fst

@[expose] noncomputable def ord6P (L : List (CV 6 × Bool)) : List (CV 6) :=
  (L.filter fun x => powOneC x.1 3 && !powOneC x.1 1).map Prod.fst

@[expose] def evenP {m : Nat} (L : List (CV m × Bool)) : List (CV m) :=
  (L.filter fun x => !x.2).map Prod.fst

@[expose] noncomputable def c6F : Bool :=
  forcePL (allPermsP 6 inferInstance) fun L =>
    forceCL (inv6P L) fun I => forceCL (evenP L) fun E => forceCL (ord6P L) fun O =>
      forceOL (O.map fun τ => (τ, E.filter fun b => cmC b τ)) fun OC => c6B I OC

@[expose] noncomputable def f5F : Bool :=
  forcePL (allPermsP 5 inferInstance) fun L => forceCL (evenP L) fun E =>
    L.all fun x => !(powOneC x.1 3 && !powOneC x.1 1) || forceC x.1⁻¹ fun ti =>
      E.all fun b => !cmC b x.1 || (powOneC b 1 || Nat.beq b.1 x.1.1 || Nat.beq b.1 ti.1)

end CFSG.Certificates.Kernel.PkCV

end
