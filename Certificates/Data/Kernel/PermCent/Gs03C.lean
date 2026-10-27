module

public import Certificates.Data.Kernel.PermCent.CV

public section

namespace CFSG.Certificates.Kernel.PkCV.Gs03

open CFSG.Certificates

variable {n : Nat} [Small n]

@[expose] noncomputable def wEvC (cs : List (CV n)) : List ℕ → CV n
  | [] => 1
  | l :: w => cs.getD l 1 * wEvC cs w

@[expose] noncomputable def clsC (QP : RawSchreierDatum n) (gens : List (CV n)) (k : ℕ)
    (r : CV n) (ss : List (CV n)) (ws : List (List ℕ)) : Bool :=
  (ss.length == k) && ss.all (fun x => siftC QP x 0) && (ws.length == gens.length) &&
    (gens.zip ws).all fun gw => decide (wEvC (ss.map fun x => x⁻¹ * r * x) gw.2 = gw.1)

@[expose] noncomputable def clsesC (QP : RawSchreierDatum n) (gens : List (CV n)) (k : ℕ)
    (cls : List (CV n × List (CV n) × List (List ℕ))) : Bool :=
  cls.all fun c => clsC QP gens k c.1 c.2.1 c.2.2

@[expose] noncomputable def evCls (c : CV n × List (CV n) × List (List ℕ)) :
    Equiv.Perm (Fin n) × List (Equiv.Perm (Fin n)) × List (List ℕ) :=
  (ev c.1, c.2.1.map ev, c.2.2)

@[expose] noncomputable def cOfCls (c : Equiv.Perm (Fin n) × List (Equiv.Perm (Fin n)) ×
    List (List ℕ)) : CV n × List (CV n) × List (List ℕ) :=
  (cOf c.1, c.2.1.map cOf, c.2.2)

@[expose] noncomputable def covAt (L R : List (CV n)) (g : CV n) (w : ℕ × ℕ) : Bool :=
  bif decide (w.1 < R.length) then
    decide (w.2 < L.length) && eq22C (L.getD w.2 1) (R.getD w.1 1) g (L.getD w.2 1)
  else !(powOneC g 2 && !decide (g = 1))

@[expose] noncomputable def covWC (L R : List (CV n)) (wit : List (ℕ × ℕ)) : Bool :=
  (wit.length == L.length) && (L.zip wit).all fun gw => covAt L R gw.1 gw.2

end CFSG.Certificates.Kernel.PkCV.Gs03

end
