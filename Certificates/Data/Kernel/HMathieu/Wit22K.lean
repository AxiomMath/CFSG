module

public import Certificates.Data.Kernel.HMathieu.Bfs
public import CFSG.Quasithin.H13.A5M22HatInputs
public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.HMathieu

open CFSG.KC.Enum CFSG.KS CFSG.Quasithin.H13.A5.M22Hat

@[expose] noncomputable def poolP : List Nat :=
  [385186268308509128468048256697913376, 605251439709246669493550984188045344,
    670397833609487708988406303928228896, 887261872910891192523348484881459232,
    522532126434174487728779852004447264, 916696840240582501193088347382729760]

@[expose] noncomputable def poolI : List Nat :=
  [893321682357476910108114413510075424, 219917916642175089009789275541344288,
    464897295487069016792816453669101600, 317679939632640064777115990450419744,
    133789694659092030616633741329764384, 487121465593190225092493745991374880]

@[expose] noncomputable def pcS (p q : Nat) : Nat :=
  strictN p fun p => strictN q fun q => pc24 p q

@[expose] noncomputable def conjK (a ai t : Nat) : Nat := pcS (pcS a t) ai

@[expose] noncomputable def powK (a k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pidn 24 5) (fun _ ih => pcS a ih) k

@[expose] noncomputable def fixK (q : Nat) : Bool :=
  (List.range 24).all fun i => pg 5 (mask 5) q i == i

@[expose] noncomputable def ord11K (a : Nat) : Bool :=
  (List.range 24).any (fun i => pg 5 (mask 5) a i != i) && strictB (powK a 11) fixK

@[expose] noncomputable def prod4K (t a ai b bi c ci : Nat) : Nat :=
  pcS (pcS t (conjK a ai t)) (pcS (conjK b bi t) (conjK c ci t))

@[expose] noncomputable def witK (e p : Nat) : Bool :=
  strictB wit22I[p]! fun i => strictB wit22J[p]! fun j => strictB wit22K[p]! fun k =>
    decide (i < 6) && decide (j < 6) && decide (k < 6) &&
      ord11K (prod4K e (poolP.getD i 0) (poolI.getD i 0) (poolP.getD j 0) (poolI.getD j 0)
        (poolP.getD k 0) (poolI.getD k 0))

@[expose] noncomputable def inv24K (e : Nat) : Bool :=
  (List.range 24).all fun i => pg 5 (mask 5) e (pg 5 (mask 5) e i) == i

@[expose] noncomputable def chk7106K (E : List Nat) (s : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun e _ ih p => (p == 0 || !inv24K e || witK e p) && ih (p + 1)) E s

end CFSG.KC.HMathieu

end
