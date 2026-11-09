module

public import Certificates.Data.Kernel.SporLatDc

public section

namespace CFSG.KC.SLDc

@[expose] def omOKL {Lab : Type} [DecidableEq Lab] [Inhabited Lab] (actF : Nat → Lab → Lab)
    (x0 : Lab) (nl : Nat) (O : CFSG.QuasithinUnique.Ch1.SporLat.OmegaData Lab) : Bool :=
  decide (O.lbl.toList.getD 0 default = x0) && decide (0 < O.lbl.toList.length) &&
    (List.range nl).all (fun l => (List.range O.lbl.toList.length).all fun i =>
      decide (((O.pn.toList.getD l default).toList.getD i default) < O.lbl.toList.length) &&
        decide (O.lbl.toList.getD ((O.pn.toList.getD l default).toList.getD i default) default =
          actF l (O.lbl.toList.getD i default))) &&
    (List.range O.lbl.toList.length).all (fun i => i == 0 ||
      (decide (O.par.toList.getD i default < i) && decide (O.via.toList.getD i default < nl) &&
        (O.pn.toList.getD (O.via.toList.getD i default) default).toList.getD
          (O.par.toList.getD i default) default == i)) &&
    decide O.lbl.toList.Nodup

theorem getElem!_eq_getD_omL {α : Type} [Inhabited α] (a : Array α) (i : Nat) :
    a[i]! = a.toList.getD i default := by
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, getElem!_def]
  cases a[i]? <;> rfl

theorem omOKL_eq : @omOKL = @omOKG := by
  funext Lab _ _ actF x0 nl O
  simp only [omOKL, omOKG, getElem!_eq_getD_omL, Array.size]

end CFSG.KC.SLDc

end
