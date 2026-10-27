module

public import Certificates.Data.Kernel.M3BFib.Kit

public section

namespace CFSG.KC.M3BF

abbrev EK := Nat × Nat

@[expose] noncomputable def betaK (a b : Nat) : Nat := dot (dig (vm (dig3 a) LpM)) (dig3 b)

@[expose] noncomputable def emulK (x y : EK) : EK :=
  (enc (List.zipWith (fun a b => Nat.mod (Nat.add a b) 3) (dig3 x.1) (dig3 y.1)),
    Nat.mod (Nat.add (Nat.add x.2 y.2) (betaK x.1 y.1)) 3)

@[expose] noncomputable def sqK (x : EK) : EK := emulK (emulK (0, 0) x) x

@[expose] noncomputable def substP (T : PD) (x : EK) : EK :=
  (fun P : PD => (P.1.headD 0, P.2.1.headD 0))
    (compK LpM (x.1 :: List.replicate 11 0, x.2 :: List.replicate 11 0, 1) T)

@[expose] noncomputable def padV (v : List Nat) : List Nat := (List.range 12).map fun i => v.getD i 0

@[expose] noncomputable def eP (v : List Nat) : EK := (enc (padV v), 0)

@[expose] noncomputable def nfRows (x : EK) : List EK :=
  (List.range 12).map fun i => emulK (emulK (sqK x) (Nat.pow 64 i, 0)) x

@[expose] noncomputable def nfL (v : List Nat) : PD :=
  (fun rs : List EK => (rs.map Prod.fst, rs.map Prod.snd, 1)) (nfRows (eP v))

@[expose] noncomputable def cubeK (T : PD) (x : EK) : EK :=
  (fun y => emulK (emulK (substP T y) y) x) (substP T x)

@[expose] noncomputable def zconjK (T : PD) (x y : EK) : EK :=
  emulK (emulK (substP T (sqK y)) x) y

@[expose] noncomputable def vOKB (v : List Nat) : Bool := (padV v).all fun d => Nat.blt d 3

@[expose] noncomputable def repRK (ts : List PD) (k : Nat) (v : List Nat) : PD :=
  if k = 0 then nfL v else compK LpM (ts.getD k oneK) (nfL v)

@[expose] noncomputable def rootOKF (ts : List PD) (c : Nat × List Nat × Nat × List Nat) : Bool :=
  Nat.blt c.1 4 && vOKB c.2.1 &&
    (if c.2.2.1 = 0 then !pdEq (powK LpM (repRK ts c.1 c.2.1) 3) oneK
    else if c.2.2.1 = 4 then pdEq (repRK ts c.1 c.2.1) oneK
    else !pdEq (repRK ts c.1 c.2.1) oneK &&
      (if c.2.2.1 = 1 then
        (cubeK (ts.getD c.1 oneK) (eP c.2.1)).1 == 0 &&
          ((cubeK (ts.getD c.1 oneK) (eP c.2.1)).2 == 1 ||
            (cubeK (ts.getD c.1 oneK) (eP c.2.1)).2 == 2)
      else cubeK (ts.getD c.1 oneK) (eP c.2.1) == (0, 0)) &&
      (c.2.2.1 != 3 || (vOKB c.2.2.2 &&
        zconjK (ts.getD c.1 oneK) (eP c.2.1) (eP c.2.2.2) == emulK (eP c.2.1) (0, 1))))

@[expose] noncomputable def rootChkF (ts : List PD) (cs : List (Nat × List Nat × Nat × List Nat)) :
    Bool :=
  cs.all (rootOKF ts)

end CFSG.KC.M3BF

end
