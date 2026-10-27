module

public import Certificates.Data.Kernel.LocalQT.PcOm
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBaseNative
public import CFSG.Quasithin.Background.A312SporE8Check

public section

namespace CFSG.KC.HSA312

open CFSG.KC.Enum CFSG.KC.LQT.PcW CFSG.KC.LQT.PcOm
open CFSG.QuasithinUnique.K1.SporadicPerm (keyNat)

@[expose] noncomputable def appC (w m c : Nat) (T : List Nat) : List Nat := T.map (pg w m c)

@[expose] noncomputable def ptsC (w m : Nat) (B cs : List Nat) : List Nat :=
  B ++ cs.flatMap fun c => B.map (pg w m c)

@[expose] noncomputable def baseEnumC (n w m : Nat) (B cs ci : List Nat) (Ts : Array (List Nat))
    (par cl : Array Nat) : Bool :=
  Nat.blt 0 Ts.size && Ts[0]! == ptsC w m B cs && par.size == Ts.size &&
  Ts.toList.all (fun T => T.all fun x => Nat.blt x n) &&
  (List.range Ts.size).all (fun i => i == 0 ||
    (Nat.blt par[i]! i && cs.any fun c => Ts[i]! == appC w m c Ts[par[i]!]!)) &&
  distF (Ts.toList.map (keyNat n B.length)) [] &&
  (List.range Ts.size).all (fun i => (List.range cs.length).all fun j =>
    Nat.blt cl[i * (cs.length + ci.length) + j]! Ts.size &&
      Ts[cl[i * (cs.length + ci.length) + j]!]! == appC w m (cs.getD j 0) Ts[i]!) &&
  (List.range Ts.size).all (fun i => (List.range ci.length).all fun j =>
    Nat.blt cl[i * (cs.length + ci.length) + cs.length + j]! Ts.size &&
      Ts[cl[i * (cs.length + ci.length) + cs.length + j]!]! == appC w m (ci.getD j 0) Ts[i]!)

@[expose] noncomputable def extraC (w m : Nat) (B es : List Nat) (z : Nat) (Ts : Array (List Nat)) :
    Bool :=
  Ts.toList.all fun T =>
    !((List.range es.length).all fun t => (List.range B.length).all fun j =>
        T.getD (B.length * (1 + t) + j) 0 == pg w m (es.getD t 0) (T.getD j 0)) ||
      T == ptsC w m B es || T == appC w m z (ptsC w m B es)

@[expose] noncomputable def e8VPowC (vc : List Nat) (idn b i : Nat) : Nat :=
  bif b == 1 then vc.getD i 0 else idn

@[expose] noncomputable def e8BTabC (n w m idn : Nat) (vc c : List Nat) : Nat :=
  pcS n w m (pcS n w m (e8VPowC vc idn (c.getD 0 0) 0) (e8VPowC vc idn (c.getD 1 0) 1))
    (e8VPowC vc idn (c.getD 2 0) 2)

@[expose] noncomputable def e8C (n w m idn : Nat) (vc lc : List Nat) (mats : List (List (List Nat))) :
    Bool :=
  ((List.range 3).all fun i => pcS n w m (vc.getD i 0) (vc.getD i 0) == idn) &&
  ((List.range 3).all fun i => (List.range 3).all fun j =>
    pcS n w m (vc.getD i 0) (vc.getD j 0) == pcS n w m (vc.getD j 0) (vc.getD i 0)) &&
  (CFSG.Quasithin.A312S.e8NZ.all fun c => !(e8BTabC n w m idn vc c == idn)) &&
  ((List.range lc.length).all fun l => (List.range 3).all fun i =>
    pcS n w m (lc.getD l 0) (vc.getD i 0) ==
      pcS n w m (e8BTabC n w m idn vc (CFSG.Quasithin.A312S.e8Col (mats.getD l []) i)) (lc.getD l 0))

@[expose] noncomputable def labC (n w m idn : Nat) (L : Nat → Nat) (Δ v : List Nat) : List Nat :=
  srtB (Δ.map (pg w m (wordPB n w m L v idn)))

@[expose] noncomputable def gensInC (n w m idn : Nat) (L : Nat → Nat) (ws : List (List Nat))
    (Δ : List Nat) (lbl : List (List Nat)) : Bool :=
  ws.all fun v => lbl.contains (labC n w m idn L Δ v)

@[expose] def explW (nl N : Nat) (word : Nat → List Nat) : Bool :=
  word 0 == [] && (List.range N).all fun i => (word i).all fun l => Nat.blt l nl

@[expose] noncomputable def explCode (n w m idn : Nat) (Lc : Nat → Nat) (word : Nat → List Nat)
    (TC : Nat → Nat) (i : Nat) : Bool :=
  Nat.beq (wordPB n w m Lc (word i) idn) (TC i)

@[expose] noncomputable def explDist (N : Nat) (TC : Nat → Nat) : Bool :=
  distF ((List.range N).map TC) []

@[expose] noncomputable def explMul (n w m N : Nat) (mulf : Nat → Nat → Nat) (TC : Nat → Nat)
    (i : Nat) : Bool :=
  (List.range N).all fun k => Nat.blt (mulf i k) N &&
    Nat.beq (pcS n w m (TC i) (TC k)) (TC (mulf i k))

@[expose] noncomputable def explConj (n w m nl N : Nat) (Lc : Nat → Nat) (conj : List (List Nat))
    (TC : Nat → Nat) : Bool :=
  conj.length == nl && (List.range nl).all fun l => (conj.getD l []).length == N &&
    (List.range N).all fun i => Nat.blt ((conj.getD l []).getD i 0) N &&
      Nat.beq (pcS n w m (Lc l) (TC i)) (pcS n w m (TC ((conj.getD l []).getD i 0)) (Lc l))

end CFSG.KC.HSA312

end
