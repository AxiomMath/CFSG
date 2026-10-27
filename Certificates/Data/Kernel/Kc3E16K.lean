module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.Kc3K

open CFSG.KC.Enum

@[expose] def packL (w : Nat) (l : List Nat) : Nat :=
  l.foldr (fun x acc => Nat.add x (Nat.shiftLeft acc w)) 0

@[expose] noncomputable def exK (w m : Nat) (TF : Nat → Nat) (u v p : Nat) : Nat :=
  pg w m (TF u) (pg w m (TF v) p)

@[expose] def maskL (l : List Nat) : Nat :=
  l.foldr (fun p acc => Nat.lor (Nat.shiftLeft 1 p) acc) 0

@[expose] def cntIn (F : Nat) (l : List Nat) : Nat :=
  l.foldr (fun p acc => cond (F.testBit p) (Nat.succ acc) acc) 0

@[expose] def chainLt : List Nat → Bool
  | a :: b :: l => decide (a < b) && chainLt (b :: l)
  | _ => true

@[expose] noncomputable def elK (w m NN N M : Nat) (TF : Nat → Nat) (B gs : List Nat)
    (eu ev ky iv kv : Nat → Nat) (tg : Nat → Nat → Nat) (k : Nat) : Bool :=
  strictB (eu k) fun u => strictB (ev k) fun v =>
    decide (u < NN) && decide (v < NN) && ky k == packL w (B.map fun b => exK w m TF u v b) &&
    (List.range gs.length).all (fun c => decide (tg c k < N) &&
      ky (tg c k) == packL w (B.map fun b => pg w m (TF (gs.getD c 0)) (exK w m TF u v b))) &&
    (!(B.all (fun b => exK w m TF u v (exK w m TF u v b) == b) &&
        B.any (fun b => exK w m TF u v b != b)) ||
      (decide (iv k < M) && kv (iv k) == k))

@[expose] noncomputable def ivK (w m N M R : Nat) (TF : Nat → Nat) (B : List Nat)
    (eu ev ky kv vu vv rt cj ri : Nat → Nat) (FR FL : Nat → List Nat) (FM : Nat → Nat) (i : Nat) :
    Bool :=
  decide (kv i < N) && vu i == eu (kv i) && vv i == ev (kv i) &&
    (!(decide (i + 1 < M)) || decide (ky (kv i) < ky (kv (i + 1)))) &&
    decide (rt i < R) && decide (ri (rt i) < M) && decide (cj i < N) &&
    (strictB (eu (cj i)) fun yu => strictB (ev (cj i)) fun yv => strictB (ri (rt i)) fun r =>
      B.all (fun b => exK w m TF (vu i) (vv i) (exK w m TF yu yv b) ==
        exK w m TF yu yv (exK w m TF (vu r) (vv r) b)) &&
      FL i == (FR (rt i)).map (exK w m TF yu yv) &&
      FM i == maskL (FL i))

@[expose] noncomputable def rtK (w m n M : Nat) (TF : Nat → Nat) (vu vv ri : Nat → Nat)
    (FR : Nat → List Nat) (ρ : Nat) : Bool :=
  decide (ri ρ < M) && (strictB (vu (ri ρ)) fun u => strictB (vv (ri ρ)) fun v =>
    chainLt (FR ρ) && (FR ρ).all (fun p => decide (p < n) && exK w m TF u v p == p) &&
    ((List.range n).filter fun p => exK w m TF u v p == p).length == (FR ρ).length)

@[expose] noncomputable def prK (w m M : Nat) (TF : Nat → Nat) (B : List Nat)
    (ky kv vu vv : Nat → Nat) (pr ct : Nat → Nat → Nat) (FL : Nat → List Nat) (FM : Nat → Nat)
    (i : Nat) : Bool :=
  strictB (vu i) fun ui => strictB (vv i) fun vi =>
    (List.range M).all fun j => strictB (pr i j) fun p =>
      p == pr j i && (!(decide (i < j)) ||
        (strictB (vu j) fun uj => strictB (vv j) fun vj =>
          cond (decide (p < M))
            (ky (kv p) == packL w (B.map fun b => exK w m TF ui vi (exK w m TF uj vj b)) &&
              ct i j == ct j i && ct i j == cntIn (FM j) (FL i))
            (B.any fun b => exK w m TF ui vi (exK w m TF uj vj b) !=
              exK w m TF uj vj (exK w m TF ui vi b))))

@[expose] def nbK (M : Nat) (pr : Nat → Nat → Nat) (NB : Nat → List Nat) (NM : Nat → Nat)
    (i : Nat) : Bool :=
  NB i == (List.range M).filter (fun j => decide (pr i j < M)) && NM i == maskL (NB i)

end CFSG.KC.Kc3K

end
