module

public import CFSG.LocalAnalysis.StandardType.GGResIIPoly
public import CFSG.LocalAnalysis.StandardType.GGResIIWitness

public section

namespace CFSG.StandardType

namespace GGPoly

variable {N : ℕ}

@[expose] def fdot (a z : Vector GGPoly (N + 1)) : GGPoly :=
  (List.finRange (N + 1)).foldr (fun l acc => add (mul (a.get l) (z.get l)) acc) []

@[expose] def frefl (T : Fin N → Vector GGPoly (N + 1)) (k : Fin N) (z : Vector GGPoly (N + 1)) :
    Vector GGPoly (N + 1) :=
  (fun d => Vector.ofFn fun l => if l = k.castSucc then sub (z.get l) d else z.get l)
    (fdot (T k) z)

@[expose] def fword (T : Fin N → Vector GGPoly (N + 1)) (ws : List (Fin N))
    (z : Vector GGPoly (N + 1)) : Vector GGPoly (N + 1) :=
  ws.foldr (fun k acc => frefl T k acc) z

@[expose] def funit (k : Fin (N + 1)) : Vector GGPoly (N + 1) :=
  Vector.ofFn fun l => if l = k then const 1 else []

@[expose] def fdualAt (T : Fin N → Vector GGPoly (N + 1)) (c : Vector GGPoly N) (j : Fin N) :
    GGPoly :=
  (List.finRange N).foldr (fun o acc => add (mul (c.get o) ((T o).get j.castSucc)) acc) []

@[expose] def fdrefl (T : Fin N → Vector GGPoly (N + 1)) (j : Fin N) (c : Vector GGPoly N) :
    Vector GGPoly N :=
  (fun d => Vector.ofFn fun o => if o = j then sub (c.get o) d else c.get o) (fdualAt T c j)

@[expose] def fdword (T : Fin N → Vector GGPoly (N + 1)) (ws : List (Fin N)) (c : Vector GGPoly N) :
    Vector GGPoly N :=
  ws.foldl (fun acc k => fdrefl T k acc) c

@[expose] def fdunit (k : Fin N) : Vector GGPoly N :=
  Vector.ofFn fun o => if o = k then const 1 else []

@[expose] def fA (T : Fin N → Vector GGPoly (N + 1)) (t : Fin N × List (Fin N)) :
    Vector GGPoly N :=
  (fun H => Vector.ofFn fun j => fdot (T j) H) (fword T t.2 (funit t.1.castSucc))

@[expose] def fC (T : Fin N → Vector GGPoly (N + 1)) (t : Fin N × List (Fin N)) : Vector GGPoly N :=
  fdword T t.2.reverse (fdunit t.1)

@[expose] def frootAt (T : Fin N → Vector GGPoly (N + 1)) (c : Vector GGPoly N)
    (z : Vector GGPoly (N + 1)) : GGPoly :=
  (List.finRange N).foldr (fun o acc => add (mul (c.get o) (fdot (T o) z)) acc) []

section Eval

variable {S : Type} [CommRing S] (u v : S)

@[expose] def evalV {M : ℕ} (z : Vector GGPoly M) : Vector S M := z.map (eval u v)

@[expose] def evalT (T : Fin N → Vector GGPoly (N + 1)) : Fin N → Vector S (N + 1) :=
  fun i => evalV u v (T i)

theorem get_evalV {M : ℕ} (z : Vector GGPoly M) (l : Fin M) :
    (evalV u v z).get l = eval u v (z.get l) := by
  simp [evalV, Vector.get_map]

private theorem eval_foldr_add {M : ℕ} (F : Fin M → GGPoly) :
    eval u v ((List.finRange M).foldr (fun l acc => add (F l) acc) []) =
      ∑ l : Fin M, eval u v (F l) := by
  rw [← List.sum_ofFn, List.ofFn_eq_map]
  induction (List.finRange M) with
  | nil => rfl
  | cons l L ih => rw [List.foldr_cons, eval_add, ih, List.map_cons, List.sum_cons]

theorem eval_fdot (a z : Vector GGPoly (N + 1)) :
    eval u v (fdot a z) = ggFDot (evalV u v a) (evalV u v z) := by
  rw [fdot, eval_foldr_add, ggFDot]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [eval_mul, get_evalV, get_evalV]

theorem evalV_frefl (T : Fin N → Vector GGPoly (N + 1)) (k : Fin N) (z : Vector GGPoly (N + 1)) :
    evalV u v (frefl T k z) = ggFRefl (evalT u v T) k (evalV u v z) := by
  ext l hl
  simp only [frefl, ggFRefl]
  rw [show (evalV u v (Vector.ofFn fun l => if l = k.castSucc then sub (z.get l) (fdot (T k) z)
      else z.get l))[l] = (evalV u v (Vector.ofFn fun l => if l = k.castSucc then
      sub (z.get l) (fdot (T k) z) else z.get l)).get ⟨l, hl⟩ from rfl,
    show (Vector.ofFn fun l : Fin (N + 1) => if l = k.castSucc then
      (evalV u v z).get l - ggFDot (evalT u v T k) (evalV u v z) else (evalV u v z).get l)[l] =
      (Vector.ofFn fun l : Fin (N + 1) => if l = k.castSucc then
      (evalV u v z).get l - ggFDot (evalT u v T k) (evalV u v z) else (evalV u v z).get l).get
        ⟨l, hl⟩ from rfl]
  rw [get_evalV, Vector.get_ofFn, Vector.get_ofFn]
  split_ifs
  · rw [eval_sub, eval_fdot, get_evalV]
    rfl
  · rw [get_evalV]

theorem evalV_fword (T : Fin N → Vector GGPoly (N + 1)) (ws : List (Fin N))
    (z : Vector GGPoly (N + 1)) :
    evalV u v (fword T ws z) = ggFWord (evalT u v T) ws (evalV u v z) := by
  induction ws with
  | nil => rfl
  | cons k ws ih =>
    change evalV u v (frefl T k (fword T ws z)) = ggFRefl (evalT u v T) k
      (ggFWord (evalT u v T) ws (evalV u v z))
    rw [evalV_frefl, ih]

theorem evalV_funit (k : Fin (N + 1)) : evalV u v (funit k) = (ggFUnit k : Vector S (N + 1)) := by
  ext l hl
  change (evalV u v (funit k)).get ⟨l, hl⟩ = (ggFUnit k : Vector S (N + 1)).get ⟨l, hl⟩
  rw [get_evalV, funit, ggFUnit, Vector.get_ofFn, Vector.get_ofFn]
  split_ifs
  · rw [eval_const, Int.cast_one]
  · rfl

theorem eval_fdualAt (T : Fin N → Vector GGPoly (N + 1)) (c : Vector GGPoly N) (j : Fin N) :
    eval u v (fdualAt T c j) = ggFDualAt (evalT u v T) (evalV u v c) j := by
  rw [fdualAt, eval_foldr_add, ggFDualAt]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [eval_mul, get_evalV, evalT, get_evalV]

theorem evalV_fdrefl (T : Fin N → Vector GGPoly (N + 1)) (j : Fin N) (c : Vector GGPoly N) :
    evalV u v (fdrefl T j c) = ggFDRefl (evalT u v T) j (evalV u v c) := by
  ext o ho
  change (evalV u v (fdrefl T j c)).get ⟨o, ho⟩ =
    (ggFDRefl (evalT u v T) j (evalV u v c)).get ⟨o, ho⟩
  rw [get_evalV, fdrefl, ggFDRefl, Vector.get_ofFn, Vector.get_ofFn]
  split_ifs
  · rw [eval_sub, eval_fdualAt, get_evalV]
  · rw [get_evalV]

theorem evalV_fdword (T : Fin N → Vector GGPoly (N + 1)) (ws : List (Fin N))
    (c : Vector GGPoly N) :
    evalV u v (fdword T ws c) = ggFDWord (evalT u v T) ws (evalV u v c) := by
  induction ws generalizing c with
  | nil => rfl
  | cons k ws ih =>
    change evalV u v (fdword T ws (fdrefl T k c)) = ggFDWord (evalT u v T) ws
      (ggFDRefl (evalT u v T) k (evalV u v c))
    rw [ih, evalV_fdrefl]

theorem evalV_fdunit (k : Fin N) : evalV u v (fdunit k) = (ggFDUnit k : Vector S N) := by
  ext o ho
  change (evalV u v (fdunit k)).get ⟨o, ho⟩ = (ggFDUnit k : Vector S N).get ⟨o, ho⟩
  rw [get_evalV, fdunit, ggFDUnit, Vector.get_ofFn, Vector.get_ofFn]
  split_ifs
  · rw [eval_const, Int.cast_one]
  · rfl

theorem eval_fA (T : Fin N → Vector GGPoly (N + 1)) (t : Fin N × List (Fin N)) (j : Fin N) :
    eval u v ((fA T t).get j) = ggFA (evalT u v T) t j := by
  rw [fA, Vector.get_ofFn, eval_fdot, evalV_fword, evalV_funit, ggFA]
  rfl

theorem evalV_fC (T : Fin N → Vector GGPoly (N + 1)) (t : Fin N × List (Fin N)) :
    evalV u v (fC T t) = ggFC (evalT u v T) t := by
  rw [fC, evalV_fdword, evalV_fdunit, ggFC]

theorem eval_fC (T : Fin N → Vector GGPoly (N + 1)) (t : Fin N × List (Fin N)) (o : Fin N) :
    eval u v ((fC T t).get o) = (ggFC (evalT u v T) t).get o := by
  rw [← evalV_fC, get_evalV]

theorem eval_frootAt (T : Fin N → Vector GGPoly (N + 1)) (c : Vector GGPoly N)
    (z : Vector GGPoly (N + 1)) :
    eval u v (frootAt T c z) = ggFRootAt (evalT u v T) (evalV u v c) (evalV u v z) := by
  rw [frootAt, eval_foldr_add, ggFRootAt]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [eval_mul, eval_fdot, get_evalV, evalT]

end Eval

end GGPoly

end CFSG.StandardType
