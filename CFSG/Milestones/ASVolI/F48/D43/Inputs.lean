module

public import CFSG.Milestones.ASVolI.F48.D43.Data
public import CFSG.LieType.Ree.Mirror
public import Certificates.Data.CFSGNative.ONSchreier.Vectors
public import Certificates.Data.CFSGNative.MonsterB.Co2Data

public section

namespace CFSG.ASVolI

open CFSG.F3.Native CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.ON.Native
open CFSG.Monster.B.Co2.Native (hexTable)
open CFSG.Blueprint.Chevalley

set_option compiler.extract_closed false

@[expose] def burnsideF48d_addC (a b : ℕ) : ℕ :=
  (a % 3 + b % 3) % 3 + 3 * ((a / 3 % 3 + b / 3 % 3) % 3) + 9 * ((a / 9 % 3 + b / 9 % 3) % 3)

@[expose] def burnsideF48d_mulC (a b : ℕ) : ℕ :=
  (a % 3 * (b % 3) + a / 3 % 3 * (b / 9 % 3) + a / 9 % 3 * (b / 3 % 3)) % 3 +
    3 * ((a % 3 * (b / 3 % 3) + a / 3 % 3 * (b % 3) + a / 3 % 3 * (b / 9 % 3) +
      a / 9 % 3 * (b / 3 % 3) + a / 9 % 3 * (b / 9 % 3)) % 3) +
    9 * ((a % 3 * (b / 9 % 3) + a / 3 % 3 * (b / 3 % 3) + a / 9 % 3 * (b % 3) +
      a / 9 % 3 * (b / 9 % 3)) % 3)

@[expose] def burnsideF48d_powC (a : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => burnsideF48d_mulC a (burnsideF48d_powC a k)

@[expose] def burnsideF48d_frobC (a : ℕ) : ℕ :=
  burnsideF48d_mulC a (burnsideF48d_mulC a a)

@[expose] def burnsideF48d_intC (z : ℤ) : ℕ := (z % 3).toNat

abbrev burnsideF48d_C : RootCertificate .D4 := Tag.rootCertificate .D4

@[expose] def burnsideF48d_idx (b : ℕ) : CFSG.LieType.Ree.Idx burnsideF48d_C :=
  if h : b < 4 then .inl ⟨b, h⟩ else
    if h' : b - 4 < burnsideF48d_C.roots.length then .inr ⟨b - 4, h'⟩ else .inl ⟨0, by decide⟩

@[expose] def burnsideF48d_ofIdx : CFSG.LieType.Ree.Idx burnsideF48d_C → ℕ
  | .inl j => j.val
  | .inr m => 4 + m.val

@[expose] def burnsideF48d_col (y : Bool) (i k b : ℕ) : Option (ℕ × ℤ) :=
  if hi : i < 4 then
    ((if y then CFSG.LieType.Ree.yCol burnsideF48d_C (Tag.stringData .D4) ⟨i, hi⟩ k
        (burnsideF48d_idx b)
      else CFSG.LieType.Ree.xCol burnsideF48d_C (Tag.stringData .D4) ⟨i, hi⟩ k
        (burnsideF48d_idx b))).map fun p => (burnsideF48d_ofIdx p.1, p.2)
  else none

@[expose] def burnsideF48d_colTab (_ : Unit := ()) :
    Array (Array (Array (Array (Option (ℕ × ℤ))))) :=
  #[false, true].map fun y => (Array.range 4).map fun i => (Array.range 4).map fun k =>
    (Array.range 28).map fun b => burnsideF48d_col y i k b

@[expose] def burnsideF48d_opStep (col : Option (ℕ × ℤ)) (cw : ℕ) (out : Array ℕ) : Array ℕ :=
  match col with
  | none => out
  | some (a, z) =>
    out.set! a (burnsideF48d_addC out[a]! (burnsideF48d_mulC cw (burnsideF48d_intC z)))

@[expose] def burnsideF48d_opCoord (T : Array (Array (Array (Array (Option (ℕ × ℤ))))))
    (y : Bool) (i c : ℕ) (w : Array ℕ) (out : Array ℕ) (b : ℕ) : Array ℕ :=
  if w[b]! = 0 then out else
    (List.range 4).foldl (fun out k =>
      burnsideF48d_opStep ((((T[if y then 1 else 0]!)[i]!)[k]!)[b]!)
        (burnsideF48d_mulC w[b]! (burnsideF48d_powC c k)) out) out

@[expose] def burnsideF48d_applyOp (T : Array (Array (Array (Array (Option (ℕ × ℤ))))))
    (y : Bool) (i c : ℕ) (w : Array ℕ) : Array ℕ :=
  (List.range 28).foldl (burnsideF48d_opCoord T y i c w) (Array.replicate 28 0)

@[expose] def burnsideF48d_unit (b : ℕ) : Array ℕ := (Array.replicate 28 0).set! b 1

@[expose] def burnsideF48d_genSpec (k : ℕ) : List (Bool × ℕ × ℕ) :=
  let c := if k = 2 ∨ k = 5 then 1 else if k = 3 ∨ k = 6 then 3 else 9
  let y := decide (5 ≤ k)
  if k = 0 then [(false, 2, 1)] else if k = 1 then [(true, 2, 1)] else
    [(y, 0, c), (y, 1, burnsideF48d_frobC c), (y, 3, burnsideF48d_frobC (burnsideF48d_frobC c))]

@[expose] def burnsideF48d_genCol (T : Array (Array (Array (Array (Option (ℕ × ℤ))))))
    (k b : ℕ) : Array ℕ :=
  (burnsideF48d_genSpec k).foldr (fun op w => burnsideF48d_applyOp T op.1 op.2.1 op.2.2 w)
    (burnsideF48d_unit b)

@[expose] def burnsideF48d_realW (w : Array ℕ) : W :=
  ofV (V.ofFn 154 fun q => if q < 84 then w[q / 3]! / 3 ^ (q % 3) % 3 else 0)

@[expose] def burnsideF48d_rowsOf (cols : Array (Array ℕ)) : Array W :=
  Array.ofFn (n := 154) fun q => if q.val < 84 then
    burnsideF48d_realW ((cols[q.val / 3]!).map
      (burnsideF48d_mulC (burnsideF48d_powC 3 (q.val % 3))))
    else W.zero

@[expose] def burnsideF48d_genRows (T : Array (Array (Array (Array (Option (ℕ × ℤ))))))
    (k : ℕ) : Array W :=
  burnsideF48d_rowsOf ((Array.range 28).map (burnsideF48d_genCol T k))

@[expose] def burnsideF48d_frobRows (_ : Unit := ()) : Array W :=
  Array.ofFn (n := 154) fun q => if q.val < 84 then
    burnsideF48d_realW ((burnsideF48d_unit (q.val / 3)).map fun x =>
      burnsideF48d_frobC (burnsideF48d_mulC (burnsideF48d_powC 3 (q.val % 3)) x))
    else W.zero

abbrev burnsideF48d_N : ℕ := 26572

abbrev burnsideF48d_NK : ℕ := 53144

@[expose] def burnsideF48d_limbs (_ : Unit := ()) : Array ℕ :=
  hexTable 16 (4 * 26572) 0 burnsideF48d_KeysHex

@[expose] def burnsideF48d_keys (_ : Unit := ()) : Array W :=
  let t := burnsideF48d_limbs ()
  Array.ofFn (n := 53144) fun i =>
    let j := i.val / 2
    let w : W := ⟨UInt64.ofNat t[4 * j]!, UInt64.ofNat t[4 * j + 1]!, 0, 0,
      UInt64.ofNat t[4 * j + 2]!, UInt64.ofNat t[4 * j + 3]!, 0, 0⟩
    if i.val % 2 = 0 then w else w.neg

@[expose] def burnsideF48d_tab (k : ℕ) : Table :=
  (hexTable 4 53144 (53144 * k) burnsideF48d_TabsHex).map UInt32.ofNat

@[expose] def burnsideF48d_gen (k : ℕ) : Array ℕ :=
  hexTable 4 26572 (26572 * k) burnsideF48d_GensHex

@[expose] def burnsideF48d_phi (_ : Unit := ()) : Array ℕ :=
  hexTable 4 26572 0 burnsideF48d_PhiHex

@[expose] def burnsideF48d_toT (a : Array ℕ) : Table := a.map UInt32.ofNat

@[expose] def burnsideF48d_rows (T : Array (Array (Array (Array (Option (ℕ × ℤ)))))) (k : ℕ) :
    Array W :=
  if k = 8 then burnsideF48d_frobRows () else burnsideF48d_genRows T k

@[expose] def burnsideF48d_OrbOK (k k' : ℕ) (_ : Unit := ()) : Bool :=
  let T := burnsideF48d_colTab ()
  let keys := burnsideF48d_keys ()
  let index := indexOf keys
  orbitOK 53144 (burnsideF48d_rows T k) (burnsideF48d_rows T k')
    ⟨keys, burnsideF48d_tab k, burnsideF48d_tab k'⟩
    (CFSG.ONSchreier.Native.posOf index 53144) 15

@[expose] def burnsideF48d_low84 (a : W) : Bool :=
  a.p1 >>> 20 == 0 && a.m1 >>> 20 == 0 && a.p2 == 0 && a.m2 == 0 && a.p3 == 0 && a.m3 == 0

@[expose] def burnsideF48d_lowOK (keys : Array W) : Bool :=
  allIn 0 53144 fun i => burnsideF48d_low84 keys[i]!

@[expose] def burnsideF48d_permOK (T : Table) : Bool :=
  let R := invT 26572 T
  T.size == 26572 && allIn 0 26572 fun i => decide (ap T i < 26572) && ap R (ap T i) == i

@[expose] def burnsideF48d_PtsOK (_ : Unit := ()) : Bool :=
  let keys := burnsideF48d_keys ()
  keys.size == 53144 && keys[0]! == burnsideF48d_realW (burnsideF48d_unit 26) &&
    burnsideF48d_lowOK keys &&
    (Nat.all 8 fun k _ =>
      let t := burnsideF48d_tab k
      let g := burnsideF48d_gen k
      t.size == 53144 && g.size == 26572 &&
        Nat.all 26572 fun i _ => (ap t (2 * i)) / 2 == g[i]! && decide (g[i]! < 26572)) &&
    burnsideF48d_permOK (burnsideF48d_toT (burnsideF48d_phi ()))

@[expose] def burnsideF48d_genTabs (_ : Unit := ()) : Array Table :=
  let G := (Array.range 8).map fun k => burnsideF48d_toT (burnsideF48d_gen k)
  Array.ofFn (n := 16) fun l => if l.val % 2 = 0 then G[l.val / 2]! else invT 26572 G[l.val / 2]!

@[expose] def burnsideF48d_GenInvOK (_ : Unit := ()) : Bool :=
  let GT := burnsideF48d_genTabs ()
  GT.size == 16 && allIn 0 8 fun k => invOK 26572 GT[2 * k]! GT[2 * k + 1]!

@[expose] def burnsideF48d_intWord {n : ℕ} (w : List (Fin n × Bool)) : List Int :=
  w.map fun l => if l.2 then ((l.1.val + 1 : ℕ) : Int) else -((l.1.val + 1 : ℕ) : Int)

@[expose] def burnsideF48d_letterT (GT : Array Table) (l : Int) : Table :=
  if 0 < l then GT[2 * (l.toNat - 1)]! else GT[2 * ((-l).toNat - 1) + 1]!

@[expose] def burnsideF48d_letters (_ : Unit := ()) : Array Table :=
  let GT := burnsideF48d_genTabs ()
  let L := burnsideF48d_LW.toArray.map fun w =>
    wordT 26572 (burnsideF48d_letterT GT) (burnsideF48d_intWord w)
  Array.ofFn (n := 34) fun l => if l.val % 2 = 0 then L[l.val / 2]! else invT 26572 L[l.val / 2]!

abbrev burnsideF48d_baseX : Array ℕ := #[0, 26571, 6, 479, 15916, 186, 1, 3]

abbrev burnsideF48d_lvS1 : Array ℕ :=
  #[0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27,
    28, 29, 30, 31, 32, 33]

abbrev burnsideF48d_lvT : Array ℕ := #[4, 5, 6, 7, 8, 9]

@[expose] def burnsideF48d_ChainXOK (_ : Unit := ()) : Bool :=
  let ls := burnsideF48d_letters ()
  let b := burnsideF48d_baseX
  let trees := CFSG.Perm.Native.chainTrees 26572 ls b
  ls.size == 34 && allIn 0 17 (fun j => invOK 26572 ls[2 * j]! ls[2 * j + 1]!) &&
    trees.size == 8 &&
    allIn 0 8 (fun i => CFSG.Perm.Native.treeOK 26572 b[i]! trees[i]! ls
      (CFSG.Perm.Native.levelLetters ls b i)) &&
    CFSG.Perm.Native.orbitSizes trees == [26572, 19683, 28, 1, 27, 1, 2, 26] &&
    CFSG.Perm.Native.levelLetters ls b 1 == burnsideF48d_lvS1 &&
    CFSG.Perm.Native.levelLetters ls b 6 == burnsideF48d_lvT

abbrev burnsideF48d_baseB : Array ℕ := #[6, 26571, 15916, 1, 3]

@[expose] def burnsideF48d_ChainBOK (_ : Unit := ()) : Bool :=
  let ls := (burnsideF48d_letters ()).extract 4 34
  let b := burnsideF48d_baseB
  let trees := CFSG.Perm.Native.chainTrees 26572 ls b
  ls.size == 30 && allIn 0 15 (fun j => invOK 26572 ls[2 * j]! ls[2 * j + 1]!) &&
    trees.size == 5 &&
    allIn 0 5 (fun i => CFSG.Perm.Native.treeOK 26572 b[i]! trees[i]! ls
      (CFSG.Perm.Native.levelLetters ls b i)) &&
    CFSG.Perm.Native.orbitSizes trees == [3, 6561, 27, 2, 26]

abbrev burnsideF48d_lvS2 : Array ℕ :=
  #[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27,
    28, 29, 30, 31, 32, 33]

abbrev burnsideF48d_lvU : Array ℕ :=
  #[10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]

@[inline, expose] def burnsideF48d_inT (T : CFSG.Perm.Native.Tree) (p : ℕ) : Bool :=
  decide (ap T.pos p < T.pts.size)

@[expose] def burnsideF48d_treeOK (ls : Array Table) (root : ℕ) (lv : Array ℕ) (size : ℕ) :
    Bool :=
  let T := CFSG.Perm.Native.treeBFS 26572 root ls lv
  CFSG.Perm.Native.treeOK 26572 root T ls lv && T.pts.size == size

@[expose] def burnsideF48d_TreesOK (_ : Unit := ()) : Bool :=
  let ls := burnsideF48d_letters ()
  burnsideF48d_treeOK ls 6 burnsideF48d_lvS1 84 &&
    burnsideF48d_treeOK ls 479 burnsideF48d_lvS1 6804 &&
    burnsideF48d_treeOK ls 0 burnsideF48d_lvS2 4 &&
    burnsideF48d_treeOK ls 6 burnsideF48d_lvU 3 &&
    burnsideF48d_treeOK ls 3 burnsideF48d_lvU 81 &&
    burnsideF48d_treeOK ls 10 burnsideF48d_lvU 243 &&
    burnsideF48d_treeOK ls 50 burnsideF48d_lvU 6561 &&
    burnsideF48d_treeOK ls 167 burnsideF48d_lvU 19683

abbrev burnsideF48d_apt : List ℕ := [0, 6, 479, 26571, 15916, 186]

@[expose] def burnsideF48d_PointsOK (_ : Unit := ()) : Bool :=
  let ls := burnsideF48d_letters ()
  let T84 := CFSG.Perm.Native.treeBFS 26572 6 ls burnsideF48d_lvS1
  let T6804 := CFSG.Perm.Native.treeBFS 26572 479 ls burnsideF48d_lvS1
  let T19683 := CFSG.Perm.Native.treeBFS 26572 26571 ls burnsideF48d_lvS1
  let Tl := CFSG.Perm.Native.treeBFS 26572 0 ls burnsideF48d_lvS2
  let U1 := CFSG.Perm.Native.treeBFS 26572 3 ls burnsideF48d_lvU
  let U2 := CFSG.Perm.Native.treeBFS 26572 10 ls burnsideF48d_lvU
  let U3 := CFSG.Perm.Native.treeBFS 26572 50 ls burnsideF48d_lvU
  let U4 := CFSG.Perm.Native.treeBFS 26572 167 ls burnsideF48d_lvU
  let ta := ls[4]!
  let tb := ls[6]!
  allIn 0 26572 (fun p => burnsideF48d_apt.contains p || ap ta p != p || ap tb p != p) &&
    allIn 0 26572 (fun p => burnsideF48d_inT Tl p || burnsideF48d_inT U1 p ||
      burnsideF48d_inT U2 p || burnsideF48d_inT U3 p || burnsideF48d_inT U4 p) &&
    burnsideF48d_inT T84 6 && burnsideF48d_inT T84 186 && !burnsideF48d_inT T84 0 &&
    !burnsideF48d_inT T84 479 && !burnsideF48d_inT T84 26571 && !burnsideF48d_inT T84 15916 &&
    burnsideF48d_inT T6804 479 && burnsideF48d_inT T6804 15916 &&
    !burnsideF48d_inT T19683 0 && !burnsideF48d_inT T19683 6 && !burnsideF48d_inT T19683 479 &&
    !burnsideF48d_inT T19683 15916 && !burnsideF48d_inT T19683 186 &&
    burnsideF48d_inT Tl 6 && !burnsideF48d_inT Tl 479 && !burnsideF48d_inT Tl 26571 &&
    !burnsideF48d_inT Tl 15916 && !burnsideF48d_inT Tl 186 &&
    ap ls[0]! 6 == 186 && ap ls[2]! 0 == 6 && ap ls[2]! 6 == 0 && ap ls[2]! 186 == 479 &&
    ap ls[2]! 26571 == 15916

@[expose] def burnsideF48d_evPt {n : ℕ} (ls : Array Table) (w : List (Fin n × Bool)) (p : ℕ) : ℕ :=
  w.foldr (fun l q => ap ls[2 * l.1.val + (if l.2 then 0 else 1)]! q) p

@[expose] def burnsideF48d_KW : List (List (Fin 17 × Bool)) :=
  (List.range 2).flatMap fun j => (List.range 26).map fun i =>
    List.replicate i ((2 : Fin 17), true) ++ List.replicate j ((3 : Fin 17), true)

@[expose] def burnsideF48d_RelOK (_ : Unit := ()) : Bool :=
  let ls := burnsideF48d_letters ()
  let b := burnsideF48d_baseX
  ((burnsideF48d_R1 ++ burnsideF48d_R2 ++
      [(List.replicate 6 [((0 : Fin 17), true), ((1 : Fin 17), true)]).flatten]).all
    fun r => b.all fun p => burnsideF48d_evPt ls r p == p) &&
  (burnsideF48d_KW.tail.all fun c => b.any fun p =>
    burnsideF48d_evPt ls ([((0 : Fin 17), true), ((1 : Fin 17), true)] ++ c) p !=
      burnsideF48d_evPt ls (c ++ [((0 : Fin 17), true), ((1 : Fin 17), true)]) p)

end CFSG.ASVolI
