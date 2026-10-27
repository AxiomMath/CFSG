module

public import CFSG.Milestones.ASVolI.F48.D43.Inputs

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.Th.Native

set_option compiler.extract_closed false

@[noinline, expose] def burnsideF48d_pairsOK (GT : Array Table) (m : ℕ) : Bool :=
  GT.size == 2 * m && allIn 0 m fun k => invOK 26572 GT[2 * k]! GT[2 * k + 1]!

@[noinline, expose] def burnsideF48d_chainCheck (ls : Array Table) (b : Array ℕ)
    (trees : Array CFSG.Perm.Native.Tree) (sizes : List ℕ) : Bool :=
  trees.size == b.size &&
    allIn 0 b.size (fun i => CFSG.Perm.Native.treeOK 26572 b[i]! trees[i]! ls
      (CFSG.Perm.Native.levelLetters ls b i)) &&
    CFSG.Perm.Native.orbitSizes trees == sizes

@[noinline, expose] def burnsideF48d_chainXCheck (ls : Array Table) : Bool :=
  burnsideF48d_pairsOK ls 17 &&
    burnsideF48d_chainCheck ls burnsideF48d_baseX
      (CFSG.Perm.Native.chainTrees 26572 ls burnsideF48d_baseX)
      [26572, 19683, 28, 1, 27, 1, 2, 26] &&
    CFSG.Perm.Native.levelLetters ls burnsideF48d_baseX 1 == burnsideF48d_lvS1 &&
    CFSG.Perm.Native.levelLetters ls burnsideF48d_baseX 6 == burnsideF48d_lvT

@[expose] def burnsideF48d_XChainOK (_ : Unit := ()) : Bool :=
  burnsideF48d_chainXCheck (burnsideF48d_letters ())

@[noinline, expose] def burnsideF48d_chainBCheck (ls : Array Table) : Bool :=
  burnsideF48d_pairsOK ls 15 &&
    burnsideF48d_chainCheck ls burnsideF48d_baseB
      (CFSG.Perm.Native.chainTrees 26572 ls burnsideF48d_baseB) [3, 6561, 27, 2, 26]

@[expose] def burnsideF48d_BChainOK (_ : Unit := ()) : Bool :=
  burnsideF48d_chainBCheck ((burnsideF48d_letters ()).extract 4 34)

@[inline, expose] def burnsideF48d_memT (T : CFSG.Perm.Native.Tree) (p : ℕ) : Bool :=
  decide (ap T.pos p < T.pts.size) && ap T.pts (ap T.pos p) == p

@[noinline, expose] def burnsideF48d_tree (ls : Array Table) (root : ℕ) (lv : Array ℕ) :
    CFSG.Perm.Native.Tree :=
  CFSG.Perm.Native.treeBFS 26572 root ls lv

@[inline, expose] def burnsideF48d_vtree (ls : Array Table) (root : ℕ) (lv : Array ℕ) (size : ℕ)
    (T : CFSG.Perm.Native.Tree) : Bool :=
  CFSG.Perm.Native.treeOK 26572 root T ls lv && T.pts.size == size

abbrev burnsideF48d_lineL : List ℕ := [0, 1, 2, 6]

@[noinline, expose] def burnsideF48d_orbCheck (ls : Array Table)
    (A6 A479 A26571 L0 U6 U186 U479 U15916 U26571 L186 L26571 : CFSG.Perm.Native.Tree) : Bool :=
  burnsideF48d_vtree ls 6 burnsideF48d_lvS1 84 A6 &&
    burnsideF48d_vtree ls 479 burnsideF48d_lvS1 6804 A479 &&
    burnsideF48d_vtree ls 26571 burnsideF48d_lvS1 19683 A26571 &&
    burnsideF48d_vtree ls 0 burnsideF48d_lvS2 4 L0 &&
    burnsideF48d_vtree ls 6 burnsideF48d_lvU 3 U6 &&
    burnsideF48d_vtree ls 186 burnsideF48d_lvU 81 U186 &&
    burnsideF48d_vtree ls 479 burnsideF48d_lvU 243 U479 &&
    burnsideF48d_vtree ls 15916 burnsideF48d_lvU 6561 U15916 &&
    burnsideF48d_vtree ls 26571 burnsideF48d_lvU 19683 U26571 &&
    allIn 1 26572 (fun p => burnsideF48d_memT A6 p || burnsideF48d_memT A479 p ||
      burnsideF48d_memT A26571 p) &&
    allIn 1 26572 (fun p => burnsideF48d_memT U6 p || burnsideF48d_memT U186 p ||
      burnsideF48d_memT U479 p || burnsideF48d_memT U15916 p || burnsideF48d_memT U26571 p) &&
    burnsideF48d_memT A6 186 && burnsideF48d_memT A479 15916 &&
    burnsideF48d_memT L0 1 && burnsideF48d_memT L0 2 && burnsideF48d_memT L0 6 &&
    burnsideF48d_memT U6 1 && burnsideF48d_memT U6 2 &&
    burnsideF48d_vtree ls 186 burnsideF48d_lvS2 324 L186 &&
    burnsideF48d_vtree ls 26571 burnsideF48d_lvS2 26244 L26571 &&
    allIn 0 26572 (fun p => burnsideF48d_memT L0 p || burnsideF48d_memT L186 p ||
      burnsideF48d_memT L26571 p)

@[noinline, expose] def burnsideF48d_ptCheck (ls : Array Table) : Bool :=
  allIn 0 26572 (fun p => burnsideF48d_apt.contains p || ap ls[4]! p != p || ap ls[6]! p != p) &&
    burnsideF48d_lvS2.all (fun t => burnsideF48d_lineL.all fun p =>
      burnsideF48d_lineL.contains (ap ls[t]! p)) &&
    burnsideF48d_apt.map (ap ls[0]!) == [0, 186, 15916, 26571, 479, 6] &&
    burnsideF48d_apt.map (ap ls[2]!) == [6, 0, 186, 15916, 26571, 479]

@[expose] def burnsideF48d_OrbsOK (_ : Unit := ()) : Bool :=
  let ls := burnsideF48d_letters ()
  burnsideF48d_orbCheck ls (burnsideF48d_tree ls 6 burnsideF48d_lvS1)
      (burnsideF48d_tree ls 479 burnsideF48d_lvS1) (burnsideF48d_tree ls 26571 burnsideF48d_lvS1)
      (burnsideF48d_tree ls 0 burnsideF48d_lvS2) (burnsideF48d_tree ls 6 burnsideF48d_lvU)
      (burnsideF48d_tree ls 186 burnsideF48d_lvU) (burnsideF48d_tree ls 479 burnsideF48d_lvU)
      (burnsideF48d_tree ls 15916 burnsideF48d_lvU) (burnsideF48d_tree ls 26571 burnsideF48d_lvU)
      (burnsideF48d_tree ls 186 burnsideF48d_lvS2) (burnsideF48d_tree ls 26571 burnsideF48d_lvS2) &&
    burnsideF48d_ptCheck ls

@[expose] def burnsideF48d_baseImg {n : ℕ} (ls : Array Table) (w : List (Fin n × Bool)) :
    List ℕ :=
  burnsideF48d_baseX.toList.map (burnsideF48d_evPt ls w)

abbrev burnsideF48d_xyW : List (Fin 17 × Bool) := [((0 : Fin 17), true), ((1 : Fin 17), true)]

abbrev burnsideF48d_w0W : List (Fin 17 × Bool) :=
  [(1, true), (0, true), (1, true), (0, true), (1, true), (0, true)]

abbrev burnsideF48d_W1 : List (Fin 17 × Bool) :=
  [(5, true)] ++ burnsideF48d_w0W ++ [(5, true)] ++
    [(0, false), (1, false), (0, false), (1, false), (0, false), (1, false)] ++ [(5, true), (0, false)]

abbrev burnsideF48d_W2 : List (Fin 17 × Bool) :=
  [(5, true), (0, true), (1, true), (0, true), (12, true), (0, false), (1, false), (0, false),
    (5, true), (0, false)]

@[noinline, expose] def burnsideF48d_relCheck (ls : Array Table) : Bool :=
  ((burnsideF48d_R1 ++ burnsideF48d_R2 ++
      [(List.replicate 6 burnsideF48d_xyW).flatten, burnsideF48d_W1, burnsideF48d_W2]).all
    fun r => burnsideF48d_baseImg ls r == burnsideF48d_baseX.toList) &&
  (burnsideF48d_KW.map (burnsideF48d_baseImg ls)).Nodup &&
  burnsideF48d_KW.tail.all fun c =>
    burnsideF48d_baseImg ls (burnsideF48d_xyW ++ c) != burnsideF48d_baseImg ls (c ++ burnsideF48d_xyW)

@[expose] def burnsideF48d_RelsOK (_ : Unit := ()) : Bool :=
  burnsideF48d_relCheck (burnsideF48d_letters ())

end CFSG.ASVolI
