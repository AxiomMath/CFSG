module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCCoordCore
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNA6DataM10

public section

namespace CFSG.LocalAnalysis.WeakClosure81.CoordA6.M10CData

open CFSG.QuasithinUnique.A6Facts.Core CFSG.LocalAnalysis.WeakClosure81.NFA6.Core
  CFSG.LocalAnalysis.WeakClosure81.CoordA6.Core

set_option maxRecDepth 100000

@[expose] def H0K : SubData where
  gc := [[2, 1, 9, 7, 8, 3, 4, 5, 6, 0], [0, 1, 9, 4, 3, 8, 7, 6, 5, 2]]
  tree := [(0, 0), (0, 1), (1, 0), (1, 1), (2, 0)]
  tbl := [[1, 2], [3, 4], [5, 0], [0, 5], [2, 1], [4, 3]]
  lit := [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
      [2, 1, 9, 7, 8, 3, 4, 5, 6, 0],
      [0, 1, 9, 4, 3, 8, 7, 6, 5, 2],
      [9, 1, 0, 5, 6, 7, 8, 3, 4, 2],
      [2, 1, 0, 8, 7, 6, 5, 4, 3, 9],
      [9, 1, 2, 6, 5, 4, 3, 8, 7, 0]]

@[expose] def H0N2 : SubData where
  gc := [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]]
  tree := []
  tbl := [[0]]
  lit := [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]]

@[expose] def H0Np : SubData where
  gc := [[9, 1, 0, 5, 6, 7, 8, 3, 4, 2]]
  tree := [(0, 0), (1, 0)]
  tbl := [[1], [2], [0]]
  lit := [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
      [9, 1, 0, 5, 6, 7, 8, 3, 4, 2],
      [2, 1, 9, 7, 8, 3, 4, 5, 6, 0]]

@[expose] def H0 : KData where
  K := H0K
  N2 := H0N2
  Np := H0Np
  y := [2, 1, 9, 7, 8, 3, 4, 5, 6, 0]
  p := 3

@[expose] def Hs : List KData := [NFA6.M10Data.K0]

@[expose] def ms : List MovW := [
  ⟨0, [0, 2, 1, 6, 8, 7, 3, 5, 4, 9], 2, 2, []⟩,
  ⟨0, [0, 2, 1, 6, 8, 7, 3, 5, 4, 9], 2, 2, []⟩,
  ⟨0, [0, 2, 1, 6, 8, 7, 3, 5, 4, 9], 2, 2, []⟩,
  ⟨0, [0, 2, 1, 6, 8, 7, 3, 5, 4, 9], 2, 2, []⟩,
  ⟨0, [0, 2, 1, 6, 8, 7, 3, 5, 4, 9], 2, 2, []⟩,
  ⟨0, [0, 2, 1, 6, 8, 7, 3, 5, 4, 9], 2, 2, []⟩,
  ⟨0, [0, 2, 1, 6, 8, 7, 3, 5, 4, 9], 2, 2, []⟩,
  ⟨0, [0, 2, 1, 6, 8, 7, 3, 5, 4, 9], 2, 2, []⟩]

@[expose] def Ks : List KData := [NFA6.M10Data.K0, NFA6.M10Data.K1, H0]

@[expose] def fs : List (Option FixW) := [
  none,
  some ⟨2, [9, 1, 2, 6, 5, 4, 3, 8, 7, 0], [2, 1, 9, 7, 8, 3, 4, 5, 6, 0],
    [2, 1, 0, 8, 7, 6, 5, 4, 3, 9], 1, []⟩,
  some ⟨1, [3, 2, 1, 0, 5, 4, 9, 7, 8, 6], [0, 6, 3, 1, 7, 4, 2, 8, 5, 9],
    [1, 0, 9, 6, 7, 5, 3, 4, 8, 2], 1, []⟩,
  some ⟨0, [9, 2, 1, 3, 7, 8, 6, 4, 5, 0], [0, 7, 8, 9, 5, 4, 6, 1, 2, 3],
    [3, 5, 4, 0, 2, 1, 6, 8, 7, 9], 1, []⟩,
  some ⟨1, [6, 2, 1, 9, 4, 5, 0, 8, 7, 3], [0, 6, 3, 1, 7, 4, 2, 8, 5, 9],
    [2, 9, 0, 6, 4, 8, 3, 7, 5, 1], 1, []⟩,
  some ⟨0, [0, 2, 1, 6, 8, 7, 3, 5, 4, 9], [0, 7, 8, 9, 5, 4, 6, 1, 2, 3],
    [0, 4, 5, 3, 1, 2, 9, 8, 7, 6], 1, []⟩,
  some ⟨0, [0, 2, 1, 6, 8, 7, 3, 5, 4, 9], [0, 7, 8, 9, 5, 4, 6, 1, 2, 3],
    [0, 4, 5, 3, 1, 2, 9, 8, 7, 6], 1, []⟩,
  some ⟨1, [3, 2, 1, 0, 5, 4, 9, 7, 8, 6], [0, 6, 3, 1, 7, 4, 2, 8, 5, 9],
    [1, 0, 9, 6, 7, 5, 3, 4, 8, 2], 1, []⟩]

@[expose] def pc : List PairC := [
  ⟨[9, 1, 2, 6, 5, 4, 3, 8, 7, 0], [1, 7, 4, 2, 8, 5, 0, 6, 3, 9], [0, 6, 3, 1, 7, 4, 2, 8, 5, 9],
    [9, 2, 1, 3, 7, 8, 6, 4, 5, 0], [3, 2, 1, 0, 5, 4, 9, 7, 8, 6]⟩]

theorem H0_ok : H0.check NFA6.M10Data.T = true := by decide +kernel

theorem Hs_ok : ∀ D ∈ Hs, D.check NFA6.M10Data.T = true := by
  intro D hD
  simp only [Hs, List.mem_cons, List.not_mem_nil, or_false] at hD
  subst hD
  exact NFA6.M10Data.K0_ok

theorem Ks_ok : ∀ D ∈ Ks, D.check NFA6.M10Data.T = true := by
  intro D hD
  simp only [Ks, List.mem_cons, List.not_mem_nil, or_false] at hD
  rcases hD with rfl | rfl | rfl
  · exact NFA6.M10Data.K0_ok
  · exact NFA6.M10Data.K1_ok
  · exact H0_ok

theorem Hs_gens : Hs.all (fun D => D.K.gc.all pslLit.contains) = true := by decide +kernel

theorem Ks_gens : Ks.all (fun D => D.K.gc.all
    (pslLit ++ pslLit.map (fun c => cmul c [0, 4, 8, 7, 2, 3, 5, 6, 1, 9])).contains) = true := by
  decide +kernel

theorem mov_ok :
    movAll NFA6.M10Data.T Hs (eList NFA6.M10Data.T (NFA6.M10Data.Es.map Entry.E)) ms = true := by
  decide +kernel

theorem fix_ok : fixAll NFA6.M10Data.T Ks (eList NFA6.M10Data.T (NFA6.M10Data.Es.map Entry.E))
    fs [cid] = true := by
  decide +kernel

theorem pc_ok : pairCCheck NFA6.M10Data.T pslLit pc = true := by decide +kernel

theorem sq_ok :
    (NFA6.M10Data.T.filter pslLit.contains).any (fun c => cmul c c != cid) = true := by
  decide +kernel

end CFSG.LocalAnalysis.WeakClosure81.CoordA6.M10CData
