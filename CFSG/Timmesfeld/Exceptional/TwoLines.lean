module

public import CFSG.Timmesfeld.Exceptional.TwoLinesCheck192
public import CFSG.Timmesfeld.Exceptional.TwoLinesCheckTriv
public import CFSG.Timmesfeld.Exceptional.TwoLinesCheck168
public import CFSG.Timmesfeld.Exceptional.TwoLinesCheck1080
public import CFSG.Certificates.WordPresentation
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Timmesfeld.Exceptional.CosetWalk

public section

namespace CFSG.Timmesfeld.Moufang

open CFSG.Certificates CFSG.Certificates.CosetEnumeration

variable {G : Type*} [Group G] {D : Set G}

namespace TwoLines

@[expose] def wP : List (Fin 3 × Bool) := [(0, true), (1, true), (0, true), (1, true)]

@[expose] def wD : List (Fin 3 × Bool) :=
  [(2, true), (0, true), (1, true), (2, true)] ++ wP ++ [(2, true), (1, true), (0, true), (2, true)]

@[expose] def wPC : List (Fin 3 × Bool) := wP ++ [(2, true)]

@[expose] def relsW : List (List (Fin 3 × Bool)) :=
  [[(0, true), (0, true)], [(1, true), (1, true)], [(2, true), (2, true)],
    (List.replicate 4 [(0, true), (1, true)]).flatten,
    (List.replicate 3 [(0, true), (2, true)]).flatten,
    (List.replicate 3 [(1, true), (2, true)]).flatten]

@[expose] def relsA : List (List (Fin 3 × Bool)) := relsW ++ [wD ++ wP]

@[expose] def relsB : List (List (Fin 3 × Bool)) := relsW ++ [wD ++ wP ++ [(0, true)]]

@[expose] def relsD : List (List (Fin 3 × Bool)) :=
  relsW ++ [wP ++ wD ++ (wP ++ wD) ++ [(0, true)]]

@[expose] def relsD1 : List (List (Fin 3 × Bool)) :=
  relsD ++ [(List.replicate 4 (wD ++ [(2, true)])).flatten]

@[expose] def relsD2 : List (List (Fin 3 × Bool)) :=
  relsD ++ [(List.replicate 4 ([(0, true)] ++ wD ++ [(2, true)])).flatten]

theorem mk_eq_one_A (w : List (Fin 3 × Bool))
    (hwalk : Exc.coverWalk (2 * 3) Data192.fx Data192.fy Data192.ffi 0 (w.map letterCode) = 0) :
    PresentedGroup.mk (wordRels relsA) (FreeGroup.mk w) = 1 :=
  Exc.mk_eq_one_of_coverWalk (N := 192) (F := 576) (fx := Data192.fx) (fc := Data192.fc)
    (fy := Data192.fy) (kind := Data192.kind) (wi := Data192.wi) (fs := Data192.fs)
    (ft := Data192.ft) (fo := Data192.fo) (refs := Data192.refs) (pl := Data192.pl)
    (ffi := Data192.ffi) (live := Data192.live) (rels := wordRels relsA) relsA Data192.words
    (fun w hw => ⟨w, hw, rfl⟩) (by decide +kernel) Data192.live_zero (by norm_num)
    Data192.facts_all Data192.cover_all w hwalk

theorem mk_eq_one_B (w : List (Fin 3 × Bool))
    (hwalk : Exc.coverWalk (2 * 3) DataTriv.fx DataTriv.fy DataTriv.ffi 0 (w.map letterCode) =
      0) :
    PresentedGroup.mk (wordRels relsB) (FreeGroup.mk w) = 1 :=
  Exc.mk_eq_one_of_coverWalk (N := 109) (F := 394) (fx := DataTriv.fx) (fc := DataTriv.fc)
    (fy := DataTriv.fy) (kind := DataTriv.kind) (wi := DataTriv.wi) (fs := DataTriv.fs)
    (ft := DataTriv.ft) (fo := DataTriv.fo) (refs := DataTriv.refs) (pl := DataTriv.pl)
    (ffi := DataTriv.ffi) (live := DataTriv.live) (rels := wordRels relsB) relsB DataTriv.words
    (fun w hw => ⟨w, hw, rfl⟩) (by decide +kernel) DataTriv.live_zero (by norm_num)
    DataTriv.facts_all DataTriv.cover_all w hwalk

theorem mk_eq_one_D1 (w : List (Fin 3 × Bool))
    (hwalk : Exc.coverWalk (2 * 3) Data168.fx Data168.fy Data168.ffi 0 (w.map letterCode) = 0) :
    PresentedGroup.mk (wordRels relsD1) (FreeGroup.mk w) = 1 :=
  Exc.mk_eq_one_of_coverWalk (N := 2027) (F := 6256) (fx := Data168.fx) (fc := Data168.fc)
    (fy := Data168.fy) (kind := Data168.kind) (wi := Data168.wi) (fs := Data168.fs)
    (ft := Data168.ft) (fo := Data168.fo) (refs := Data168.refs) (pl := Data168.pl)
    (ffi := Data168.ffi) (live := Data168.live) (rels := wordRels relsD1) relsD1 Data168.words
    (fun w hw => ⟨w, hw, rfl⟩) (by decide +kernel) Data168.live_zero (by norm_num)
    Data168.facts_all Data168.cover_all w hwalk

theorem mk_eq_one_D2 (w : List (Fin 3 × Bool))
    (hwalk : Exc.coverWalk (2 * 3) Data1080.fx Data1080.fy Data1080.ffi 0 (w.map letterCode) =
      0) :
    PresentedGroup.mk (wordRels relsD2) (FreeGroup.mk w) = 1 :=
  Exc.mk_eq_one_of_coverWalk (N := 3218) (F := 10305) (fx := Data1080.fx) (fc := Data1080.fc)
    (fy := Data1080.fy) (kind := Data1080.kind) (wi := Data1080.wi) (fs := Data1080.fs)
    (ft := Data1080.ft) (fo := Data1080.fo) (refs := Data1080.refs) (pl := Data1080.pl)
    (ffi := Data1080.ffi) (live := Data1080.live) (rels := wordRels relsD2) relsD2
    Data1080.words (fun w hw => ⟨w, hw, rfl⟩) (by decide +kernel) Data1080.live_zero
    (by norm_num) Data1080.facts_all Data1080.cover_all w hwalk

theorem mk_A :
    PresentedGroup.mk (wordRels relsA) (FreeGroup.mk (List.replicate 4 wPC).flatten) = 1 :=
  mk_eq_one_A _ (by decide +kernel)

theorem mk_B : PresentedGroup.mk (wordRels relsB) (FreeGroup.mk [(0, true)]) = 1 :=
  mk_eq_one_B _ (by decide +kernel)

theorem mk_D1 :
    PresentedGroup.mk (wordRels relsD1) (FreeGroup.mk (List.replicate 3 wPC).flatten) = 1 :=
  mk_eq_one_D1 _ (by decide +kernel)

theorem mk_D2 :
    PresentedGroup.mk (wordRels relsD2) (FreeGroup.mk (List.replicate 5 wPC).flatten) = 1 :=
  mk_eq_one_D2 _ (by decide +kernel)

theorem signedProd_wP (x : Fin 3 → G) : signedProd x wP = (x 0 * x 1) ^ 2 := by
  simp [signedProd, wP, pow_two, mul_assoc]

theorem signedProd_wD (x : Fin 3 → G) :
    signedProd x wD = x 2 * x 0 * x 1 * x 2 * (x 0 * x 1) ^ 2 * (x 2 * x 1 * x 0 * x 2) := by
  rw [wD, signedProd_append, signedProd_append, signedProd_wP]
  simp [signedProd, mul_assoc]

theorem signedProd_wPC (x : Fin 3 → G) : signedProd x wPC = (x 0 * x 1) ^ 2 * x 2 := by
  rw [wPC, signedProd_append, signedProd_wP]
  simp [signedProd]

theorem relsW_eq_one {x : Fin 3 → G} (h0 : x 0 * x 0 = 1) (h1 : x 1 * x 1 = 1)
    (h2 : x 2 * x 2 = 1) (h01 : (x 0 * x 1) ^ 4 = 1) (h02 : (x 0 * x 2) ^ 3 = 1)
    (h12 : (x 1 * x 2) ^ 3 = 1) : ∀ r ∈ relsW, signedProd x r = 1 := by
  intro r hr
  simp only [relsW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [signedProd] using h0
  · simpa [signedProd] using h1
  · simpa [signedProd] using h2
  · rw [signedProd_replicate]; simpa [signedProd] using h01
  · rw [signedProd_replicate]; simpa [signedProd] using h02
  · rw [signedProd_replicate]; simpa [signedProd] using h12

theorem orderOf_ne_one_of_not_commute {p c : G} (hpc : ¬ Commute p c) :
    orderOf (p * c) ≠ 1 := by
  intro h
  rw [orderOf_eq_one_iff] at h
  apply hpc
  rw [eq_inv_of_mul_eq_one_right h]
  exact (Commute.refl p).inv_right

end TwoLines

open TwoLines

end CFSG.Timmesfeld.Moufang
