module

public import CFSG.Monster.AxisCount.CertBasic
public import Certificates.Data.CFSGNative.MonsterAxis.Cover

public section

namespace CertificateChecks.KernelAP

open CFSG.Monster.AxisCount.Native CFSG.Monster.AxisCount.Cert

theorem getElem!_append_ite {α : Type} [Inhabited α] (a b : Array α) (k : Nat) :
    (a ++ b)[k]! = if k < a.size then a[k]! else b[k - a.size]! := by
  split
  · rename_i h
    rw [getElem!_pos (a ++ b) k (by simp; omega), getElem!_pos a k h, Array.getElem_append_left h]
  · rename_i h
    by_cases hb : k - a.size < b.size
    · rw [getElem!_pos (a ++ b) k (by simp; omega), getElem!_pos b _ hb,
        Array.getElem_append_right (by omega)]
    · rw [getElem!_neg (a ++ b) k (by simp; omega), getElem!_neg b _ hb]

@[expose] def plArr (k : Nat) : Array Nat :=
  if k < 1100 then
    if k < 1000 then
      if k < 900 then
        if k < 800 then
          if k < 700 then
            if k < 600 then
              if k < 500 then
                if k < 400 then
                  if k < 300 then
                    if k < 200 then
                      if k < 100 then permChunk0[k]! else permChunk1[k - 100]!
                    else permChunk2[k - 200]!
                  else permChunk3[k - 300]!
                else permChunk4[k - 400]!
              else permChunk5[k - 500]!
            else permChunk6[k - 600]!
          else permChunk7[k - 700]!
        else permChunk8[k - 800]!
      else permChunk9[k - 900]!
    else permChunk10[k - 1000]!
  else permChunk11[k - 1100]!

theorem pl_eq (k : Nat) : pl k = .perm (plArr k) := by
  have s0 : permChunk0.size = 100 := rfl
  have s1 : permChunk1.size = 100 := rfl
  have s2 : permChunk2.size = 100 := rfl
  have s3 : permChunk3.size = 100 := rfl
  have s4 : permChunk4.size = 100 := rfl
  have s5 : permChunk5.size = 100 := rfl
  have s6 : permChunk6.size = 100 := rfl
  have s7 : permChunk7.size = 100 := rfl
  have s8 : permChunk8.size = 100 := rfl
  have s9 : permChunk9.size = 100 := rfl
  have s10 : permChunk10.size = 100 := rfl
  simp only [pl, permTab, plArr, getElem!_append_ite, Array.size_append, s0, s1, s2, s3, s4, s5,
    s6, s7, s8, s9, s10, Nat.reduceAdd]

@[expose] def foldRows (ms : List (Array Nat)) (v : Nat) : Nat :=
  ms.foldl (fun v m => Cover.actRows m v) v

@[expose] def rowsOf (ms : List (Array Nat)) : Array Nat :=
  Array.ofFn (n := 24) fun j => foldRows ms ((1 : Nat) <<< j.val)

theorem wordRows_eq {w : List Gen} {ms : List (Array Nat)} (h : w.map Gen.l2Rows = ms) :
    Cover.wordRows w = rowsOf ms := by
  subst h
  rfl

theorem l2Word_eq {w : List Gen} {ms : List (Array Nat)} (h : w.map Gen.l2Rows = ms) (v : Nat) :
    Cover.l2Word w v = foldRows ms v := by
  subst h
  rfl

theorem map_nil : ([] : List Gen).map Gen.l2Rows = [] := rfl

theorem map_cons {g : Gen} {w : List Gen} {m : Array Nat} {ms : List (Array Nat)}
    (h₁ : g.l2Rows = m) (h₂ : w.map Gen.l2Rows = ms) : (g :: w).map Gen.l2Rows = m :: ms := by
  rw [List.map_cons, h₁, h₂]

theorem all_nil : ([] : List Gen).all Gen.isVis = true := rfl

theorem all_cons {g : Gen} {w : List Gen} (h₁ : g.isVis = true) (h₂ : w.all Gen.isVis = true) :
    (g :: w).all Gen.isVis = true := by
  rw [List.all_cons, h₁, h₂]
  rfl

@[expose] def WordM (w : List Gen) (ms : List (Array Nat)) : Prop :=
  w.map Gen.l2Rows = ms ∧ w.all Gen.isVis = true

theorem WordM.of {w : List Gen} {ms : List (Array Nat)} (h₁ : w.map Gen.l2Rows = ms)
    (h₂ : w.all Gen.isVis = true) : WordM w ms :=
  ⟨h₁, h₂⟩

theorem rows_of_toList {a : Array Nat} {l : List Nat} (h : (a.toList == l) = true) :
    a = l.toArray :=
  Array.ext' (by rw [eq_of_beq h])

theorem l2Rows_pl {k : Nat} {l : List Nat} (h : ((Gen.perm (plArr k)).l2Rows.toList == l) = true) :
    (pl k).l2Rows = l.toArray := by
  rw [pl_eq]
  exact rows_of_toList h

theorem isVis_pl {k : Nat} (h : (Gen.perm (plArr k)).isVis = true) : (pl k).isVis = true := by
  rw [pl_eq]
  exact h

theorem l2Rows_of {g : Gen} {l : List Nat} (h : (g.l2Rows.toList == l) = true) :
    g.l2Rows = l.toArray :=
  rows_of_toList h

theorem l2Rows_rho {q₀ : Bool × Nat × Nat} {l : List Nat}
    (h : ((Gen.rho q₀).l2Rows.toList == l) = true) (q : Bool × Nat × Nat) :
    (Gen.rho q).l2Rows = l.toArray :=
  rows_of_toList (a := (Gen.rho q₀).l2Rows) h

theorem isVis_sign (a : Nat) : (Gen.sign a).isVis = true := rfl

theorem isVis_rho (q : Bool × Nat × Nat) : (Gen.rho q).isVis = true := rfl

theorem isVis_xi : Gen.xi.isVis = true := rfl

theorem wordRows_check {w : List Gen} {ms : List (Array Nat)} {r : List Nat}
    (h : w.map Gen.l2Rows = ms) (hc : (rowsOf ms == r.toArray) = true) :
    (Cover.wordRows w == r.toArray) = true := by
  rw [wordRows_eq h]
  exact hc

theorem l2Word_check {w : List Gen} {ms : List (Array Nat)} {v t : Nat}
    (h : w.map Gen.l2Rows = ms) (hc : (foldRows ms v == t) = true) :
    (Cover.l2Word w v == t) = true := by
  rw [l2Word_eq h]
  exact hc

end CertificateChecks.KernelAP

end
