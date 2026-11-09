module

public import Init

public section

namespace CFSG.KC.IdxAll

theorem all_range_get1 (a : Array Nat) (n : Nat) (ha : a.size = n) (f : Nat → Nat → Bool) :
    (List.range n).all (fun x => f x a[x]!) = a.toList.zipIdx.all (fun p => f p.2 p.1) := by
  subst ha
  have e : a.toList.zipIdx = (List.range a.size).map fun x => (a[x]!, x) := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_zipIdx, List.getElem_map, List.getElem_range, Array.getElem_toList]
      have hi : i < a.size := by simpa using h2
      rw [getElem!_pos a i hi]
      simp
  rw [e, List.all_map]
  rfl

theorem all_range_get2 (a b : Array Nat) (n : Nat) (ha : a.size = n) (hb : b.size = n)
    (f : Nat → Nat → Nat → Bool) :
    (List.range n).all (fun x => f x a[x]! b[x]!) =
      (a.toList.zip b.toList).zipIdx.all (fun p => f p.2 p.1.1 p.1.2) := by
  subst ha
  have e : (a.toList.zip b.toList).zipIdx = (List.range a.size).map fun x => ((a[x]!, b[x]!), x) := by
    apply List.ext_getElem
    · simp [hb]
    · intro i h1 h2
      simp only [List.getElem_zipIdx, List.getElem_map, List.getElem_range, List.getElem_zip,
        Array.getElem_toList]
      have hi : i < a.size := by simpa using h2
      rw [getElem!_pos a i hi, getElem!_pos b i (hb ▸ hi)]
      simp
  rw [e, List.all_map]
  rfl

end CFSG.KC.IdxAll

end
