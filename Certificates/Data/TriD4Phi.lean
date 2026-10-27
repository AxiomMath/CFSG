module

public import Certificates.Data.TriD4TwoRow
public import CFSG.Monster.B.Co2.PermArr

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434D42

open CFSG.Monster.B.Co2 CFSG.StandardType.TriD4TwoRow

@[expose] noncomputable def d4Phi : Equiv.Perm (Fin 2457) := permOfArr 2457 (phiArr ())

theorem foldl_insert_get_of_ne (f : ℕ → ℕ) {k : ℕ} :
    ∀ (l : List ℕ) (m : Std.HashMap ℕ ℕ), (∀ i ∈ l, f i ≠ k) →
      (l.foldl (fun m i => m.insert (f i) i) m)[k]? = m[k]?
  | [], _, _ => rfl
  | a :: l, m, h => by
    rw [List.foldl_cons, foldl_insert_get_of_ne f l _ fun i hi => h i (List.mem_cons_of_mem a hi),
      Std.HashMap.getElem?_insert, beq_eq_false_iff_ne.2 (h a List.mem_cons_self)]
    rfl

theorem foldl_insert_get (f : ℕ → ℕ) {j : ℕ} :
    ∀ (l : List ℕ) (m : Std.HashMap ℕ ℕ), j ∈ l → (∀ i ∈ l, f i = f j → i = j) →
      (l.foldl (fun m i => m.insert (f i) i) m)[f j]? = some j
  | [], _, hj, _ => absurd hj List.not_mem_nil
  | a :: l, m, hj, h => by
    rw [List.foldl_cons]
    by_cases hl : j ∈ l
    · exact foldl_insert_get f l _ hl fun i hi => h i (List.mem_cons_of_mem a hi)
    · have ha : a = j := by
        rcases List.mem_cons.1 hj with e | e
        · exact e.symm
        · exact absurd e hl
      subst ha
      rw [foldl_insert_get_of_ne f l _ fun i hi e => hl (h i (List.mem_cons_of_mem _ hi) e ▸ hi),
        Std.HashMap.getElem?_insert_self]

theorem phiArr_get
    (hkey : ∀ i < lineCert.pts.size, ∀ j < lineCert.pts.size,
      keyV lineCert.pts[i]! = keyV lineCert.pts[j]! → i = j)
    {i j : ℕ} (hi : i < lineCert.pts.size) (hj : j < lineCert.pts.size)
    (hf : lineCert.pts[j]! = frobCode lineCert.pts[i]!) : (phiArr ())[i]! = j := by
  have hget : (lineKeyIdx ()).get? (keyV lineCert.pts[j]!) = some j := by
    rw [Std.HashMap.get?_eq_getElem?, lineKeyIdx]
    exact foldl_insert_get (fun i => keyV lineCert.pts[i]!) _ _ (List.mem_range.2 hj)
      fun i hi e => hkey i (List.mem_range.1 hi) j hj e
  simp only [phiArr]
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_map, ← getElem!_pos, ← hf, hget]
  rfl

end CFSG.RankThree.PartTwo.Sec4.Item434D42
