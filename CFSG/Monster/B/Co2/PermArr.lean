module

public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Certificates.SchreierChainData
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Ring.RingNF

public noncomputable section

namespace CFSG.Monster.B.Co2

open Native CFSG.Certificates

theorem allLt_iff {n : ℕ} {p : ℕ → Bool} : allLt n p = true ↔ ∀ i < n, p i = true := by
  unfold allLt
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h i hi
    exact h ⟨i, hi⟩ (List.mem_finRange _)
  · intro h i _
    exact h i i.2

theorem allLt_spec {n : ℕ} {p : ℕ → Bool} (h : allLt n p = true) {i : ℕ} (hi : i < n) :
    p i = true :=
  allLt_iff.1 h i hi

theorem parLt_spec {n chunks : ℕ} {p : ℕ → Bool} (hc : 0 < chunks)
    (h : parLt n chunks p = true) : ∀ i < n, p i = true := by
  intro i hi
  unfold parLt at h
  simp only [List.all_map, List.all_eq_true, List.mem_range, Function.comp_apply] at h
  set sz := n / chunks + 1 with hsz
  have hsz0 : 0 < sz := Nat.succ_pos _
  have hj : i / sz < chunks := by
    rw [Nat.div_lt_iff_lt_mul hsz0]
    have h1 := Nat.div_add_mod n chunks
    have h2 := Nat.mod_lt n hc
    have : chunks * sz = chunks * (n / chunks) + chunks := by rw [hsz]; ring
    rw [this]
    generalize chunks * (n / chunks) = A at h1 ⊢
    omega
  have hstep := h (i / sz) hj
  change allLt sz (fun k => !(decide (i / sz * sz + k < n)) || p (i / sz * sz + k)) = true
    at hstep
  have := allLt_spec hstep (Nat.mod_lt i hsz0)
  have e : i / sz * sz + i % sz = i := by
    rw [mul_comm]
    exact Nat.div_add_mod i sz
  rw [e] at this
  simpa [hi] using this

variable {n : ℕ}

@[expose] def Rep (n : ℕ) (t : Array ℕ) (g : Equiv.Perm (Fin n)) : Prop :=
  ∀ x : Fin n, t[(x : ℕ)]! = g x

theorem getElem!_ofFn_nat {m : ℕ} (f : Fin m → ℕ) {i : ℕ} (hi : i < m) :
    (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by simpa using hi), Array.getElem_ofFn]

theorem compA_get {t u : Array ℕ} {i : ℕ} (hi : i < n) : (compA n t u)[i]! = t[u[i]!]! := by
  rw [compA, getElem!_ofFn_nat _ hi]

theorem idA_get {i : ℕ} (hi : i < n) : (idA n)[i]! = i := by
  rw [idA, getElem!_ofFn_nat _ hi]

theorem rep_compA {t u : Array ℕ} {g h : Equiv.Perm (Fin n)} (ht : Rep n t g) (hu : Rep n u h) :
    Rep n (compA n t u) (g * h) := fun x => by
  rw [compA_get x.2, hu x, ht (h x), Equiv.Perm.mul_apply]

theorem rep_idA : Rep n (idA n) 1 := fun x => by
  rw [idA_get x.2]
  rfl

theorem Rep.apply {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) {i : ℕ} (hi : i < n) :
    t[i]! = (g ⟨i, hi⟩ : ℕ) :=
  ht ⟨i, hi⟩

theorem Rep.lt {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) {i : ℕ} (hi : i < n) :
    t[i]! < n := by
  rw [ht.apply hi]
  exact (g _).2

theorem Rep.unique {t : Array ℕ} {g h : Equiv.Perm (Fin n)} (hg : Rep n t g) (hh : Rep n t h) :
    g = h :=
  Equiv.ext fun x => Fin.ext ((hg x).symm.trans (hh x))

theorem eqA_iff {t u : Array ℕ} {g h : Equiv.Perm (Fin n)} (ht : Rep n t g) (hu : Rep n u h) :
    eqA n t u = true ↔ g = h := by
  rw [eqA, allLt_iff]
  constructor
  · intro H
    refine Equiv.ext fun x => Fin.ext ?_
    have := H x x.2
    rwa [beq_iff_eq, ht x, hu x] at this
  · rintro rfl i hi
    rw [beq_iff_eq, ht.apply hi, hu.apply hi]

theorem eq_of_eqA {t u : Array ℕ} {g h : Equiv.Perm (Fin n)} (ht : Rep n t g) (hu : Rep n u h)
    (he : eqA n t u = true) : g = h :=
  (eqA_iff ht hu).1 he

open scoped _root_.Classical in
@[expose, irreducible] def permOfArr (n : ℕ) (t : Array ℕ) : Equiv.Perm (Fin n) :=
  if h : (∀ i < n, t[i]! < n) ∧ ∀ i < n, ∀ j < n, t[i]! = t[j]! → i = j then
    Equiv.ofBijective (fun i : Fin n => (⟨t[(i : ℕ)]!, h.1 i i.2⟩ : Fin n))
      (Finite.injective_iff_bijective.1 fun i j hij =>
        Fin.ext (h.2 i i.2 j j.2 (congrArg Fin.val hij)))
  else 1

theorem isInvA_spec {t r : Array ℕ} (h : isInvA n t r = true) {i : ℕ} (hi : i < n) :
    t[i]! < n ∧ r[t[i]!]! = i := by
  have := allLt_spec h hi
  simpa [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using this

theorem rep_permOfArr {t r : Array ℕ} (h : isInvA n t r = true) :
    Rep n t (permOfArr n t) ∧ Rep n r (permOfArr n t)⁻¹ := by
  have hc : (∀ i < n, t[i]! < n) ∧ ∀ i < n, ∀ j < n, t[i]! = t[j]! → i = j :=
    ⟨fun i hi => (isInvA_spec h hi).1, fun i hi j hj hij => by
      rw [← (isInvA_spec h hi).2, ← (isInvA_spec h hj).2, hij]⟩
  have ht : Rep n t (permOfArr n t) := fun x => by
    rw [permOfArr, dite_eq_left hc]
    rfl
  refine ⟨ht, fun x => ?_⟩
  set y := (permOfArr n t)⁻¹ x
  have hy : permOfArr n t y = x := by simp [y]
  have h1 := ht y
  rw [hy] at h1
  rw [← h1, (isInvA_spec h y.2).2]

theorem rep_inv_of_isInvA {t r : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g)
    (h : isInvA n t r = true) : Rep n r g⁻¹ := by
  have := rep_permOfArr h
  rw [ht.unique this.1]
  exact this.2

@[expose] def toLetters (j : ℕ) (w : List ℤ) : List (SchreierLetter j) :=
  w.filterMap fun l =>
    if h : l ≠ 0 ∧ l.natAbs ≤ j then some (⟨l.natAbs - 1, by omega⟩, decide (0 < l)) else none

theorem rep_letterA {S Sinv : Array (Array ℕ)} {gs : ℕ → Equiv.Perm (Fin n)} {j : ℕ}
    (hS : ∀ h < j, Rep n S[h]! (gs h)) (hSinv : ∀ h < j, Rep n Sinv[h]! (gs h)⁻¹) {l : ℤ}
    (hl : l ≠ 0 ∧ l.natAbs ≤ j) :
    Rep n (letterA S Sinv l)
      (if decide (0 < l) then gs (l.natAbs - 1) else (gs (l.natAbs - 1))⁻¹) := by
  unfold letterA
  by_cases hpos : 0 < l
  · rw [ite_eq_left hpos, ite_eq_left (decide_eq_true hpos)]
    have e : l.toNat - 1 = l.natAbs - 1 := by omega
    rw [e]
    exact hS _ (by omega)
  · rw [ite_eq_right hpos, ite_eq_right (by simpa using hpos)]
    have e : (-l).toNat - 1 = l.natAbs - 1 := by omega
    rw [e]
    exact hSinv _ (by omega)

theorem rep_wordA {S Sinv : Array (Array ℕ)} {gs : ℕ → Equiv.Perm (Fin n)} {j : ℕ}
    (hS : ∀ h < j, Rep n S[h]! (gs h)) (hSinv : ∀ h < j, Rep n Sinv[h]! (gs h)⁻¹) :
    ∀ w : List ℤ, lettersOK j w = true →
      Rep n (wordA n S Sinv w)
        (Quiver.SchreierGraph.evalWord (fun h : Fin j => gs h) (toLetters j w))
  | [], _ => by
    simpa [wordA, toLetters] using (rep_idA (n := n))
  | l :: w, hw => by
    simp only [lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw
    obtain ⟨⟨hl0, hlj⟩, hw⟩ := hw
    have hw' : lettersOK j w = true := by
      simpa [lettersOK, List.all_eq_true] using hw
    have ih := rep_wordA hS hSinv w hw'
    have hcons : toLetters j (l :: w) = (⟨l.natAbs - 1, by omega⟩, decide (0 < l)) ::
        toLetters j w := by
      simp [toLetters, hl0, hlj]
    rw [wordA, hcons]
    have hlet := rep_letterA hS hSinv ⟨hl0, hlj⟩
    by_cases hpos : 0 < l
    · rw [ite_eq_left (decide_eq_true hpos)] at hlet
      rw [decide_eq_true hpos, Quiver.SchreierGraph.evalWord_cons_true]
      exact rep_compA hlet ih
    · rw [ite_eq_right (by simpa using hpos)] at hlet
      rw [show decide (0 < l) = false by simpa using hpos,
        Quiver.SchreierGraph.evalWord_cons_false]
      exact rep_compA hlet ih

end CFSG.Monster.B.Co2
