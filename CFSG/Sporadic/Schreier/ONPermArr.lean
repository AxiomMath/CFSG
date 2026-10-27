module

public import Certificates.Data.CFSGNative.ONSchreier.Compact
public import CFSG.Certificates.SchreierChainData
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Ring.RingNF

public noncomputable section

namespace CFSG.ONSchreier

open CFSG.ONSchreier.Native CFSG.Certificates

theorem allBelowN_iff {n : ℕ} {p : ℕ → Bool} : allBelowN n p = true ↔ ∀ i < n, p i = true := by
  unfold allBelowN
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h i hi
    exact h ⟨i, hi⟩ (List.mem_finRange _)
  · intro h i _
    exact h i i.2

theorem allBelowN_spec {n : ℕ} {p : ℕ → Bool} (h : allBelowN n p = true) {i : ℕ} (hi : i < n) :
    p i = true :=
  allBelowN_iff.1 h i hi

theorem parBelow_spec {n chunks : ℕ} {p : ℕ → Bool} (hc : 0 < chunks)
    (h : parBelow n chunks p = true) : ∀ i < n, p i = true := by
  intro i hi
  unfold parBelow at h
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
  change allBelowN sz (fun k => !(decide (i / sz * sz + k < n)) || p (i / sz * sz + k)) = true
    at hstep
  have := allBelowN_spec hstep (Nat.mod_lt i hsz0)
  have e : i / sz * sz + i % sz = i := by
    rw [mul_comm]
    exact Nat.div_add_mod i sz
  rw [e] at this
  simpa [hi] using this

variable {n : ℕ}

@[expose] def PRep (n : ℕ) (t : Array ℕ) (g : Equiv.Perm (Fin n)) : Prop :=
  ∀ x : Fin n, t[(x : ℕ)]! = g x

theorem getElem!_ofFn_nat {m : ℕ} (f : Fin m → ℕ) {i : ℕ} (hi : i < m) :
    (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by simpa using hi), Array.getElem_ofFn]

theorem pcomp_get {t u : Array ℕ} {i : ℕ} (hi : i < n) : (pcomp n t u)[i]! = t[u[i]!]! := by
  rw [pcomp, getElem!_ofFn_nat _ hi]

theorem pid_get {i : ℕ} (hi : i < n) : (pid n)[i]! = i := by
  rw [pid, getElem!_ofFn_nat _ hi]

theorem prep_pcomp {t u : Array ℕ} {g h : Equiv.Perm (Fin n)} (ht : PRep n t g)
    (hu : PRep n u h) : PRep n (pcomp n t u) (g * h) := fun x => by
  rw [pcomp_get x.2, hu x, ht (h x), Equiv.Perm.mul_apply]

theorem prep_pid : PRep n (pid n) 1 := fun x => by
  rw [pid_get x.2]
  rfl

theorem PRep.apply {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : PRep n t g) {i : ℕ}
    (hi : i < n) : t[i]! = (g ⟨i, hi⟩ : ℕ) :=
  ht ⟨i, hi⟩

theorem PRep.lt {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : PRep n t g) {i : ℕ} (hi : i < n) :
    t[i]! < n := by
  rw [ht.apply hi]
  exact (g _).2

theorem PRep.unique {t : Array ℕ} {g h : Equiv.Perm (Fin n)} (hg : PRep n t g)
    (hh : PRep n t h) : g = h :=
  Equiv.ext fun x => Fin.ext ((hg x).symm.trans (hh x))

theorem peq_iff {t u : Array ℕ} {g h : Equiv.Perm (Fin n)} (ht : PRep n t g) (hu : PRep n u h) :
    peq n t u = true ↔ g = h := by
  rw [peq, allBelowN_iff]
  constructor
  · intro H
    refine Equiv.ext fun x => Fin.ext ?_
    have := H x x.2
    rwa [beq_iff_eq, ht x, hu x] at this
  · rintro rfl i hi
    rw [beq_iff_eq, ht.apply hi, hu.apply hi]

theorem eq_of_peq {t u : Array ℕ} {g h : Equiv.Perm (Fin n)} (ht : PRep n t g) (hu : PRep n u h)
    (he : peq n t u = true) : g = h :=
  (peq_iff ht hu).1 he

open scoped Classical in
@[expose, irreducible] def permOfArr (n : ℕ) (t : Array ℕ) : Equiv.Perm (Fin n) :=
  if h : (∀ i < n, t[i]! < n) ∧ ∀ i < n, ∀ j < n, t[i]! = t[j]! → i = j then
    Equiv.ofBijective (fun i : Fin n => (⟨t[(i : ℕ)]!, h.1 i i.2⟩ : Fin n))
      (Finite.injective_iff_bijective.1 fun i j hij =>
        Fin.ext (h.2 i i.2 j j.2 (congrArg Fin.val hij)))
  else 1

theorem pisInv_spec {t r : Array ℕ} (h : pisInv n t r = true) {i : ℕ} (hi : i < n) :
    t[i]! < n ∧ r[t[i]!]! = i := by
  have := allBelowN_spec h hi
  simpa [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using this

theorem prep_permOfArr {t r : Array ℕ} (h : pisInv n t r = true) :
    PRep n t (permOfArr n t) ∧ PRep n r (permOfArr n t)⁻¹ := by
  have hc : (∀ i < n, t[i]! < n) ∧ ∀ i < n, ∀ j < n, t[i]! = t[j]! → i = j :=
    ⟨fun i hi => (pisInv_spec h hi).1, fun i hi j hj hij => by
      rw [← (pisInv_spec h hi).2, ← (pisInv_spec h hj).2, hij]⟩
  have ht : PRep n t (permOfArr n t) := fun x => by
    rw [permOfArr, dite_eq_left hc]
    rfl
  refine ⟨ht, fun x => ?_⟩
  set y := (permOfArr n t)⁻¹ x
  have hy : permOfArr n t y = x := by simp [y]
  have h1 := ht y
  rw [hy] at h1
  rw [← h1, (pisInv_spec h y.2).2]

theorem prep_inv_of_pisInv {t r : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : PRep n t g)
    (h : pisInv n t r = true) : PRep n r g⁻¹ := by
  have := prep_permOfArr h
  rw [ht.unique this.1]
  exact this.2

@[expose] def ptoLetters (j : ℕ) (w : List ℤ) : List (SchreierLetter j) :=
  w.filterMap fun l =>
    if h : l ≠ 0 ∧ l.natAbs ≤ j then some (⟨l.natAbs - 1, by omega⟩, decide (0 < l)) else none

theorem prep_pletter {S Sinv : Array (Array ℕ)} {gs : ℕ → Equiv.Perm (Fin n)} {j : ℕ}
    (hS : ∀ h < j, PRep n S[h]! (gs h)) (hSinv : ∀ h < j, PRep n Sinv[h]! (gs h)⁻¹) {l : ℤ}
    (hl : l ≠ 0 ∧ l.natAbs ≤ j) :
    PRep n (pletter S Sinv l)
      (if decide (0 < l) then gs (l.natAbs - 1) else (gs (l.natAbs - 1))⁻¹) := by
  unfold pletter
  by_cases hpos : 0 < l
  · rw [ite_eq_left hpos, ite_eq_left (decide_eq_true hpos)]
    have e : l.toNat - 1 = l.natAbs - 1 := by omega
    rw [e]
    exact hS _ (by omega)
  · rw [ite_eq_right hpos, ite_eq_right (by simpa using hpos)]
    have e : (-l).toNat - 1 = l.natAbs - 1 := by omega
    rw [e]
    exact hSinv _ (by omega)

theorem prep_pword {S Sinv : Array (Array ℕ)} {gs : ℕ → Equiv.Perm (Fin n)} {j : ℕ}
    (hS : ∀ h < j, PRep n S[h]! (gs h)) (hSinv : ∀ h < j, PRep n Sinv[h]! (gs h)⁻¹) :
    ∀ w : List ℤ, plettersOK j w = true →
      PRep n (pword n S Sinv w)
        (Quiver.SchreierGraph.evalWord (fun h : Fin j => gs h) (ptoLetters j w))
  | [], _ => by
    simpa [pword, ptoLetters] using (prep_pid (n := n))
  | l :: w, hw => by
    simp only [plettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw
    obtain ⟨⟨hl0, hlj⟩, hw⟩ := hw
    have hw' : plettersOK j w = true := by
      simpa [plettersOK, List.all_eq_true] using hw
    have ih := prep_pword hS hSinv w hw'
    have hcons : ptoLetters j (l :: w) = (⟨l.natAbs - 1, by omega⟩, decide (0 < l)) ::
        ptoLetters j w := by
      simp [ptoLetters, hl0, hlj]
    rw [pword, hcons]
    have hlet := prep_pletter hS hSinv ⟨hl0, hlj⟩
    by_cases hpos : 0 < l
    · rw [ite_eq_left (decide_eq_true hpos)] at hlet
      rw [decide_eq_true hpos, Quiver.SchreierGraph.evalWord_cons_true]
      exact prep_pcomp hlet ih
    · rw [ite_eq_right (by simpa using hpos)] at hlet
      rw [show decide (0 < l) = false by simpa using hpos,
        Quiver.SchreierGraph.evalWord_cons_false]
      exact prep_pcomp hlet ih

end CFSG.ONSchreier
