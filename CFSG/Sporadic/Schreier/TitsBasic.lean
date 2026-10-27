module

public import CFSG.Monster.B.Co2.PermArr
public import Certificates.Data.CFSGNative.Schreier.Check
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open scoped commutatorElement

section Words

variable {G H : Type*} [Group G] [Group H]

@[expose] def wordIn (k : ℕ) (gs : ℕ → G) (w : List ℤ) : G :=
  Quiver.SchreierGraph.evalWord (fun h : Fin k => gs h) (toLetters k w)

@[expose] def tcomm (x y : G) : G := x⁻¹ * y⁻¹ * x * y

theorem evalWord_map (f : G →* H) {k : ℕ} (gs : Fin k → G) (w : List (Fin k × Bool)) :
    f (Quiver.SchreierGraph.evalWord gs w) = Quiver.SchreierGraph.evalWord (f ∘ gs) w := by
  induction w with
  | nil => simp
  | cons a w ih =>
    obtain ⟨h, b⟩ := a
    cases b <;> simp [ih]

theorem map_wordIn (f : G →* H) (k : ℕ) (gs : ℕ → G) (w : List ℤ) :
    f (wordIn k gs w) = wordIn k (f ∘ gs) w :=
  evalWord_map f _ _

theorem map_tcomm (f : G →* H) (x y : G) : f (tcomm x y) = tcomm (f x) (f y) := by
  simp [tcomm]

theorem wordIn_append (k : ℕ) (gs : ℕ → G) (w₁ w₂ : List ℤ) :
    wordIn k gs (w₁ ++ w₂) = wordIn k gs w₁ * wordIn k gs w₂ := by
  rw [wordIn, toLetters, List.filterMap_append, Quiver.SchreierGraph.evalWord_append]
  rfl

theorem evalWord_congr {k : ℕ} {gs gs' : Fin k → G} (h : ∀ i, gs i = gs' i)
    (w : List (Fin k × Bool)) :
    Quiver.SchreierGraph.evalWord gs w = Quiver.SchreierGraph.evalWord gs' w := by
  rw [show gs = gs' from funext h]

theorem wordIn_congr {k : ℕ} {gs gs' : ℕ → G} (h : ∀ i < k, gs i = gs' i) (w : List ℤ) :
    wordIn k gs w = wordIn k gs' w :=
  evalWord_congr (fun i => h i i.2) _

theorem wordIn_mem {k : ℕ} {gs : ℕ → G} {K : Subgroup G} (h : ∀ i < k, gs i ∈ K)
    (w : List ℤ) : wordIn k gs w ∈ K := by
  have hle : Subgroup.closure (Set.range fun i : Fin k => gs i) ≤ K :=
    (Subgroup.closure_le K).2 (by rintro _ ⟨i, rfl⟩; exact h i i.2)
  exact hle (Quiver.SchreierGraph.evalWord_mem_closure _ _)

theorem tcomm_mem {K : Subgroup G} {x y : G} (hx : x ∈ K) (hy : y ∈ K) : tcomm x y ∈ K :=
  mul_mem (mul_mem (mul_mem (inv_mem hx) (inv_mem hy)) hx) hy

theorem tcomm_eq_commutatorElement (x y : G) : tcomm x y = ⁅x⁻¹, y⁻¹⁆ := by
  simp [tcomm, commutatorElement_def]

theorem tcomm_mem_commutator {K : Subgroup G} {x y : G} (hx : x ∈ K) (hy : y ∈ K) :
    tcomm x y ∈ ⁅K, K⁆ := by
  rw [tcomm_eq_commutatorElement]
  exact Subgroup.commutator_mem_commutator (inv_mem hx) (inv_mem hy)

end Words

theorem perm_apply_inv {α : Type*} (g : Equiv.Perm α) (x : α) : g (g⁻¹ x) = x := by
  rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]

theorem perm_inv_apply {α : Type*} (g : Equiv.Perm α) (x : α) : g⁻¹ (g x) = x := by
  rw [← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]

section Strong

variable {G H : Type*} [Group G] [Group H]

@[expose] def strongOf (k : ℕ) (start : ℕ → G) (W : List (List ℤ)) (j : ℕ) : G :=
  if j < k then start j
  else wordIn j (fun h => if h < j then strongOf k start W h else 1) (W.getD (j - k) [])
termination_by j
decreasing_by all_goals omega

theorem strongOf_of_lt {k : ℕ} {start : ℕ → G} {W : List (List ℤ)} {j : ℕ} (hj : j < k) :
    strongOf k start W j = start j := by
  rw [strongOf]
  simp only [hj, ↓reduceIte]

theorem strongOf_of_le {k : ℕ} {start : ℕ → G} {W : List (List ℤ)} {j : ℕ} (hj : k ≤ j) :
    strongOf k start W j = wordIn j (strongOf k start W) (W.getD (j - k) []) := by
  rw [strongOf]
  simp only [show ¬ j < k by omega, ↓reduceIte]
  exact wordIn_congr (fun h hh => by simp only [hh, ↓reduceIte]) _

theorem map_strongOf (f : G →* H) (k : ℕ) (start : ℕ → G) (W : List (List ℤ)) :
    ∀ j, f (strongOf k start W j) = strongOf k (f ∘ start) W j := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    by_cases hj : j < k
    · rw [strongOf_of_lt hj, strongOf_of_lt hj]
      rfl
    · rw [strongOf_of_le (by omega), strongOf_of_le (by omega), map_wordIn]
      exact wordIn_congr (fun h hh => ih h hh) _

theorem strongOf_mem {k : ℕ} {start : ℕ → G} {W : List (List ℤ)} {K : Subgroup G}
    (h : ∀ i < k, start i ∈ K) : ∀ j, strongOf k start W j ∈ K := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    by_cases hj : j < k
    · rw [strongOf_of_lt hj]
      exact h j hj
    · rw [strongOf_of_le (by omega)]
      exact wordIn_mem (fun h hh => ih h hh) _

end Strong

@[expose] def finPt (n : ℕ) [NeZero n] (x : ℕ) : Fin n := ⟨x % n, Nat.mod_lt _ (NeZero.pos n)⟩

theorem finPt_val {n : ℕ} [NeZero n] {x : ℕ} (hx : x < n) : ((finPt n x : Fin n) : ℕ) = x :=
  Nat.mod_eq_of_lt hx

theorem finPt_eq {n : ℕ} [NeZero n] {x : ℕ} (hx : x < n) : finPt n x = ⟨x, hx⟩ :=
  Fin.ext (finPt_val hx)

@[expose] def finList (n : ℕ) [NeZero n] (b : List ℕ) : List (Fin n) := b.map (finPt n)

@[expose] def baseArr (n : ℕ) [NeZero n] (b : List ℕ) : Array ℕ :=
  ((finList n b).map Fin.val).toArray

@[expose] def wordsArr (k s : ℕ) (D : List (List ℤ)) : Array (List ℤ) :=
  Array.ofFn (n := s) fun j => if j.val < k then [] else D.getD (j.val - k) []

section Lift

variable {G M : Type*} [Group G] [Group M]

@[expose] def liftFam (K : Subgroup G) (k : ℕ) (gs : ℕ → G) (h : ∀ i < k, gs i ∈ K) : ℕ → K :=
  fun i => if hi : i < k then ⟨gs i, h i hi⟩ else 1

theorem coe_liftFam {K : Subgroup G} {k : ℕ} {gs : ℕ → G} (h : ∀ i < k, gs i ∈ K) {i : ℕ}
    (hi : i < k) : (liftFam K k gs h i : G) = gs i := by
  simp [liftFam, hi]

theorem coe_wordIn_liftFam {K : Subgroup G} {k : ℕ} {gs : ℕ → G} (h : ∀ i < k, gs i ∈ K)
    (w : List ℤ) : ((wordIn k (liftFam K k gs h) w : K) : G) = wordIn k gs w := by
  rw [← K.coe_subtype, map_wordIn]
  exact wordIn_congr (fun i hi => coe_liftFam h hi) w

theorem strongOf_congr {k : ℕ} {s s' : ℕ → M} (h : ∀ i < k, s i = s' i) (W : List (List ℤ)) :
    ∀ j, strongOf k s W j = strongOf k s' W j := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    by_cases hj : j < k
    · rw [strongOf_of_lt hj, strongOf_of_lt hj, h j hj]
    · rw [strongOf_of_le (by omega), strongOf_of_le (by omega)]
      exact wordIn_congr (fun i hi => ih i hi) _

theorem coe_strongOf_liftFam {K : Subgroup G} {k : ℕ} {gs : ℕ → G} (h : ∀ i < k, gs i ∈ K)
    (W : List (List ℤ)) (j : ℕ) :
    ((strongOf k (liftFam K k gs h) W j : K) : G) = strongOf k gs W j := by
  rw [← K.coe_subtype, map_strongOf]
  exact strongOf_congr (fun i hi => coe_liftFam h hi) W j

theorem hom_wordIn {K : Subgroup G} (φ : K →* M) {k : ℕ} {gs : ℕ → G} (h : ∀ i < k, gs i ∈ K)
    {ms : ℕ → M} (hms : ∀ i (hi : i < k), φ ⟨gs i, h i hi⟩ = ms i) (w : List ℤ)
    (hw : wordIn k gs w ∈ K) : φ ⟨wordIn k gs w, hw⟩ = wordIn k ms w := by
  have e : (⟨wordIn k gs w, hw⟩ : K) = wordIn k (liftFam K k gs h) w :=
    Subtype.ext (coe_wordIn_liftFam h w).symm
  rw [e, map_wordIn]
  exact wordIn_congr (fun i hi => by simp only [Function.comp_apply, liftFam, hi, ↓reduceDIte,
    hms i hi]) w

theorem hom_strongOf {K : Subgroup G} (φ : K →* M) {k : ℕ} {gs : ℕ → G} (h : ∀ i < k, gs i ∈ K)
    {ms : ℕ → M} (hms : ∀ i (hi : i < k), φ ⟨gs i, h i hi⟩ = ms i) (W : List (List ℤ)) (j : ℕ)
    (hj : strongOf k gs W j ∈ K) : φ ⟨strongOf k gs W j, hj⟩ = strongOf k ms W j := by
  have e : (⟨strongOf k gs W j, hj⟩ : K) = strongOf k (liftFam K k gs h) W j :=
    Subtype.ext (coe_strongOf_liftFam h W j).symm
  rw [e, map_strongOf]
  exact strongOf_congr (fun i hi => by simp only [Function.comp_apply, liftFam, hi,
    ↓reduceDIte, hms i hi]) W j

end Lift

section Arrays

variable {n : ℕ}

@[expose] def allPermsOK (n : ℕ) (A : Array (Array ℕ)) : Bool :=
  allLt A.size fun j => isInvA n A[j]! (invCand n A[j]!)

theorem isInvA_of_allPermsOK {A : Array (Array ℕ)} (h : allPermsOK n A = true) {j : ℕ}
    (hj : j < A.size) : isInvA n A[j]! (invCand n A[j]!) = true :=
  allLt_spec h hj

theorem rep_of_allPermsOK {A : Array (Array ℕ)} (h : allPermsOK n A = true) {j : ℕ}
    (hj : j < A.size) : Rep n A[j]! (permOfArr n A[j]!) :=
  (rep_permOfArr (isInvA_of_allPermsOK h hj)).1

@[expose] def wordArr (n : ℕ) (A : Array (Array ℕ)) (w : List ℤ) : Array ℕ :=
  wordA n A (A.map (invCand n)) w

@[expose] def commArr (n : ℕ) (u v : Array ℕ) : Array ℕ :=
  compA n (compA n (compA n (invCand n u) (invCand n v)) u) v

@[expose] def strongArrs (n : ℕ) (start : Array (Array ℕ)) (W : List (List ℤ)) :
    Array (Array ℕ) :=
  W.foldl (fun S w => S.push (wordArr n S w)) start

theorem getElem!_map_of_lt {A : Array (Array ℕ)} {f : Array ℕ → Array ℕ} {i : ℕ}
    (hi : i < A.size) : (A.map f)[i]! = f A[i]! := by
  rw [getElem!_pos (A.map f) i (by simpa using hi), Array.getElem_map, getElem!_pos A i hi]

theorem getElem!_ofFn_of_lt {α : Type*} [Inhabited α] {m : ℕ} (f : Fin m → α) {i : ℕ}
    (hi : i < m) : (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by simpa using hi), Array.getElem_ofFn]

theorem rep_wordArr {k : ℕ} {A : Array (Array ℕ)} {gs : ℕ → Equiv.Perm (Fin n)} (hk : k ≤ A.size)
    (hA : ∀ i < k, Rep n A[i]! (gs i)) (hinv : ∀ i < k, isInvA n A[i]! (invCand n A[i]!) = true)
    {w : List ℤ} (hw : lettersOK k w = true) : Rep n (wordArr n A w) (wordIn k gs w) :=
  rep_wordA hA (fun i hi => by
    rw [getElem!_map_of_lt (by omega)]
    exact rep_inv_of_isInvA (hA i hi) (hinv i hi)) w hw

theorem rep_commArr {u v : Array ℕ} {x y : Equiv.Perm (Fin n)} (hu : Rep n u x) (hv : Rep n v y)
    (hu' : isInvA n u (invCand n u) = true) (hv' : isInvA n v (invCand n v) = true) :
    Rep n (commArr n u v) (tcomm x y) :=
  rep_compA (rep_compA (rep_compA (rep_inv_of_isInvA hu hu') (rep_inv_of_isInvA hv hv')) hu) hv

@[expose] def strongOK (n k : ℕ) (start S : Array (Array ℕ)) (W : List (List ℤ)) : Bool :=
  S.size == k + W.length && allLt S.size (fun j => isInvA n S[j]! (invCand n S[j]!)) &&
    allLt k (fun j => eqA n S[j]! start[j]!) &&
    allLt W.length (fun i => lettersOK (k + i) W[i]! &&
      eqA n S[k + i]! (wordA n S (S.map (invCand n)) W[i]!))

theorem size_of_strongOK {k : ℕ} {start S : Array (Array ℕ)} {W : List (List ℤ)}
    (h : strongOK n k start S W = true) : S.size = k + W.length := by
  simp only [strongOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1

theorem isInvA_of_strongOK {k : ℕ} {start S : Array (Array ℕ)} {W : List (List ℤ)}
    (h : strongOK n k start S W = true) {j : ℕ} (hj : j < S.size) :
    isInvA n S[j]! (invCand n S[j]!) = true := by
  simp only [strongOK, Bool.and_eq_true, beq_iff_eq] at h
  exact allLt_spec h.1.1.2 hj

theorem rep_of_strongOK {k : ℕ} {start S : Array (Array ℕ)} {W : List (List ℤ)}
    {gs : ℕ → Equiv.Perm (Fin n)} (h : strongOK n k start S W = true)
    (hs : ∀ i < k, Rep n start[i]! (gs i)) :
    ∀ j < S.size, Rep n S[j]! (strongOf k gs W j) := by
  simp only [strongOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hsz, hinv⟩, hstart⟩, hword⟩ := h
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    by_cases hjk : j < k
    · rw [strongOf_of_lt hjk]
      have he := allLt_spec hstart hjk
      have hr := rep_permOfArr (allLt_spec hinv hj)
      have hr' := (hs j hjk)
      rw [eq_of_eqA hr.1 hr' he] at hr
      exact hr.1
    · have hi : j - k < W.length := by omega
      have hw := allLt_spec hword hi
      simp only [Bool.and_eq_true] at hw
      rw [show k + (j - k) = j by omega] at hw
      have hrep : Rep n (wordA n S (S.map (invCand n)) W[j - k]!)
          (wordIn j (strongOf k gs W) W[j - k]!) :=
        rep_wordA (fun h hh => ih h hh (by omega)) (fun h hh => by
          rw [getElem!_map_of_lt (by omega)]
          exact rep_inv_of_isInvA (ih h hh (by omega)) (allLt_spec hinv (by omega)))
          _ hw.1
      have hr := rep_permOfArr (allLt_spec hinv hj)
      rw [strongOf_of_le (by omega), show W.getD (j - k) [] = W[j - k]! by
        rw [List.getD_eq_getElem?_getD, getElem!_def]; rfl]
      rw [← eq_of_eqA hr.1 hrep hw.2]
      exact hr.1

end Arrays

end CFSG.Sporadic.Schreier.Tits
