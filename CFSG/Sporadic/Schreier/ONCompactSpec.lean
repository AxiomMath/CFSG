module

public import CFSG.Sporadic.Schreier.ONPermArr
public import CFSG.Certificates.SchreierPointSift
public import CFSG.Certificates.SchreierChainOrder
public import CFSG.Monster.B.Co2.BFS
public import Mathlib.Data.List.GetD

public noncomputable section

namespace CFSG.ONSchreier

open CFSG.ONSchreier.Native CFSG.Certificates CFSG.Certificates.SchreierOrbitState
open CFSG.Monster.B.Co2 (BFSCert LexLt)

variable {n : ℕ}

structure CArrays (Q : RawSchreierDatum n) (m : ℕ) (S : Array (Array ℕ)) (base : Array ℕ)
    (W : Array (List ℤ)) : Prop where
  orig_count : Q.originalCount = m
  strong_size : S.size = Q.strongCount
  base_size : base.size = Q.baseCount
  orig : ∀ j : Fin Q.strongCount, j.val < m → PRep n S[j.val]! (Q.strong.get j)
  base_val : ∀ i : Fin Q.baseCount, ((Q.base.get i : Fin n) : ℕ) = base[i.val]!
  deriv : ∀ (j : Fin Q.strongCount) (hj : Q.originalCount ≤ j.val),
    Q.derivation j hj = ptoLetters j.val W[j.val]!
  initial : ∀ j : Fin Q.originalCount,
    Q.strong.get (Fin.castLE Q.originalCount_le j) = Q.original.get j
  words : ∀ (j : Fin Q.strongCount) (hj : Q.originalCount ≤ j.val),
    Q.strong.get j = Q.derivationValue j hj

abbrev stepsOf (n : ℕ) (S : Array (Array ℕ)) (base : Array ℕ) : Array (Array (Array ℕ)) :=
  allSteps S (pinvs n S) base

abbrev invsOf (n : ℕ) (S : Array (Array ℕ)) (base : Array ℕ) : Array (Array (Array ℕ)) :=
  allInvSteps S (pinvs n S) base

abbrev levelsOf (n : ℕ) (S : Array (Array ℕ)) (base : Array ℕ) : Array CLevel :=
  cLevels n base (stepsOf n S base)

structure CChainFacts (n m : ℕ) (S : Array (Array ℕ)) (base : Array ℕ) (W : Array (List ℤ))
    (pts bidx : Array ℕ) (full : Bool) (chunks : ℕ) : Prop where
  m_le : m ≤ S.size
  words_size : W.size = S.size
  strong_inv : ∀ j < S.size, pisInv n S[j]! (pinvs n S)[j]! = true
  words : ∀ j < S.size, m ≤ j →
    plettersOK j W[j]! = true ∧ peq n S[j]! (pword n S (pinvs n S) W[j]!) = true
  base_lt : ∀ i < base.size, base[i]! < n
  bidx_size : bidx.size = base.size
  bidx_ok : ∀ i < base.size, bidx[i]! < pts.size ∧ pts[bidx[i]!]! = base[i]!
  pts_lt : ∀ t < pts.size, pts[t]! < n
  terminal : full = true → ∀ j < S.size, pfixes base S[j]! base.size = true →
    peq n S[j]! (pid n) = true
  level : ∀ i < base.size,
    clevelOK n base[i]! (stepsOf n S base)[i]! (levelsOf n S base)[i]! = true
  schreier : ∀ i < base.size, cschreierOK (levelsOf n S base) (stepsOf n S base)
    (invsOf n S base) pts bidx full i chunks = true

theorem chainFacts {m : ℕ} {S : Array (Array ℕ)} {base : Array ℕ} {W : Array (List ℤ)}
    {pts bidx : Array ℕ} {full : Bool} {chunks : ℕ}
    (h : chainOK n m S base W pts bidx full chunks = true) :
    CChainFacts n m S base W pts bidx full chunks := by
  simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  refine ⟨h1, h2, fun j hj => allBelowN_spec h3 hj, fun j hj hjm => ?_,
    fun i hi => of_decide_eq_true (allBelowN_spec h5 hi), h6, fun i hi => ?_,
    fun t ht => of_decide_eq_true (allBelowN_spec h8 ht), fun hf j hj hfix => ?_,
    fun i hi => allBelowN_spec h10 hi, fun i hi => allBelowN_spec h11 hi⟩
  · have := allBelowN_spec h4 hj
    simpa [show ¬ j < m by omega] using this
  · have := allBelowN_spec h7 hi
    simpa [Bool.and_eq_true] using this
  · subst hf
    have := allBelowN_spec h9 hj
    simpa [hfix] using this

@[expose] def strongAt (Q : RawSchreierDatum n) (j : ℕ) : Equiv.Perm (Fin n) :=
  if h : j < Q.strongCount then Q.strong.get ⟨j, h⟩ else 1

theorem strongAt_of_lt (Q : RawSchreierDatum n) {j : ℕ} (hj : j < Q.strongCount) :
    strongAt Q j = Q.strong.get ⟨j, hj⟩ := by
  simp only [strongAt, hj, ↓reduceDIte]

theorem prep_of_peq {t u : Array ℕ} {g : Equiv.Perm (Fin n)} (h : peq n t u = true)
    (hu : PRep n u g) : PRep n t g := fun x => by
  have := allBelowN_spec h x.2
  rw [beq_iff_eq] at this
  rw [this, hu x]

theorem getElem!_map' {α β : Type*} [Inhabited α] [Inhabited β] (f : α → β) (a : Array α) {i : ℕ}
    (hi : i < a.size) : (a.map f)[i]! = f a[i]! := by
  rw [getElem!_pos (a.map f) i (by simpa using hi), Array.getElem_map, getElem!_pos a i hi]

theorem stepsOf_getElem {S : Array (Array ℕ)} {base : Array ℕ} {i : ℕ} (hi : i < base.size) :
    (stepsOf n S base)[i]! = levSteps S (pinvs n S) base i := by
  rw [stepsOf, allSteps, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem invsOf_getElem {S : Array (Array ℕ)} {base : Array ℕ} {i : ℕ} (hi : i < base.size) :
    (invsOf n S base)[i]! = levInvSteps S (pinvs n S) base i := by
  rw [invsOf, allInvSteps, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

namespace CArrays

variable {Q : RawSchreierDatum n} {m : ℕ} {S : Array (Array ℕ)} {base : Array ℕ}
  {W : Array (List ℤ)} {pts bidx : Array ℕ} {full : Bool} {chunks : ℕ}

section Facts

variable (hA : CArrays Q m S base W) (hF : CChainFacts n m S base W pts bidx full chunks)
include hA hF

theorem prep_strong : ∀ j < S.size, PRep n S[j]! (strongAt Q j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    have hjQ : j < Q.strongCount := hA.strong_size ▸ hj
    rw [strongAt_of_lt Q hjQ]
    by_cases hjm : j < m
    · exact hA.orig ⟨j, hjQ⟩ hjm
    · obtain ⟨hl, he⟩ := hF.words j hj (by omega)
      have hrep := prep_pword (gs := strongAt Q) (j := j)
        (fun h hh => ih h hh (by omega))
        (fun h hh => prep_inv_of_pisInv (ih h hh (by omega)) (by
          have := hF.strong_inv h (by omega)
          exact this)) _ hl
      refine prep_of_peq he ?_
      have hjm' : Q.originalCount ≤ j := by rw [hA.orig_count]; omega
      rw [hA.words ⟨j, hjQ⟩ hjm', RawSchreierDatum.derivationValue, schreierWordValue,
        hA.deriv ⟨j, hjQ⟩ hjm']
      convert hrep using 2
      funext h
      exact (strongAt_of_lt Q (by omega)).symm

theorem prep_strongInv {j : ℕ} (hj : j < S.size) : PRep n (pinvs n S)[j]! (strongAt Q j)⁻¹ :=
  prep_inv_of_pisInv (hA.prep_strong hF j hj) (hF.strong_inv j hj)

end Facts

theorem strong_toList (Q : RawSchreierDatum n) :
    Q.strong.toList = (List.range Q.strongCount).map (strongAt Q) := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [List.length_map, List.length_range] at h2
  rw [List.getElem_map, List.getElem_range, strongAt_of_lt Q h2, Vector.getElem_toList]
  rfl

@[expose] def toFin (Q : RawSchreierDatum n) (x : ℕ) : Fin n :=
  ⟨x % n, Nat.mod_lt _ (by have := Q.degree_pos; omega)⟩

theorem toFin_eq (Q : RawSchreierDatum n) {x : ℕ} (hx : x < n) : toFin Q x = ⟨x, hx⟩ :=
  Fin.ext (Nat.mod_eq_of_lt hx)

section Facts

variable (hA : CArrays Q m S base W) (hF : CChainFacts n m S base W pts bidx full chunks)
include hA hF

theorem base_toList :
    Q.base.toList = (List.range Q.baseCount).map fun k => toFin Q base[k]! := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [List.length_map, List.length_range] at h2
  rw [List.getElem_map, List.getElem_range, Vector.getElem_toList]
  have hb := hF.base_lt k (hA.base_size ▸ h2)
  rw [toFin_eq Q hb]
  apply Fin.ext
  exact hA.base_val ⟨k, h2⟩

theorem fixes_iff {j : ℕ} (hj : j < S.size) {i : ℕ} (hi : i ≤ Q.baseCount) :
    ((Q.base.toList.take i).all fun b => decide (strongAt Q j b = b)) =
      pfixes base S[j]! i := by
  rw [hA.base_toList hF, List.map_take.symm, List.take_range, Nat.min_eq_left hi,
    Bool.eq_iff_iff, List.all_map, List.all_eq_true, pfixes, allBelowN_iff]
  simp only [List.mem_range, Function.comp_apply, decide_eq_true_eq, beq_iff_eq]
  refine forall_congr' fun k => imp_congr_right fun hk => ?_
  have hb := hF.base_lt k (by rw [hA.base_size]; omega)
  rw [toFin_eq Q hb, (hA.prep_strong hF j hj).apply hb, Fin.ext_iff]

theorem levelGenerators_eq {i : ℕ} (hi : i ≤ Q.baseCount) :
    Q.levelGenerators i = (levIdx S base i).map (strongAt Q) := by
  rw [RawSchreierDatum.levelGenerators, strong_toList, List.filter_map, levIdx,
    hA.strong_size]
  congr 1
  apply List.filter_congr
  intro j hj
  exact hA.fixes_iff hF (hA.strong_size ▸ List.mem_range.1 hj) hi

end Facts

theorem levIdx_lt {i j : ℕ} (hj : j ∈ levIdx S base i) : j < S.size := by
  rw [levIdx] at hj
  exact List.mem_range.1 (List.mem_filter.1 hj).1

section Facts

variable (hA : CArrays Q m S base W) (hF : CChainFacts n m S base W pts bidx full chunks)
include hA hF

theorem levelSteps_eq {i : ℕ} (hi : i ≤ Q.baseCount) :
    Q.levelSteps i = (levIdx S base i).map (strongAt Q) ++
      (levIdx S base i).map fun j => (strongAt Q j)⁻¹ := by
  rw [RawSchreierDatum.levelSteps, hA.levelGenerators_eq hF hi, List.map_map]
  rfl

theorem steps_size {i : ℕ} (hi : i < Q.baseCount) :
    (stepsOf n S base)[i]!.size = (Q.levelSteps i).length := by
  rw [stepsOf_getElem (n := n) (S := S) (hA.base_size ▸ hi), hA.levelSteps_eq hF (Nat.le_of_lt hi),
    levSteps]
  simp

theorem invs_size {i : ℕ} (hi : i < Q.baseCount) :
    (invsOf n S base)[i]!.size = (Q.levelSteps i).length := by
  rw [invsOf_getElem (n := n) (S := S) (hA.base_size ▸ hi), hA.levelSteps_eq hF (Nat.le_of_lt hi),
    levInvSteps]
  simp

theorem prep_steps {i : ℕ} (hi : i < Q.baseCount) {j : ℕ} (hj : j < (Q.levelSteps i).length) :
    PRep n ((stepsOf n S base)[i]!)[j]! ((Q.levelSteps i)[j]) := by
  have hj' := hj
  rw [hA.levelSteps_eq hF (Nat.le_of_lt hi)] at hj'
  set idx := levIdx S base i with hidx
  have hsz : j < (stepsOf n S base)[i]!.size := by rw [hA.steps_size hF hi]; exact hj
  rw [getElem!_pos ((stepsOf n S base)[i]!) j hsz]
  simp only [List.length_append, List.length_map] at hj'
  have e1 : (Q.levelSteps i)[j] =
      (idx.map (strongAt Q) ++ idx.map fun j => (strongAt Q j)⁻¹)[j]'(by
        simpa [hA.levelSteps_eq hF (Nat.le_of_lt hi)] using hj) := by
    simp only [hA.levelSteps_eq hF (Nat.le_of_lt hi), idx]
  rw [e1]
  have hst := stepsOf_getElem (n := n) (S := S) (hA.base_size ▸ hi)
  by_cases hlt : j < idx.length
  · rw [List.getElem_append_left (by simpa using hlt)]
    simp only [List.getElem_map]
    have : ((stepsOf n S base)[i]!)[j] = S[idx[j]]! := by
      simp only [hst, levSteps, ← hidx]
      rw [Array.getElem_append_left (by simpa using hlt)]
      simp
    rw [this]
    exact hA.prep_strong hF _ (levIdx_lt (List.getElem_mem hlt))
  · have hle : idx.length ≤ j := by omega
    rw [List.getElem_append_right (by simpa using hle)]
    simp only [List.getElem_map, List.length_map]
    have hk : j - idx.length < idx.length := by omega
    have : ((stepsOf n S base)[i]!)[j] = (pinvs n S)[idx[j - idx.length]]! := by
      simp only [hst, levSteps, ← hidx]
      rw [Array.getElem_append_right (by simpa using hle)]
      simp
    rw [this]
    exact hA.prep_strongInv hF (levIdx_lt (List.getElem_mem hk))

theorem prep_invSteps {i : ℕ} (hi : i < Q.baseCount) {j : ℕ}
    (hj : j < (Q.levelSteps i).length) :
    PRep n ((invsOf n S base)[i]!)[j]! ((Q.levelSteps i)[j])⁻¹ := by
  have hj' := hj
  rw [hA.levelSteps_eq hF (Nat.le_of_lt hi)] at hj'
  set idx := levIdx S base i with hidx
  have hsz : j < (invsOf n S base)[i]!.size := by rw [hA.invs_size hF hi]; exact hj
  rw [getElem!_pos ((invsOf n S base)[i]!) j hsz]
  simp only [List.length_append, List.length_map] at hj'
  have e1 : (Q.levelSteps i)[j] =
      (idx.map (strongAt Q) ++ idx.map fun j => (strongAt Q j)⁻¹)[j]'(by
        simpa [hA.levelSteps_eq hF (Nat.le_of_lt hi)] using hj) := by
    simp only [hA.levelSteps_eq hF (Nat.le_of_lt hi), idx]
  rw [e1]
  have hst := invsOf_getElem (n := n) (S := S) (hA.base_size ▸ hi)
  by_cases hlt : j < idx.length
  · rw [List.getElem_append_left (by simpa using hlt)]
    simp only [List.getElem_map]
    have : ((invsOf n S base)[i]!)[j] = (pinvs n S)[idx[j]]! := by
      simp only [hst, levInvSteps, ← hidx]
      rw [Array.getElem_append_left (by simpa using hlt)]
      simp
    rw [this]
    exact hA.prep_strongInv hF (levIdx_lt (List.getElem_mem hlt))
  · have hle : idx.length ≤ j := by omega
    rw [List.getElem_append_right (by simpa using hle)]
    simp only [List.getElem_map, List.length_map, inv_inv]
    have hk : j - idx.length < idx.length := by omega
    have : ((invsOf n S base)[i]!)[j] = S[idx[j - idx.length]]! := by
      simp only [hst, levInvSteps, ← hidx]
      rw [Array.getElem_append_right (by simpa using hle)]
      simp
    rw [this]
    exact hA.prep_strong hF _ (levIdx_lt (List.getElem_mem hk))

end Facts

end CArrays

structure CLevelFacts (n root : ℕ) (steps : Array (Array ℕ)) (L : CLevel) : Prop where
  pos : 0 < L.pts.size
  le : L.pts.size ≤ n
  root : L.pts[0]! = root
  pts_lt : ∀ k < L.pts.size, L.pts[k]! < n
  pos_pts : ∀ k < L.pts.size, L.pos[L.pts[k]!]! = k
  pts_pos : ∀ z < n, L.pos[z]! < L.pts.size → L.pts[L.pos[z]!]! = z
  par_lt : ∀ k < L.pts.size, 0 < k → L.par[k]! < k
  lab_lt : ∀ k < L.pts.size, 0 < k → L.lab[k]! < steps.size
  edge : ∀ k < L.pts.size, 0 < k → (steps[L.lab[k]!]!)[L.pts[L.par[k]!]!]! = L.pts[k]!
  mono : ∀ k < L.pts.size, 0 < k → k + 1 < L.pts.size →
    plexLt L.par[k]! L.lab[k]! L.par[k + 1]! L.lab[k + 1]! = true
  closed : ∀ h < L.pts.size, ∀ j < steps.size,
    L.pos[(steps[j]!)[L.pts[h]!]!]! < L.pts.size ∧
      (L.pos[(steps[j]!)[L.pts[h]!]!]! = 0 ∨
        plexLt h j L.par[L.pos[(steps[j]!)[L.pts[h]!]!]!]!
          L.lab[L.pos[(steps[j]!)[L.pts[h]!]!]!]! = false)

theorem clevelFacts_of_clevelOK {root : ℕ} {steps : Array (Array ℕ)} {L : CLevel}
    (h : clevelOK n root steps L = true) : CLevelFacts n root steps L := by
  simp only [clevelOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨h1, h2, h3, fun k hk => ?_, fun k hk => ?_, fun z hz hzm => ?_, fun k hk hk0 => ?_,
    fun k hk hk0 => ?_, fun k hk hk0 => ?_, fun k hk hk0 hk1 => ?_, fun h hh j hj => ?_⟩
  · exact (by simpa [Bool.and_eq_true] using allBelowN_spec h4 hk : _ ∧ _).1
  · exact (by simpa [Bool.and_eq_true] using allBelowN_spec h4 hk : _ ∧ _).2
  · have := allBelowN_spec h5 hz
    simpa [hzm] using this
  · have := allBelowN_spec h6 hk
    simp only [show k ≠ 0 by omega, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
      decide_eq_true_eq, false_or] at this
    exact this.1.1
  · have := allBelowN_spec h6 hk
    simp only [show k ≠ 0 by omega, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
      decide_eq_true_eq, false_or] at this
    exact this.1.2
  · have := allBelowN_spec h6 hk
    simp only [show k ≠ 0 by omega, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
      decide_eq_true_eq, false_or] at this
    exact this.2
  · have := allBelowN_spec h7 hk
    simpa [show k ≠ 0 by omega, hk1] using this
  · have := allBelowN_spec (allBelowN_spec h8 hh) hj
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq,
      Bool.not_eq_true'] at this
    exact this

@[expose] def pathT (steps : List (Equiv.Perm (Fin n))) (par lab : ℕ → ℕ) (k : ℕ) :
    Equiv.Perm (Fin n) :=
  if _h : 0 < k ∧ par k < k then steps.getD (lab k) 1 * pathT steps par lab (par k) else 1
termination_by k
decreasing_by exact _h.2

theorem pathT_zero (steps : List (Equiv.Perm (Fin n))) (par lab : ℕ → ℕ) :
    pathT steps par lab 0 = 1 := by
  rw [pathT]
  simp

theorem pathT_step (steps : List (Equiv.Perm (Fin n))) (par lab : ℕ → ℕ) {k : ℕ} (hk : 0 < k)
    (hp : par k < k) :
    pathT steps par lab k = steps.getD (lab k) 1 * pathT steps par lab (par k) := by
  rw [pathT]
  simp [hk, hp]

namespace CArrays

variable {Q : RawSchreierDatum n} {m : ℕ} {S : Array (Array ℕ)} {base : Array ℕ}
  {W : Array (List ℤ)} {pts bidx : Array ℕ} {full : Bool} {chunks : ℕ}

abbrev lev (n : ℕ) (S : Array (Array ℕ)) (base : Array ℕ) (i : ℕ) : CLevel :=
  (levelsOf n S base)[i]!

@[expose] def levPts (Q : RawSchreierDatum n) (S : Array (Array ℕ)) (base : Array ℕ)
    (i k : ℕ) : Fin n :=
  toFin Q (lev n S base i).pts[k]!

@[expose] def levT (Q : RawSchreierDatum n) (S : Array (Array ℕ)) (base : Array ℕ) (i k : ℕ) :
    Equiv.Perm (Fin n) :=
  pathT (Q.levelSteps i) (fun k => (lev n S base i).par[k]!) (fun k => (lev n S base i).lab[k]!) k

theorem levelsOf_size : (levelsOf n S base).size = base.size := by simp [levelsOf, cLevels]

theorem levelsOf_getElem {i : ℕ} (hi : i < base.size) :
    (levelsOf n S base)[i]! = cbfs n base[i]! (stepsOf n S base)[i]! := by
  rw [levelsOf, cLevels, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

section Facts

variable (hA : CArrays Q m S base W) (hF : CChainFacts n m S base W pts bidx full chunks)
include hA hF

theorem levelFacts {i : ℕ} (hi : i < Q.baseCount) :
    CLevelFacts n base[i]! (stepsOf n S base)[i]! (lev n S base i) :=
  clevelFacts_of_clevelOK (hF.level i (hA.base_size ▸ hi))

theorem levPts_val {i k : ℕ} (hi : i < Q.baseCount) (hk : k < (lev n S base i).pts.size) :
    ((levPts Q S base i k : Fin n) : ℕ) = (lev n S base i).pts[k]! := by
  rw [levPts, toFin_eq Q ((hA.levelFacts hF hi).pts_lt k hk)]

theorem levT_step {i k : ℕ} (hi : i < Q.baseCount) (hk0 : 0 < k)
    (hk : k < (lev n S base i).pts.size) :
    levT Q S base i k = (Q.levelSteps i)[(lev n S base i).lab[k]!]'(by
        rw [← hA.steps_size hF hi]; exact (hA.levelFacts hF hi).lab_lt k hk hk0) *
      levT Q S base i ((lev n S base i).par[k]!) := by
  rw [levT, pathT_step _ _ _ hk0 ((hA.levelFacts hF hi).par_lt k hk hk0), List.getD_eq_getElem]
  rfl

theorem bfsCert {i : ℕ} (hi : i < Q.baseCount) :
    BFSCert (Q.levelSteps i) (Q.base.get ⟨i, hi⟩) (lev n S base i).pts.size (levPts Q S base i)
      (fun k => (lev n S base i).par[k]!) (fun k => (lev n S base i).lab[k]!)
      (levT Q S base i) := by
  have F := hA.levelFacts hF hi
  have hsz := hA.steps_size hF hi
  have hlab : ∀ k, 0 < k → k < (lev n S base i).pts.size →
      (lev n S base i).lab[k]! < (Q.levelSteps i).length :=
    fun k hk0 hk => hsz ▸ F.lab_lt k hk hk0
  refine ⟨F.pos, ?_, pathT_zero _ _ _, ?_, fun k hk0 hk => F.par_lt k hk hk0, hlab, ?_,
    fun k hk0 hk => hA.levT_step hF hi hk0 hk, ?_, ?_⟩
  · apply Fin.ext
    rw [hA.levPts_val hF hi F.pos, F.root, hA.base_val ⟨i, hi⟩]
  · intro a ha b hb hab
    have h1 := congrArg Fin.val hab
    rw [hA.levPts_val hF hi ha, hA.levPts_val hF hi hb] at h1
    rw [← F.pos_pts a ha, ← F.pos_pts b hb, h1]
  · intro k hk0 hk
    have hp := F.par_lt k hk hk0
    apply Fin.ext
    rw [hA.levPts_val hF hi hk, ← F.edge k hk hk0,
      (hA.prep_steps hF hi (hlab k hk0 hk)).apply (F.pts_lt _ (by omega))]
    congr 2
    exact Fin.ext (hA.levPts_val hF hi (by omega))
  · intro k hk0 hk1
    have := F.mono k (by omega) hk0 hk1
    simp only [plexLt, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true,
      beq_iff_eq] at this
    exact this
  · intro h hh j hj
    have hj' : j < (stepsOf n S base)[i]!.size := by rw [hsz]; exact hj
    obtain ⟨hk, hle⟩ := F.closed h hh j hj'
    set z := (((stepsOf n S base)[i]!)[j]!)[(lev n S base i).pts[h]!]! with hz
    have hzn : z < n := by
      rw [hz, (hA.prep_steps hF hi hj).apply (F.pts_lt h hh)]
      exact Fin.isLt _
    refine ⟨(lev n S base i).pos[z]!, hk, ?_, ?_⟩
    · apply Fin.ext
      rw [hA.levPts_val hF hi hk, F.pts_pos z hzn hk, hz,
        (hA.prep_steps hF hi hj).apply (F.pts_lt h hh)]
      congr 2
      exact Fin.ext (hA.levPts_val hF hi hh).symm
    · rcases hle with h0 | hl
      · exact Or.inl h0
      · right
        intro hlex
        simp only [plexLt, Bool.or_eq_false_iff, decide_eq_false_iff_not,
          Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hl
        unfold LexLt at hlex
        omega

theorem orbitSearch_eq {i : ℕ} (hi : i < Q.baseCount) :
    Q.orbitSearch ⟨i, hi⟩ =
      ⟨(List.range (lev n S base i).pts.size).map fun k =>
        (levPts Q S base i k, levT Q S base i k), []⟩ :=
  (hA.bfsCert hF hi).run_initial_eq

theorem transversal_of_lt {i : ℕ} (hi : i < Q.baseCount) {k : ℕ}
    (hk : k < (lev n S base i).pts.size) :
    (Q.orbitSearch ⟨i, hi⟩).transversal? (levPts Q S base i k) = some (levT Q S base i k) := by
  rw [hA.orbitSearch_eq hF hi]
  exact (hA.bfsCert hF hi).lookup_recs_of_lt le_rfl hk

theorem transversal_eq_none {i : ℕ} (hi : i < Q.baseCount) {z : Fin n}
    (hz : ¬ (lev n S base i).pos[(z : ℕ)]! < (lev n S base i).pts.size) :
    (Q.orbitSearch ⟨i, hi⟩).transversal? z = none := by
  rw [hA.orbitSearch_eq hF hi]
  change List.lookup z ((List.range (lev n S base i).pts.size).map fun k =>
    (levPts Q S base i k, levT Q S base i k)) = none
  rw [List.lookup_eq_none_iff]
  intro p hp
  simp only [List.mem_map, List.mem_range] at hp
  obtain ⟨k, hk, rfl⟩ := hp
  rw [bne_iff_ne]
  intro he
  apply hz
  rw [he, hA.levPts_val hF hi hk, (hA.levelFacts hF hi).pos_pts k hk]
  exact hk

theorem orbitSize_eq {i : ℕ} (hi : i < Q.baseCount) :
    Q.orbitSize ⟨i, hi⟩ = (lev n S base i).pts.size := by
  rw [RawSchreierDatum.orbitSize, hA.orbitSearch_eq hF hi]
  simp [SchreierOrbitState.keys]

theorem trApp_eq {i : ℕ} (hi : i < Q.baseCount) : ∀ fuel k, k < fuel →
    k < (lev n S base i).pts.size → ∀ p (hp : p < n),
      trApp (stepsOf n S base)[i]! (lev n S base i) fuel k p =
        (levT Q S base i k ⟨p, hp⟩ : ℕ) := by
  have F := hA.levelFacts hF hi
  intro fuel
  induction fuel with
  | zero => intro k hk; omega
  | succ fuel ih =>
    intro k hk hkm p hp
    rw [trApp]
    by_cases hk0 : k = 0
    · subst hk0
      simp [levT, pathT_zero]
    · have hpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hpar := F.par_lt k hkm hpos
      simp only [beq_iff_eq, hk0, ↓reduceIte]
      have hlab : (lev n S base i).lab[k]! < (Q.levelSteps i).length := by
        rw [← hA.steps_size hF hi]; exact F.lab_lt k hkm hpos
      rw [ih _ (by omega) (by omega) p hp,
        (hA.prep_steps hF hi hlab).apply (Fin.isLt _), hA.levT_step hF hi hpos hkm,
        Equiv.Perm.mul_apply]

theorem trInvApp_eq {i : ℕ} (hi : i < Q.baseCount) : ∀ fuel k, k < fuel →
    k < (lev n S base i).pts.size → ∀ p (hp : p < n),
      trInvApp (invsOf n S base)[i]! (lev n S base i) fuel k p =
        ((levT Q S base i k)⁻¹ ⟨p, hp⟩ : ℕ) := by
  have F := hA.levelFacts hF hi
  intro fuel
  induction fuel with
  | zero => intro k hk; omega
  | succ fuel ih =>
    intro k hk hkm p hp
    rw [trInvApp]
    by_cases hk0 : k = 0
    · subst hk0
      simp [levT, pathT_zero]
    · have hpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hpar := F.par_lt k hkm hpos
      simp only [beq_iff_eq, hk0, ↓reduceIte]
      have hlab : (lev n S base i).lab[k]! < (Q.levelSteps i).length := by
        rw [← hA.steps_size hF hi]; exact F.lab_lt k hkm hpos
      have hrep := hA.prep_invSteps hF hi hlab
      rw [hrep.apply hp, ih _ (by omega) (by omega) _ (Fin.isLt _), hA.levT_step hF hi hpos hkm,
        _root_.mul_inv_rev, Equiv.Perm.mul_apply]

end Facts

theorem schreierSiftSucceeds_cons_some (b : Fin n) (q : SchreierOrbitState n)
    (levels : List (Fin n × SchreierOrbitState n)) (h t : Equiv.Perm (Fin n))
    (ht : q.transversal? (h b) = some t) :
    schreierSiftSucceeds ((b, q) :: levels) h = schreierSiftSucceeds levels (t⁻¹ * h) := by
  unfold schreierSiftSucceeds
  rw [schreierSiftResidual_available b q levels h t ht]

theorem schreierPointSiftSucceeds_cons_some (b : Fin n) (q : SchreierOrbitState n)
    (levels : List (Fin n × SchreierOrbitState n)) (h t : Equiv.Perm (Fin n))
    (ht : q.transversal? (h b) = some t) :
    schreierPointSiftSucceeds ((b, q) :: levels) h =
      schreierPointSiftSucceeds levels (t⁻¹ * h) := by
  unfold schreierPointSiftSucceeds
  rw [schreierSiftResidual_available b q levels h t ht]

section Facts

variable (hA : CArrays Q m S base W) (hF : CChainFacts n m S base W pts bidx full chunks)
include hA hF

theorem psift_sound (hcover : full = true → ∀ x : Fin n, ∃ t < pts.size, pts[t]! = x) :
    ∀ d l, l + d = Q.baseCount → ∀ (img : Array ℕ) (G : Equiv.Perm (Fin n)),
      img.size = pts.size → (∀ t (ht : t < pts.size), img[t]! = (G ⟨pts[t]!, hF.pts_lt t ht⟩ : ℕ)) →
      psift (levelsOf n S base) (invsOf n S base) pts bidx full l img = true →
      schreierPointSiftSucceeds (Q.siftLevels Q.orbitTables l) G = true ∧
        (full = true → schreierSiftSucceeds (Q.siftLevels Q.orbitTables l) G = true) := by
  intro d
  induction d with
  | zero =>
    intro l hl img G hsz hG hs
    have hle : l = Q.baseCount := by omega
    subst hle
    have hnil : Q.siftLevels Q.orbitTables Q.baseCount = [] := by
      simp [RawSchreierDatum.siftLevels]
    rw [hnil]
    refine ⟨by simp [schreierPointSiftSucceeds, schreierSiftResidual], fun hfull => ?_⟩
    rw [psift, dite_eq_right_of_eq_false
      (eq_false (by rw [levelsOf_size, hA.base_size]; omega))] at hs
    rw [hfull, Bool.not_true, Bool.false_or, allBelowN_iff] at hs
    rw [schreierSiftSucceeds_nil]
    refine Equiv.ext fun x => ?_
    obtain ⟨t, ht, hx⟩ := hcover hfull x
    have h1 := hs t ht
    rw [beq_iff_eq, hG t ht] at h1
    apply Fin.ext
    have hx' : (⟨pts[t]!, hF.pts_lt t ht⟩ : Fin n) = x := Fin.ext hx
    rw [← hx', Equiv.Perm.coe_one, id_eq]
    exact h1
  | succ d ih =>
    intro l hl img G hsz hG hs
    have hlb : l < Q.baseCount := by omega
    have hls : l < (levelsOf n S base).size := by
      rw [levelsOf_size, hA.base_size]; exact hlb
    rw [psift, dite_eq_left_of_eq_true (eq_true hls)] at hs
    have hlev : (levelsOf n S base)[l] = lev n S base l := by
      rw [lev, getElem!_pos _ l hls]
    rw [hlev] at hs
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
    obtain ⟨hk, hs⟩ := hs
    have hcons := Q.siftLevels_cons Q.orbitTables ⟨l, hlb⟩
    simp only at hcons
    rw [hcons, RawSchreierDatum.orbitTables_get]
    set b := Q.base.get ⟨l, hlb⟩ with hb
    have hbv : (b : ℕ) = base[l]! := hA.base_val ⟨l, hlb⟩
    have hbidx := hF.bidx_ok l (hA.base_size ▸ hlb)
    have hgb : img[bidx[l]!]! = (G b : ℕ) := by
      rw [hG _ hbidx.1]
      congr 2
      exact Fin.ext (hbidx.2.trans hbv.symm)
    rw [hgb] at hk hs
    have hpts : levPts Q S base l ((lev n S base l).pos[(G b : ℕ)]!) = G b := by
      apply Fin.ext
      rw [hA.levPts_val hF hlb hk, (hA.levelFacts hF hlb).pts_pos _ (G b).2 hk]
    have ht := hA.transversal_of_lt hF hlb hk
    rw [hpts] at ht
    rw [schreierPointSiftSucceeds_cons_some _ _ _ _ _ ht,
      schreierSiftSucceeds_cons_some _ _ _ _ _ ht]
    refine ih (l + 1) (by omega) _ _ (by rw [Array.size_map, hsz]) (fun t htp => ?_) hs
    rw [getElem!_map' _ _ (by rw [hsz]; exact htp), hG t htp,
      hA.trInvApp_eq hF hlb _ _ hk hk _ (Fin.isLt _), Equiv.Perm.mul_apply]

end Facts

end CArrays

namespace CArrays

variable {Q : RawSchreierDatum n} {m : ℕ} {S : Array (Array ℕ)} {base : Array ℕ}
  {W : Array (List ℤ)} {pts bidx : Array ℕ} {full : Bool} {chunks : ℕ}

section Facts

variable (hA : CArrays Q m S base W) (hF : CChainFacts n m S base W pts bidx full chunks)
include hA hF

theorem schreierImgs_spec {i : ℕ} (hi : i < Q.baseCount) {h j : ℕ}
    (hh : h < (lev n S base i).pts.size) (hj : j < (Q.levelSteps i).length) {k : ℕ}
    (hk : k < (lev n S base i).pts.size) :
    (schreierImgs (stepsOf n S base)[i]! (invsOf n S base)[i]! (lev n S base i) pts h j k).size =
        pts.size ∧
      ∀ t (ht : t < pts.size),
        (schreierImgs (stepsOf n S base)[i]! (invsOf n S base)[i]! (lev n S base i) pts h j k)[t]! =
          (((levT Q S base i k)⁻¹ * (Q.levelSteps i)[j] * levT Q S base i h)
            ⟨pts[t]!, hF.pts_lt t ht⟩ : ℕ) := by
  refine ⟨by simp [schreierImgs], fun t ht => ?_⟩
  rw [schreierImgs, getElem!_map' _ _ ht, hA.trApp_eq hF hi _ _ hh hh _ (hF.pts_lt t ht),
    (hA.prep_steps hF hi hj).apply (Fin.isLt _), hA.trInvApp_eq hF hi _ _ hk hk _ (Fin.isLt _),
    Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]

theorem schreier (hc : 0 < chunks)
    (hcover : full = true → ∀ x : Fin n, ∃ t < pts.size, pts[t]! = x) :
    ∀ (i : Fin Q.baseCount) (x : Fin n) (tx : Equiv.Perm (Fin n)),
      (Q.orbitSearch i).transversal? x = some tx →
      ∀ s ∈ Q.levelSteps i.val, ∃ ty : Equiv.Perm (Fin n),
        (Q.orbitSearch i).transversal? (s x) = some ty ∧
        schreierPointSiftSucceeds (Q.siftLevels Q.orbitTables (i.val + 1)) (ty⁻¹ * s * tx) = true ∧
        (full = true → schreierSiftSucceeds (Q.siftLevels Q.orbitTables (i.val + 1))
          (ty⁻¹ * s * tx) = true) := by
  rintro ⟨i, hi⟩ x tx htx s hs
  rw [hA.orbitSearch_eq hF hi] at htx
  change List.lookup x ((List.range (lev n S base i).pts.size).map fun k =>
    (levPts Q S base i k, levT Q S base i k)) = some tx at htx
  obtain ⟨before, after, heq, -⟩ := List.lookup_eq_some_iff.1 htx
  have hmem : (x, tx) ∈ (List.range (lev n S base i).pts.size).map fun k =>
      (levPts Q S base i k, levT Q S base i k) := by
    rw [heq]
    simp
  simp only [List.mem_map, List.mem_range, Prod.mk.injEq] at hmem
  obtain ⟨h, hh, rfl, rfl⟩ := hmem
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
  have F := hA.levelFacts hF hi
  have hsz := hA.steps_size hF hi
  have hj' : j < (stepsOf n S base)[i]!.size := by rw [hsz]; exact hj
  have hrs := hA.prep_steps hF hi hj
  have hsch := hF.schreier i (hA.base_size ▸ hi)
  simp only [cschreierOK] at hsch
  have htest := parBelow_spec hc hsch h hh
  have htest' := allBelowN_spec htest hj'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at htest'
  obtain ⟨hk, hsift⟩ := htest'
  have hzv : (((stepsOf n S base)[i]!)[j]!)[(lev n S base i).pts[h]!]! =
      ((Q.levelSteps i)[j] (levPts Q S base i h) : ℕ) := by
    rw [hrs.apply (F.pts_lt h hh)]
    congr 2
    exact Fin.ext (hA.levPts_val hF hi hh).symm
  have hpts : levPts Q S base i
      ((lev n S base i).pos[(((stepsOf n S base)[i]!)[j]!)[(lev n S base i).pts[h]!]!]!) =
      (Q.levelSteps i)[j] (levPts Q S base i h) := by
    apply Fin.ext
    rw [hA.levPts_val hF hi hk, F.pts_pos _ (by rw [hzv]; exact Fin.isLt _) hk, hzv]
  set k := (lev n S base i).pos[(((stepsOf n S base)[i]!)[j]!)[(lev n S base i).pts[h]!]!]!
    with hkdef
  refine ⟨levT Q S base i k, ?_, ?_⟩
  · rw [← hpts]
    exact hA.transversal_of_lt hF hi hk
  · obtain ⟨hisz, himg⟩ := hA.schreierImgs_spec hF hi hh hj hk
    have hlev : (levelsOf n S base)[i]! = lev n S base i := rfl
    exact hA.psift_sound hF hcover (Q.baseCount - (i + 1)) (i + 1) (by omega) _ _ hisz himg hsift

end Facts

end CArrays

theorem validPointSchreier_of_pointChainOK {Q : RawSchreierDatum n} {m : ℕ}
    {S : Array (Array ℕ)} {base : Array ℕ} {W : Array (List ℤ)} (hA : CArrays Q m S base W)
    {chunks : ℕ} (hc : 0 < chunks) (h : pointChainOK n m S base W chunks = true) :
    ValidPointSchreier Q ∧ ∀ i : Fin Q.baseCount,
      Q.orbitSize i = (CArrays.lev n S base i).pts.size := by
  have hF := chainFacts h
  refine ⟨?_, fun i => hA.orbitSize_eq hF i.2⟩
  rw [validPointSchreier_iff]
  refine ⟨hA.initial, hA.words, fun i x tx htx s hs => ?_⟩
  obtain ⟨ty, hty, hpt, -⟩ := hA.schreier hF hc (by simp) i x tx htx s hs
  exact ⟨ty, hty, hpt⟩

theorem validSchreier_of_fullChainOK {Q : RawSchreierDatum n} {m : ℕ}
    {S : Array (Array ℕ)} {base : Array ℕ} {W : Array (List ℤ)} (hA : CArrays Q m S base W)
    {chunks : ℕ} (hc : 0 < chunks) (h : fullChainOK n m S base W chunks = true) :
    ValidSchreier Q ∧ ∀ i : Fin Q.baseCount,
      Q.orbitSize i = (CArrays.lev n S base i).pts.size := by
  have hF := chainFacts h
  refine ⟨?_, fun i => hA.orbitSize_eq hF i.2⟩
  have hcover : true = true → ∀ x : Fin n, ∃ t < (pid n).size, (pid n)[t]! = x := by
    intro _ x
    exact ⟨x, by simp [pid], by rw [pid_get x.2]⟩
  rw [validSchreier_iff]
  refine ⟨hA.initial, hA.words, fun s hs => ?_, fun i x tx htx s hs => ?_⟩
  · rw [hA.levelGenerators_eq hF le_rfl, List.mem_map] at hs
    obtain ⟨j, hj, rfl⟩ := hs
    have hjS := CArrays.levIdx_lt hj
    have hfix : pfixes base S[j]! base.size = true := by
      rw [levIdx, List.mem_filter] at hj
      rw [hA.base_size]
      exact hj.2
    exact (peq_iff (hA.prep_strong hF j hjS) prep_pid).1 (hF.terminal rfl j hjS hfix)
  · obtain ⟨ty, hty, -, hfs⟩ := hA.schreier hF hc hcover i x tx htx s hs
    exact ⟨ty, hty, hfs rfl⟩

end CFSG.ONSchreier
