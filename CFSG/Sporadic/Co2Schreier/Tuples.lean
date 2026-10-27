module

public import CFSG.Sporadic.Co2Schreier.Arrays
public import CFSG.Monster.B.Mathieu.SylowSound

public noncomputable section

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert

@[expose] def RepTuple (n : ℕ) (A : Array (Array ℕ)) (gs : List (Equiv.Perm (Fin n))) : Prop :=
  A.size = gs.length ∧ ∀ h < gs.length, Rep n A[h]! (gs.getD h 1)

theorem RepTuple.size_eq {n : ℕ} {A : Array (Array ℕ)} {gs : List (Equiv.Perm (Fin n))}
    (hA : RepTuple n A gs) : A.size = gs.length := hA.1

theorem RepTuple.rep {n : ℕ} {A : Array (Array ℕ)} {gs : List (Equiv.Perm (Fin n))}
    (hA : RepTuple n A gs) {h : ℕ} (hh : h < gs.length) : Rep n A[h]! (gs.getD h 1) := hA.2 h hh

theorem allInv_spec {A : Array (Array ℕ)} (h : allInv A = true) {j : ℕ} (hj : j < A.size) :
    isInvA 2300 A[j]! (invCand 2300 A[j]!) = true :=
  allLt_spec h hj

theorem RepTuple.word {A : Array (Array ℕ)} {gs : List (Equiv.Perm (Fin 2300))}
    (hA : RepTuple 2300 A gs) (hinv : allInv A = true) {w : List ℤ}
    (hw : lettersOK gs.length w = true) : Rep 2300 (wordArr A w) (wordValue gs w) := by
  have hS : ∀ h < gs.length, Rep 2300 A[h]! ((fun h => gs.getD h 1) h) := fun h hh => hA.2 h hh
  have hSinv : ∀ h < gs.length, Rep 2300 (rawInvs 2300 A)[h]! ((fun h => gs.getD h 1) h)⁻¹ := by
    intro h hh
    have hhA : h < A.size := hA.1 ▸ hh
    rw [rawInvs_get A hhA]
    exact rep_inv_of_isInvA (hA.2 h hh) (allInv_spec hinv hhA)
  have key := rep_wordA (gs := fun h => gs.getD h 1) (j := gs.length) hS hSinv w hw
  rw [evalWord_toLetters gs w hw] at key
  exact key

theorem RepTuple.mapWords {A : Array (Array ℕ)} {gs : List (Equiv.Perm (Fin 2300))}
    (hA : RepTuple 2300 A gs) (hinv : allInv A = true) {ws : List (List ℤ)}
    (hws : ∀ w ∈ ws, lettersOK gs.length w = true) :
    RepTuple 2300 (ws.map (wordArr A)).toArray (ws.map (wordValue gs)) := by
  refine ⟨by simp, fun h hh => ?_⟩
  have hh' : h < ws.length := by simpa using hh
  have e1 : (ws.map (wordArr A)).toArray[h]! = wordArr A ws[h] := by
    rw [getElem!_pos _ h (by simpa using hh')]
    simp
  have e2 : (ws.map (wordValue gs)).getD h 1 = wordValue gs ws[h] := by
    rw [List.getD_eq_getElem _ _ (by simpa using hh')]
    simp
  rw [e1, e2]
  exact hA.word hinv (hws _ (List.getElem_mem hh'))

theorem RepTuple.append {n : ℕ} {A B : Array (Array ℕ)} {gs hs : List (Equiv.Perm (Fin n))}
    (hA : RepTuple n A gs) (hB : RepTuple n B hs) : RepTuple n (A ++ B) (gs ++ hs) := by
  refine ⟨by simp [hA.1, hB.1], fun h hh => ?_⟩
  rw [List.length_append] at hh
  by_cases h1 : h < gs.length
  · have e1 : (A ++ B)[h]! = A[h]! := by
      rw [getElem!_pos _ h (by simp [hA.1, hB.1]; omega),
        getElem!_pos _ h (by rw [hA.1]; exact h1), Array.getElem_append_left]
    have e2 : (gs ++ hs).getD h 1 = gs.getD h 1 := by
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ h1,
        List.getElem_append_left]
    rw [e1, e2]
    exact hA.2 h h1
  · have h2 : h - gs.length < hs.length := by omega
    have e1 : (A ++ B)[h]! = B[h - gs.length]! := by
      rw [getElem!_pos _ h (by simp [hA.1, hB.1]; omega),
        getElem!_pos _ (h - gs.length) (by rw [hB.1]; exact h2),
        Array.getElem_append_right (by rw [hA.1]; omega)]
      simp [hA.1]
    have e2 : (gs ++ hs).getD h 1 = hs.getD (h - gs.length) 1 := by
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ h2,
        List.getElem_append_right (by omega)]
    rw [e1, e2]
    exact hB.2 _ h2

theorem RepTuple.conj {A : Array (Array ℕ)} {gs : List (Equiv.Perm (Fin 2300))}
    (hA : RepTuple 2300 A gs) {t : Array ℕ} {g : Equiv.Perm (Fin 2300)} (ht : Rep 2300 t g)
    (hti : isInvA 2300 t (invCand 2300 t) = true) :
    RepTuple 2300 (A.map fun x => compA 2300 (compA 2300 t x) (invCand 2300 t))
      (gs.map fun x => g * x * g⁻¹) := by
  refine ⟨by simp [hA.1], fun h hh => ?_⟩
  have hh' : h < gs.length := by simpa using hh
  have hhA : h < A.size := hA.1 ▸ hh'
  have e1 : (A.map fun x => compA 2300 (compA 2300 t x) (invCand 2300 t))[h]! =
      compA 2300 (compA 2300 t A[h]!) (invCand 2300 t) := by
    rw [getElem!_pos _ h (by simpa using hhA), Array.getElem_map, getElem!_pos A h hhA]
  have e2 : (gs.map fun x => g * x * g⁻¹).getD h 1 = g * gs.getD h 1 * g⁻¹ := by
    rw [List.getD_eq_getElem _ _ (by simpa using hh'), List.getElem_map,
      List.getD_eq_getElem _ _ hh']
  rw [e1, e2]
  exact rep_compA (rep_compA ht (hA.2 h hh')) (rep_inv_of_isInvA ht hti)

theorem extendArrs_cons (A : Array (Array ℕ)) (w : List ℤ) (ds : List (List ℤ)) :
    extendArrs A (w :: ds) = extendArrs (A.push (wordArr A w)) ds := rfl

theorem extendTuple_cons {G : Type*} [Group G] (gs : List G) (w : List ℤ) (ds : List (List ℤ)) :
    extendTuple gs (w :: ds) = extendTuple (gs ++ [wordValue gs w]) ds := rfl

theorem extendTuple_length {G : Type*} [Group G] :
    ∀ (gs : List G) (ds : List (List ℤ)), (extendTuple gs ds).length = gs.length + ds.length
  | gs, [] => rfl
  | gs, w :: ds => by
    rw [extendTuple_cons, extendTuple_length, List.length_append, List.length_cons]
    simp
    omega

theorem extendArrs_size :
    ∀ (A : Array (Array ℕ)) (ds : List (List ℤ)), (extendArrs A ds).size = A.size + ds.length
  | A, [] => rfl
  | A, w :: ds => by
    rw [extendArrs_cons, extendArrs_size, Array.size_push, List.length_cons]
    omega

theorem extendArrs_get_lt :
    ∀ (A : Array (Array ℕ)) (ds : List (List ℤ)) {i : ℕ}, i < A.size →
      (extendArrs A ds)[i]! = A[i]!
  | A, [], _, _ => rfl
  | A, w :: ds, i, hi => by
    rw [extendArrs_cons, extendArrs_get_lt _ ds (by simp; omega),
      getElem!_pos _ i (by simp; omega), getElem!_pos A i hi, Array.getElem_push_lt]

theorem allInv_of_extendArrs {A : Array (Array ℕ)} {ds : List (List ℤ)}
    (h : allInv (extendArrs A ds) = true) : allInv A = true := by
  rw [allInv, allLt_iff]
  intro j hj
  have := allInv_spec h (j := j) (by rw [extendArrs_size]; omega)
  rwa [extendArrs_get_lt A ds hj] at this

theorem extWordsOK_cons {k : ℕ} {w : List ℤ} {ds : List (List ℤ)} :
    extWordsOK k (w :: ds) = true ↔ lettersOK k w = true ∧ extWordsOK (k + 1) ds = true := by
  simp only [extWordsOK, List.length_cons, List.range_succ_eq_map, List.all_cons,
    List.all_map, Bool.and_eq_true, List.all_eq_true, Function.comp_apply, List.getD_cons_zero,
    List.getD_cons_succ, add_zero]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun j hj => by rw [show k + 1 + j = k + (j + 1) by omega]; exact h2 j hj⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun j hj => by rw [show k + (j + 1) = k + 1 + j by omega]; exact h2 j hj⟩

theorem RepTuple.extend :
    ∀ {A : Array (Array ℕ)} {gs : List (Equiv.Perm (Fin 2300))} {ds : List (List ℤ)},
      RepTuple 2300 A gs → extWordsOK gs.length ds = true → allInv (extendArrs A ds) = true →
        RepTuple 2300 (extendArrs A ds) (extendTuple gs ds)
  | A, gs, [], hA, _, _ => hA
  | A, gs, w :: ds, hA, hds, hinv => by
    rw [extendArrs_cons, extendTuple_cons]
    obtain ⟨hw, hds'⟩ := extWordsOK_cons.1 hds
    have hinvA : allInv A = true := allInv_of_extendArrs (ds := w :: ds) hinv
    have hA' : RepTuple 2300 (A.push (wordArr A w)) (gs ++ [wordValue gs w]) := by
      have h1 : RepTuple 2300 #[wordArr A w] [wordValue gs w] :=
        ⟨rfl, fun h hh => by
          have h0 : h = 0 := by simpa using hh
          subst h0
          exact hA.word hinvA hw⟩
      have := hA.append h1
      simpa using this
    refine RepTuple.extend hA' ?_ hinv
    rwa [List.length_append, List.length_singleton]

theorem mem_iff_exists_getD {α : Type*} {l : List α} {d : α} {x : α} :
    x ∈ l ↔ ∃ k < l.length, l.getD k d = x := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, List.getD_eq_getElem _ _ hk⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, (List.getD_eq_getElem _ _ hk).symm⟩

theorem originalSubgroup_rawOfArrays_of_eqA {n : ℕ} {O S : Array (Array ℕ)} {base : Array ℕ}
    {W : Array (List ℤ)} {hn : 1 ≤ n} {hle : O.size ≤ S.size}
    {hlt : ∀ i < base.size, base[i]! < n} {hnd : base.toList.Nodup} {A : Array (Array ℕ)}
    {gs : List (Equiv.Perm (Fin n))} (hA : RepTuple n A gs) (hO : O.size = gs.length)
    (hrep : ∀ k < O.size, Rep n O[k]! (permOfArr n O[k]!))
    (heq : ∀ k < O.size, eqA n O[k]! A[k]! = true) :
    (rawOfArrays n O S base W hn hle hlt hnd).originalSubgroup =
      Subgroup.closure {g | g ∈ gs} := by
  rw [RawSchreierDatum.originalSubgroup]
  congr 1
  ext g
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, original_toList_rawOfArrays,
    mem_iff_exists_getD (d := 1)]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hO ▸ hk, (eq_of_eqA (hrep k hk) (hA.2 k (hO ▸ hk)) (heq k hk)).symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hO ▸ hk, eq_of_eqA (hrep k (hO ▸ hk)) (hA.2 k hk) (heq k (hO ▸ hk))⟩

theorem extendTuple_mem {G : Type*} [Group G] (H : Subgroup G) :
    ∀ (gs : List G) (ds : List (List ℤ)), (∀ g ∈ gs, g ∈ H) → ∀ g ∈ extendTuple gs ds, g ∈ H
  | gs, [], h => h
  | gs, w :: ds, h => by
    rw [extendTuple_cons]
    refine extendTuple_mem H _ ds fun g hg => ?_
    rcases List.mem_append.1 hg with hg | hg
    · exact h g hg
    · rw [List.mem_singleton.1 hg]
      exact wordValue_mem gs H h w

end CFSG.Sporadic.Co2Schreier
