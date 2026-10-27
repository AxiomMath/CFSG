module

public import CFSG.Sporadic.J4.QT2LocVLCheck
public import CFSG.Sporadic.J4.QT2LocX0NMainBase

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A Matrix

theorem eqRows_of_mx {A B : Array V2} (hA : wfRows A = true) (hB : wfRows B = true)
    (h : rowsMatrix A = rowsMatrix B) : eqRows A B = true :=
  eqRows_iff.2 (eq_of_rowsMatrix_eq hA hB h)

@[expose] noncomputable def vlElt (p : List Nat × Nat) : J :=
  eta uJ 11 p.2 * el5 (vlLiftWord p.1)

theorem vlEtaTab_get {e : ℕ} (he : e < 2048) : vlEtaTab[e]! = etaE e := by
  unfold vlEtaTab etaE
  rw [getElem!_pos _ e (by simp [he])]
  simp

theorem vlLiftRows_eq
    {y : List Nat} (hy : y ∈ vlTables) : vlLiftRows y = wR (vlLiftWord y) := by
  have h := chkVlLiftWf_true
  unfold chkVlLiftWf at h
  rw [List.all_eq_true] at h
  have := h y hy
  rw [Bool.and_eq_true] at this
  exact eqRows_iff.1 this.2

theorem Mx_vlElt
    (hM : MatFacts) {p : List Nat × Nat} (hy : p.1 ∈ vlTables) (hp : p.2 < 2048) :
    Mx (vlElt p) = rowsMatrix (vlT p) := by
  unfold vlElt vlT
  rw [vlLiftRows_eq hy, map_mul, Mx_eta hM 11 le_rfl, QT2A.Mx_el5 hM, vlEtaTab_get hp,
    ← rowsMatrix_mulRows]
  rfl

theorem wfRows_vlT
    {p : List Nat × Nat} (hp1 : p.1 ∈ vlTables) (hp2 : p.2 < 2048) :
    wfRows (vlT p) = true := by
  unfold vlT
  refine wfRows_mulRows ?_ ?_
  · have h := chkVlEta_true
    unfold chkVlEta at h
    simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true] at h
    obtain ⟨⟨hsz, hall⟩, -⟩ := h
    rw [getElem!_pos _ p.2 (by omega)]
    exact hall p.2 (by omega)
  · have h := chkVlLiftWf_true
    unfold chkVlLiftWf at h
    rw [List.all_eq_true] at h
    have := h _ hp1
    rw [Bool.and_eq_true] at this
    exact this.1

theorem wfRows_idRows : wfRows idRows = true := by
  have h := chkVlEta_true
  unfold chkVlEta at h
  simp only [Bool.and_eq_true] at h
  exact h.2

theorem wfRows_vlXiConj
    {T : Array V2} (hT : wfRows T = true) : wfRows (vlXiConj T) = true :=
  wfRows_mulRows (wfRows_mulRows x0GenRows_zero_wf hT) x0InvRows_zero_wf

theorem Mx_vlXiConj
    (hM : MatFacts) {t : J} {T : Array V2} (hT : Mx t = rowsMatrix T) :
    Mx (fiveElt * t * fiveElt⁻¹) = rowsMatrix (vlXiConj T) := by
  unfold vlXiConj
  rw [map_mul, map_mul, hT, Mx_fiveElt hM, Mx_fiveElt_inv hM, rowsMatrix_mulRows,
    rowsMatrix_mulRows]

@[expose] noncomputable def vlCj (t : J) : ℕ → J
  | 0 => t
  | n + 1 => fiveElt * vlCj t n * fiveElt⁻¹

theorem vlCj_eq (t : J) (n : ℕ) : vlCj t n = fiveElt ^ n * t * (fiveElt ^ n)⁻¹ := by
  induction n with
  | zero => simp [vlCj]
  | succ n ih => rw [vlCj, ih, conj_step]

theorem Mx_vlCj
    (hM : MatFacts) {t : J} {T : Array V2} (hT : Mx t = rowsMatrix T) :
    Mx (vlCj t 0) = rowsMatrix (vlConjs T)[0]! ∧ Mx (vlCj t 1) = rowsMatrix (vlConjs T)[1]! ∧
      Mx (vlCj t 2) = rowsMatrix (vlConjs T)[2]! ∧ Mx (vlCj t 3) = rowsMatrix (vlConjs T)[3]! := by
  have h1 : Mx (vlCj t 1) = rowsMatrix (vlXiConj T) := Mx_vlXiConj hM hT
  have h2 : Mx (vlCj t 2) = rowsMatrix (vlXiConj (vlXiConj T)) := Mx_vlXiConj hM h1
  have h3 : Mx (vlCj t 3) = rowsMatrix (vlXiConj (vlXiConj (vlXiConj T))) := Mx_vlXiConj hM h2
  exact ⟨hT, h1, h2, h3⟩

theorem wfRows_vlConjs {T : Array V2} (hT : wfRows T = true) :
    ∀ i < 4, wfRows (vlConjs T)[i]! = true := by
  have h1 := wfRows_vlXiConj hT
  have h2 := wfRows_vlXiConj h1
  have h3 := wfRows_vlXiConj h2
  intro i hi
  interval_cases i
  · exact hT
  · exact h1
  · exact h2
  · exact h3

@[expose] noncomputable def vlSubJ (ts : ℕ → J) (m : ℕ) : J :=
  (List.range 4).foldl (fun acc i => if m.testBit i then acc * ts i else acc) 1

theorem vlSubJ_mem {V : Subgroup J} {ts : ℕ → J} (h : ∀ i < 4, ts i ∈ V) (m : ℕ) :
    vlSubJ ts m ∈ V := by
  have key : ∀ (L : List ℕ), (∀ i ∈ L, i < 4) → ∀ acc : J, acc ∈ V →
      L.foldl (fun a i => if m.testBit i then a * ts i else a) acc ∈ V := by
    intro L
    induction L with
    | nil => intro _ acc hacc; simpa using hacc
    | cons i L ih =>
      intro hL acc hacc
      simp only [List.foldl_cons]
      have hi : i < 4 := hL i (List.mem_cons_self ..)
      have hL' : ∀ j ∈ L, j < 4 := fun j hj => hL j (List.mem_cons_of_mem _ hj)
      by_cases hb : m.testBit i = true
      · simp only [hb, ↓reduceIte]
        exact ih hL' _ (V.mul_mem hacc (h i hi))
      · simp only [hb]
        exact ih hL' _ hacc
  exact key _ (by simp) 1 V.one_mem

theorem Mx_vlSubJ {ts : ℕ → J} {Ts : Array (Array V2)}
    (hT : ∀ i < 4, Mx (ts i) = rowsMatrix Ts[i]!) (m : ℕ) :
    Mx (vlSubJ ts m) = rowsMatrix (vlSubsetProd Ts m) := by
  unfold vlSubJ vlSubsetProd
  have key : ∀ (L : List ℕ), (∀ i ∈ L, i < 4) → ∀ (acc : J) (accR : Array V2),
      Mx acc = rowsMatrix accR →
      Mx (L.foldl (fun a i => if m.testBit i then a * ts i else a) acc) =
        rowsMatrix (L.foldl (fun a i => if m.testBit i then mulRows a Ts[i]! else a) accR) := by
    intro L
    induction L with
    | nil => intro _ acc accR h; simpa using h
    | cons i L ih =>
      intro hL acc accR h
      simp only [List.foldl_cons]
      have hi : i < 4 := hL i (List.mem_cons_self ..)
      have hL' : ∀ j ∈ L, j < 4 := fun j hj => hL j (List.mem_cons_of_mem _ hj)
      by_cases hb : m.testBit i = true
      · simp only [hb, ↓reduceIte]
        exact ih hL' _ _ (by rw [map_mul, h, hT i hi, rowsMatrix_mulRows])
      · simp only [hb]
        exact ih hL' _ _ h
  exact key _ (by simp) 1 idRows (by rw [map_one, rowsMatrix_idRows])

theorem wfRows_vlSubsetProd
    {Ts : Array (Array V2)} (hT : ∀ i < 4, wfRows Ts[i]! = true)
    (m : ℕ) : wfRows (vlSubsetProd Ts m) = true := by
  unfold vlSubsetProd
  have key : ∀ (L : List ℕ), (∀ i ∈ L, i < 4) → ∀ accR : Array V2, wfRows accR = true →
      wfRows (L.foldl (fun a i => if m.testBit i then mulRows a Ts[i]! else a) accR) = true := by
    intro L
    induction L with
    | nil => intro _ accR h; simpa using h
    | cons i L ih =>
      intro hL accR h
      simp only [List.foldl_cons]
      have hi : i < 4 := hL i (List.mem_cons_self ..)
      have hL' : ∀ j ∈ L, j < 4 := fun j hj => hL j (List.mem_cons_of_mem _ hj)
      by_cases hb : m.testBit i = true
      · simp only [hb, ↓reduceIte]
        exact ih hL' _ (wfRows_mulRows h (hT i hi))
      · simp only [hb]
        exact ih hL' _ h
  exact key _ (by simp) idRows wfRows_idRows

theorem vlValid_of_group
    (hM : MatFacts) {t : J} {T : Array V2} (hwf : wfRows T = true)
    (hT : Mx t = rowsMatrix T) (h2 : t * t = 1) (h01 : t * vlCj t 1 = vlCj t 1 * t)
    (h02 : t * vlCj t 2 = vlCj t 2 * t)
    (hprod : t * vlCj t 1 * vlCj t 2 * vlCj t 3 * vlCj t 4 = 1) : vlValid T = true := by
  have hM1 : Mx (vlCj t 1) = rowsMatrix (vlXiConj T) := Mx_vlXiConj hM hT
  have hM2 : Mx (vlCj t 2) = rowsMatrix (vlXiConj (vlXiConj T)) := Mx_vlXiConj hM hM1
  have hM3 : Mx (vlCj t 3) = rowsMatrix (vlXiConj (vlXiConj (vlXiConj T))) :=
    Mx_vlXiConj hM hM2
  have hM4 : Mx (vlCj t 4) = rowsMatrix (vlXiConj (vlXiConj (vlXiConj (vlXiConj T)))) :=
    Mx_vlXiConj hM hM3
  have w1 := wfRows_vlXiConj hwf
  have w2 := wfRows_vlXiConj w1
  have w3 := wfRows_vlXiConj w2
  have w4 := wfRows_vlXiConj w3
  unfold vlValid
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · refine eqRows_of_mx (wfRows_mulRows hwf hwf) wfRows_idRows ?_
    rw [rowsMatrix_mulRows, ← hT, ← map_mul, h2, map_one, rowsMatrix_idRows]
  · simp only [Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · unfold vlComm
      refine eqRows_of_mx (wfRows_mulRows hwf w1) (wfRows_mulRows w1 hwf) ?_
      rw [rowsMatrix_mulRows, rowsMatrix_mulRows, ← hT, ← hM1, ← map_mul, ← map_mul, h01]
    · unfold vlComm
      refine eqRows_of_mx (wfRows_mulRows hwf w2) (wfRows_mulRows w2 hwf) ?_
      rw [rowsMatrix_mulRows, rowsMatrix_mulRows, ← hT, ← hM2, ← map_mul, ← map_mul, h02]
    · refine eqRows_of_mx (wfRows_mulRows (wfRows_mulRows (wfRows_mulRows (wfRows_mulRows hwf w1)
        w2) w3) w4) wfRows_idRows ?_
      rw [rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_mulRows, ← hT,
        ← hM1, ← hM2, ← hM3, ← hM4, ← map_mul, ← map_mul, ← map_mul, ← map_mul, hprod, map_one,
        rowsMatrix_idRows]

end CFSG.Sporadic.J4.QT2
