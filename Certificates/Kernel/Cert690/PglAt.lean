module

public import Certificates.Data.Kernel.Cert690.Pgl
public import Certificates.Kernel.Cert690.PglData
public import Certificates.Kernel.Cert690.PglF10Data

public section

namespace CertificateChecks.KernelC690.Pgl

open CFSG.KC.C690 CFSG.GF2Type.Smith1979W3.Cert690

@[expose] def subsAllK (b : Nat) (Q : Nat → Bool) (k : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) Q
    (fun i r acc => r acc && (Nat.beq (Nat.land (Nat.shiftRight b i) 1) 1 ||
      r (Nat.add acc (Nat.shiftLeft 1 i)))) k

theorem subsAllK_spec (b : Nat) (Q : Nat → Bool) (k : Nat) :
    ∀ acc, subsAllK b Q k acc = true → ∀ m, m < 2 ^ k → m &&& b = 0 → Q (acc + m) = true := by
  induction k with
  | zero =>
    intro acc h m hm _
    have : m = 0 := by omega
    subst this
    exact h
  | succ k ih =>
    intro acc h m hm hb
    have h' : (subsAllK b Q k acc && (Nat.beq (Nat.land (Nat.shiftRight b k) 1) 1 ||
        subsAllK b Q k (Nat.add acc (Nat.shiftLeft 1 k)))) = true := h
    rw [Bool.and_eq_true, Bool.or_eq_true] at h'
    have hbit : ∀ j, m.testBit j = true → b.testBit j = false := by
      intro j hj
      have := congrArg (fun x => x.testBit j) hb
      simp only [Nat.testBit_and, Nat.zero_testBit, hj, Bool.true_and] at this
      exact this
    by_cases hlt : m < 2 ^ k
    · exact ih acc h'.1 m hlt hb
    · have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
      have hm' : m - 2 ^ k < 2 ^ k := by omega
      have hmk : m.testBit k = true := by
        have e : m = 2 ^ k + (m - 2 ^ k) := by omega
        rw [e, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hm']
        rfl
      rcases h'.2 with h2 | h2
      · exfalso
        have hb1 : b.testBit k = true := by
          have h3 : 1 &&& (b >>> k) = 1 := by
            rw [Nat.land_comm]
            exact Nat.eq_of_beq_eq_true h2
          unfold Nat.testBit
          rw [h3]
          rfl
        rw [hbit k hmk] at hb1
        exact absurd hb1 (by decide)
      · have hsub : (m - 2 ^ k) &&& b = 0 := by
          apply Nat.eq_of_testBit_eq
          intro j
          rw [Nat.testBit_and, Nat.zero_testBit]
          have e : m - 2 ^ k = m % 2 ^ k := by
            rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hm']
          rw [e, Nat.testBit_mod_two_pow]
          cases hj : m.testBit j
          · simp
          · simp [hbit j hj]
        have := ih _ h2 (m - 2 ^ k) hm' hsub
        have e1 : Nat.shiftLeft 1 k = 2 ^ k := Nat.one_shiftLeft k
        have e2 : Nat.add acc (Nat.shiftLeft 1 k) + (m - 2 ^ k) = acc + m := by
          rw [e1]
          change acc + 2 ^ k + (m - 2 ^ k) = acc + m
          omega
        rwa [e2] at this

theorem all_range_of_subsAllK (n b : Nat) (Q : Nat → Bool)
    (hQ : ∀ m, ¬ m &&& b = 0 → Q m = true) (h : subsAllK b Q n 0 = true) :
    (List.range (2 ^ n)).all Q = true := by
  rw [List.all_eq_true]
  intro m hm
  rw [List.mem_range] at hm
  by_cases hb : m &&& b = 0
  · have := subsAllK_spec b Q n 0 h m hm hb
    rwa [Nat.zero_add] at this
  · exact hQ m hb

@[expose] noncomputable def f10Q (elems : Array Nat) (e : Nat) (M conj : Array (Array Nat))
    (badCent : Array Nat) (bad oneIdx n mask : Nat) : Bool :=
  if (mask &&& bad == 0) && (mask.testBit oneIdx && decide (4 ≤ bitCount n mask)) then
    if maskClosed M mask n then
      let normEq := (List.range elems.size).all fun h =>
        normalizesMask (conj[h]!) mask n == (actF (elems[h]!) e == e)
      let bad2 := badCent.toList.any fun m => (mask &&& m) == mask
      !normEq || bad2
    else true
  else true

@[expose] noncomputable def f10Core (elems invs : Array Nat) (e : Nat) (C : Array Nat) : Bool :=
    let n := C.size
    let M := mulIdxTableK C
    let isInv := (C.toList.map (fun a => mulF a a == oneF)).toArray
    let oneIdx := C.toList.idxOf oneF
    let conj := conjIdxTableK C elems invs
    let cent := centralMaskTableK C elems
    let badCent := (List.range elems.size).foldl
      (fun acc i => if pow2F (elems[i]!) then acc else acc.push (cent[i]!)) #[]
    if n == 16 then
      let mexact := (List.range n).all fun i =>
        (List.range n).all fun j =>
          let m := (M[i]!)[j]!
          decide (m < n) && C[m]! == mulF (C[i]!) (C[j]!)
      let cexact := (List.range elems.size).all fun h =>
        (List.range n).all fun i =>
          let y := (conj[h]!)[i]!
          let z := mulF (mulF (elems[h]!) (C[i]!)) (invs[h]!)
          (decide (y < n) && C[y]! == z) || (y == n && !(C.toList.contains z))
      C.toList.dedup.length == C.size &&
      decide (oneIdx < n) && C[oneIdx]! == oneF &&
      mexact && cexact &&
      (List.range (2 ^ n)).all (f10Q elems e M conj badCent (badMaskK isInv n) oneIdx n)
    else false

theorem f10At_eq (elems invs : Array Nat) (e : Nat) :
    f10At elems invs e = f10Core elems invs e (elems.filter fun k => actF k e == e) := rfl

@[expose] noncomputable def f10R (elems invs : Array Nat) (e : Nat) (C : Array Nat)
    (T : Array (Array Nat)) : Bool :=
    let n := C.size
    let M := mulIdxTableK C
    let isInv := (C.toList.map (fun a => mulF a a == oneF)).toArray
    let oneIdx := C.toList.idxOf oneF
    let cent := centralMaskTableK C elems
    let badCent := (List.range elems.size).foldl
      (fun acc i => if pow2F (elems[i]!) then acc else acc.push (cent[i]!)) #[]
    if n == 16 then
      let mexact := (List.range n).all fun i =>
        (List.range n).all fun j =>
          let m := (M[i]!)[j]!
          decide (m < n) && C[m]! == mulF (C[i]!) (C[j]!)
      let tabOK := T.size == elems.size && invs.size == elems.size &&
        ((T.toList.zip elems.toList).zip invs.toList).all fun p =>
          p.1.1.size == n && (p.1.1.toList.zip C.toList).all fun q =>
            q.1 == C.toList.idxOf (mulF (mulF p.1.2 q.2) p.2)
      C.toList.dedup.length == C.size &&
      decide (oneIdx < n) && C[oneIdx]! == oneF &&
      mexact && tabOK &&
      subsAllK (badMaskK isInv n) (f10Q elems e M T badCent (badMaskK isInv n) oneIdx n) n 0
    else false

@[expose] noncomputable def f10L (elems invs : Array Nat) (e : Nat) (C : Array Nat)
    (T : Array (Array Nat)) : Bool :=
  (elems.filter fun k => actF k e == e).toList == C.toList && f10R elems invs e C T

theorem f10_all_congr {f g : Nat → Bool} :
    ∀ l : List Nat, (∀ i ∈ l, f i = g i) → l.all f = l.all g := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro H
    rw [List.all_cons, List.all_cons, H a List.mem_cons_self,
      ih (fun i hi => H i (List.mem_cons_of_mem a hi))]

theorem f10_zip2_all {α β : Type} (A : List α) (B : List β) (f : α × β → Bool)
    (hA : A.length = B.length) (h : (A.zip B).all f = true) (x : Nat) (hx : x < B.length) :
    f (A[x]'(by omega), B[x]) = true := by
  rw [List.all_eq_true] at h
  apply h
  have hl : x < (A.zip B).length := by simp [List.length_zip]; omega
  simpa [List.getElem_zip] using List.getElem_mem hl

theorem f10_zip3_all {α β γ : Type} (A : List α) (B : List β) (D : List γ) (f : (α × β) × γ → Bool)
    (hA : A.length = B.length) (hD : D.length = B.length) (h : ((A.zip B).zip D).all f = true)
    (x : Nat) (hx : x < B.length) :
    f ((A[x]'(by omega), B[x]), D[x]'(by omega)) = true := by
  rw [List.all_eq_true] at h
  apply h
  have hl : x < ((A.zip B).zip D).length := by simp [List.length_zip]; omega
  simpa [List.getElem_zip] using List.getElem_mem hl

theorem conjIdxTableK_get(A K invK : Array Nat) (h i : Nat) (hh : h < K.size) (hi : i < A.size) :
    ((conjIdxTableK A K invK)[h]!)[i]! = A.toList.idxOf (mulF (mulF (K[h]!) (A[i]!)) (invK[h]!)) := by
  unfold conjIdxTableK
  simp [getElem!_pos, hh, hi]

theorem f10Q_congr (elems : Array Nat) (e : Nat) (M T T' : Array (Array Nat)) (badCent : Array Nat)
    (bad oneIdx n : Nat) (hT : ∀ h < elems.size, ∀ i < n, (T[h]!)[i]! = (T'[h]!)[i]!) :
    f10Q elems e M T badCent bad oneIdx n = f10Q elems e M T' badCent bad oneIdx n := by
  funext mask
  unfold f10Q
  dsimp only
  have hE : ((List.range elems.size).all fun h =>
        normalizesMask (T[h]!) mask n == (actF (elems[h]!) e == e)) =
      ((List.range elems.size).all fun h =>
        normalizesMask (T'[h]!) mask n == (actF (elems[h]!) e == e)) := by
    apply f10_all_congr
    intro h hh
    rw [List.mem_range] at hh
    unfold normalizesMask
    rw [f10_all_congr (g := fun i => !(mask.testBit i) || mask.testBit ((T'[h]!)[i]!)) _
      (fun i hi => by rw [hT h hh i (List.mem_range.mp hi)])]
  rw [hE]

theorem f10Core_of_R (elems invs : Array Nat) (e : Nat) (C : Array Nat) (T : Array (Array Nat))
    (h : f10R elems invs e C T = true) : f10Core elems invs e C = true := by
  unfold f10R at h
  unfold f10Core
  dsimp only at h ⊢
  split
  · rw [if_pos (by assumption)] at h
    simp only [Bool.and_eq_true] at h ⊢
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, hm⟩, ⟨⟨hTs, hIs⟩, h4⟩⟩, h5⟩ := h
    have hT : ∀ x < elems.size, ∀ i < C.size,
        (T[x]!)[i]! = ((conjIdxTableK C elems invs)[x]!)[i]! := by
      intro x hx i hi
      rw [conjIdxTableK_get _ _ _ x i hx hi]
      have hTs' := beq_iff_eq.mp hTs
      have hIs' := beq_iff_eq.mp hIs
      have h4x := f10_zip3_all T.toList elems.toList invs.toList _ (by simpa using hTs')
        (by simpa using hIs') h4 x (by simpa using hx)
      rw [Bool.and_eq_true] at h4x
      have hr := beq_iff_eq.mp h4x.1
      have := beq_iff_eq.mp (f10_zip2_all _ C.toList _ (by simpa using hr) h4x.2 i (by simpa using hi))
      have hrx : (T[x]'(by omega)).size = C.size := by simpa using hr
      have hi2 : i < (T[x]'(by omega)).size := by omega
      simpa [getElem!_pos, hx, hi, hi2, hTs', hIs'] using this
    refine ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, hm⟩, ?_⟩, ?_⟩
    · rw [List.all_eq_true]
      intro x hx
      rw [List.all_eq_true]
      intro i hi
      rw [List.mem_range] at hx hi
      rw [conjIdxTableK_get _ _ _ x i hx hi]
      generalize mulF (mulF (elems[x]!) (C[i]!)) (invs[x]!) = z
      by_cases hz : z ∈ C.toList
      · have hy : C.toList.idxOf z < C.size := by
          simpa using (List.idxOf_lt_length_iff.mpr hz)
        have hv : C[C.toList.idxOf z] = z := by
          have := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hz)
          rw [Array.getElem_toList] at this
          exact this
        simp [hy, hv]
      · have hy : C.toList.idxOf z = C.size := by
          simpa using (List.idxOf_eq_length hz)
        simp [hy, hz]
    · rw [← f10Q_congr _ _ _ _ _ _ _ _ _ hT]
      refine all_range_of_subsAllK _ _ _ (fun m hm => ?_) h5
      unfold f10Q
      rw [if_neg]
      intro hc
      rw [Bool.and_eq_true] at hc
      exact hm (beq_iff_eq.mp hc.1)
  · rw [if_neg (by assumption)] at h
    exact h

theorem f10At_of_L (elems invs : Array Nat) (e : Nat) (C : Array Nat) (T : Array (Array Nat))
    (h : f10L elems invs e C T = true) : f10At elems invs e = true := by
  unfold f10L at h
  rw [Bool.and_eq_true] at h
  have hC : elems.filter (fun k => actF k e == e) = C := Array.toList_inj.mp (beq_iff_eq.mp h.1)
  rw [f10At_eq, hC]
  exact f10Core_of_R elems invs e C T h.2

@[expose] def f10Es : List Nat :=
  [5, 10, 15, 18, 20, 21, 22, 26, 31, 33, 37, 40, 41, 42, 47, 51, 55, 59, 60, 61, 62]

theorem f10Vecs_eq : f10Vecs = f10Es := by decide

@[expose] noncomputable def f10I (k : Nat) : Bool :=
  f10L K.toArray (invsL K).toArray (f10Es.getD k 0) (f10Cs.getD k #[]) (f10Ts.getD k #[])

@[expose] noncomputable def f11I (k : Nat) : Bool := f11At K.toArray ((outersL K K0).getD k 0)

end CertificateChecks.KernelC690.Pgl

end
