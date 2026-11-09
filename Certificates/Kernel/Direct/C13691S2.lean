module

public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharDataE8
public import Certificates.Kernel.Direct.C13691S2Lanes
public import Certificates.Kernel.Direct.C13691S2Tree

public section

namespace CertificateChecks.KernelDirect.C13691

open CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag}

@[expose] def stepK (C : RootCertificate τ) (S : StabCert3) (k : ℕ) : Bool :=
  (List.range τ.rank).all fun i =>
    StabCert3.stepAux τ (RootTables.ofCert C) (S.simple.map fun β => (RootTables.ofCert C).vecs.getD β [])
      (KTree.ofSorted S.keys) (imgL (RootTables.ofCert C) i (decodeT τ.rank k))

@[expose] def headK (C : RootCertificate τ) (S : StabCert3) : Bool :=
  (KTree.ofSorted S.keys).mem (encodeT (List.range τ.rank)) &&
  decide (decodeT τ.rank (encodeT (List.range τ.rank)) = List.range τ.rank) &&
  S.simple.all (fun β => decide (β < C.roots.length) && decide (0 < height (C.root β)) &&
    decide (triPairing (vec3 (τ := τ) S.vec) (C.root β) = 0))

theorem check_eq (C : RootCertificate τ) (S : StabCert3) :
    S.check C = (headK C S && S.keys.all (stepK C S)) := rfl

theorem all_of_chunks {α : Type} (f : α → Bool) (l : List α) (c : ℕ) :
    ∀ m, (∀ j, j < m → ((l.drop (c * j)).take c).all f = true) → l.drop (c * m) = [] →
      l.all f = true := by
  intro m
  induction m generalizing l with
  | zero =>
    intro _ h
    simp only [Nat.mul_zero, List.drop_zero] at h
    simp [h]
  | succ m ih =>
    intro hc hd
    rw [← List.take_append_drop c l, List.all_append, Bool.and_eq_true]
    refine ⟨by simpa using hc 0 (by omega), ih (l.drop c) (fun j hj => ?_) ?_⟩
    · rw [List.drop_drop, show c + c * j = c * (j + 1) by rw [Nat.mul_add_one, Nat.add_comm]]
      exact hc (j + 1) (by omega)
    · rw [List.drop_drop, show c + c * m = c * (m + 1) by rw [Nat.mul_add_one, Nat.add_comm]]
      exact hd

@[expose] def laneB (X k : ℕ) : ℕ := Nat.land (Nat.shiftRight X (Nat.mul 8 k)) 255

@[expose] def imgP (IM : List ℕ) (i : ℕ) (t : List ℕ) : List ℕ := t.map fun k => laneB (IM.getD i 0) k

@[expose] def hsP (HT : ℕ) (t : List ℕ) : List ℤ := t.map fun k => ((laneB HT k : ℕ) : ℤ) - 32

@[expose] def stepP (S : StabCert3) (Δv : List (List ℤ)) (HT : ℕ) (r : ℕ) (img : List ℕ) : Bool :=
  !(dTestL Δv (hsP HT img)) ||
    (decide (decodeT r (encodeT img) = img) && (KTree.ofSorted S.keys).mem (encodeT img))

@[expose] def stepKP (C : RootCertificate τ) (S : StabCert3) (IM : List ℕ) (HT : ℕ) (k : ℕ) : Bool :=
  (List.range τ.rank).all fun i =>
    stepP S (S.simple.map fun β => (RootTables.ofCert C).vecs.getD β []) HT τ.rank
      (imgP IM i (decodeT τ.rank k))

@[expose] def lanesOK (C : RootCertificate τ) (IM : List ℕ) (HT : ℕ) : Bool :=
  (List.range τ.rank).all (fun i => (List.range 256).all fun k =>
    Nat.beq (((RootTables.ofCert C).imgs.getD i []).getD k 0) (laneB (IM.getD i 0) k)) &&
  (List.range 256).all fun k => decide ((RootTables.ofCert C).hts.getD k 0 = ((laneB HT k : ℕ) : ℤ) - 32)

theorem laneB_lt (X k : ℕ) : laneB X k < 256 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem all_congr' {α : Type} {l : List α} {f g : α → Bool} (h : ∀ a ∈ l, f a = g a) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons]
    rw [h a List.mem_cons_self, ih fun b hb => h b (List.mem_cons_of_mem a hb)]

theorem stepK_eq (C : RootCertificate τ) (S : StabCert3) (IM : List ℕ) (HT : ℕ)
    (h : lanesOK C IM HT = true) (k : ℕ) : stepK C S k = stepKP C S IM HT k := by
  simp only [lanesOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, Nat.beq_eq,
    decide_eq_true_eq] at h
  obtain ⟨hI, hH⟩ := h
  unfold stepK stepKP
  refine all_congr' fun i hi => ?_
  rw [List.mem_range] at hi
  have h1 : imgL (RootTables.ofCert C) i (decodeT τ.rank k) = imgP IM i (decodeT τ.rank k) := by
    unfold imgL imgP
    refine List.map_congr_left fun x hx => hI i hi x ?_
    simp only [decodeT, List.mem_map] at hx
    obtain ⟨j, -, rfl⟩ := hx
    exact Nat.mod_lt _ (by decide)
  have h2 : hsL (RootTables.ofCert C) (imgP IM i (decodeT τ.rank k)) =
      hsP HT (imgP IM i (decodeT τ.rank k)) := by
    unfold hsL hsP
    refine List.map_congr_left fun x hx => hH x ?_
    simp only [imgP, List.mem_map] at hx
    obtain ⟨j, -, rfl⟩ := hx
    exact laneB_lt _ _
  rw [h1]
  unfold StabCert3.stepAux stepP
  rw [h2]

@[expose] def ktreeEq : KTree → KTree → Bool
  | .nil, .nil => true
  | .node l k r, .node l' k' r' => Nat.beq k k' && ktreeEq l l' && ktreeEq r r'
  | _, _ => false

theorem eq_of_ktreeEq : ∀ {a b : KTree}, ktreeEq a b = true → a = b
  | .nil, .nil, _ => rfl
  | .node l k r, .node l' k' r', h => by
    simp only [ktreeEq, Bool.and_eq_true, Nat.beq_eq] at h
    rw [h.1.1, eq_of_ktreeEq h.1.2, eq_of_ktreeEq h.2]
  | .nil, .node _ _ _, h => by simp [ktreeEq] at h
  | .node _ _ _, .nil, h => by simp [ktreeEq] at h

@[expose] def stepQ (DV : List (List ℤ)) (T : KTree) (HT : ℕ) (r : ℕ) (img : List ℕ) : Bool :=
  !(dTestL DV (hsP HT img)) || (decide (decodeT r (encodeT img) = img) && T.mem (encodeT img))

@[expose] def stepKQ (IM : List ℕ) (HT : ℕ) (r : ℕ) (DV : List (List ℤ)) (T : KTree) (k : ℕ) :
    Bool :=
  (List.range r).all fun i => stepQ DV T HT r (imgP IM i (decodeT r k))

theorem stepKP_eq (C : RootCertificate τ) (S : StabCert3) (IM : List ℕ) (HT : ℕ)
    (DV : List (List ℤ)) (T : KTree)
    (hDV : S.simple.map (fun β => (RootTables.ofCert C).vecs.getD β []) = DV)
    (hT : KTree.ofSorted S.keys = T) (k : ℕ) :
    stepKP C S IM HT k = stepKQ IM HT τ.rank DV T k := by
  subst hDV hT
  rfl

@[expose] def dotN : List ℕ → List ℕ → ℕ
  | a :: as, b :: bs => Nat.add (Nat.mul a b) (dotN as bs)
  | _, _ => 0

@[expose] def dTestN (DV : List (List ℕ × ℕ)) (hs : List ℕ) : Bool :=
  DV.all fun p => Nat.blt p.2 (dotN p.1 hs)

@[expose] def stepN (DV : List (List ℕ × ℕ)) (T : KTree) (HT : ℕ) (r : ℕ) (img : List ℕ) : Bool :=
  !(dTestN DV (img.map (laneB HT))) ||
    (decide (decodeT r (encodeT img) = img) && T.mem (encodeT img))

@[expose] def stepKN (IM : List ℕ) (HT : ℕ) (r : ℕ) (DV : List (List ℕ × ℕ)) (T : KTree) (k : ℕ) :
    Bool :=
  (List.range r).all fun i => stepN DV T HT r (imgP IM i (decodeT r k))

@[expose] def dvnOK (r : ℕ) (DV : List (List ℕ × ℕ)) : Bool :=
  DV.all fun p => Nat.beq p.1.length r && Nat.beq p.2 (32 * p.1.sum)

theorem dotL_natCast : ∀ (a c : List ℕ), a.length = c.length →
    dotL (a.map fun x : ℕ => (x : ℤ)) (c.map fun x : ℕ => (x : ℤ) - 32) =
      ((dotN a c : ℕ) : ℤ) - 32 * ((a.sum : ℕ) : ℤ)
  | [], [], _ => by simp [dotL, dotN]
  | x :: a, y :: c, h => by
    have ih := dotL_natCast a c (by simpa using h)
    simp only [dotL, List.map_cons, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
    rw [ih]
    simp only [dotN, Nat.add_eq, Nat.mul_eq]
    push_cast
    ring
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem dTestL_eq (DV : List (List ℕ × ℕ)) (r HT : ℕ) (h : dvnOK r DV = true) (img : List ℕ)
    (hl : img.length = r) :
    dTestL (DV.map fun p => p.1.map fun x : ℕ => (x : ℤ)) (hsP HT img) =
      dTestN DV (img.map (laneB HT)) := by
  simp only [dvnOK, List.all_eq_true, Bool.and_eq_true, Nat.beq_eq] at h
  have e : hsP HT img = (img.map (laneB HT)).map fun x : ℕ => (x : ℤ) - 32 := by
    unfold hsP
    rw [List.map_map]
    rfl
  unfold dTestL dTestN
  rw [List.all_map, e]
  refine all_congr' fun p hp => ?_
  obtain ⟨h1, h2⟩ := h p hp
  simp only [Function.comp_apply]
  rw [dotL_natCast _ _ (by simp [h1, hl]), h2, Bool.eq_iff_iff, decide_eq_true_iff, Nat.blt_eq]
  omega

theorem stepKQ_eq_N (IM : List ℕ) (HT r : ℕ) (DV : List (List ℕ × ℕ)) (T : KTree)
    (h : dvnOK r DV = true) (k : ℕ) :
    stepKQ IM HT r (DV.map fun p => p.1.map fun x : ℕ => (x : ℤ)) T k = stepKN IM HT r DV T k := by
  unfold stepKQ stepKN
  refine all_congr' fun i _ => ?_
  unfold stepQ stepN
  rw [dTestL_eq DV r HT h _ (by simp [imgP, decodeT])]

def keyChunk (j : ℕ) : Bool :=
  ((e8ThreeStab2.keys.drop (64 * j)).take 64).all (stepKN e8IM e8HT (Tag.rank .E8) e8DVN e8T2)

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem head_ok : headK e8Certificate e8ThreeStab2 = true := by decide +kernel
theorem pass_ok : decide ((e8ThreeStab2.passing e8Certificate).length ≤ 1) = true := by
  decide +kernel
theorem drop_ok : e8ThreeStab2.keys.drop (64 * 30) = [] := by decide +kernel
theorem lanes_ok : lanesOK e8Certificate e8IM e8HT = true := by decide +kernel
theorem tree_ok : KTree.ofSorted e8ThreeStab2.keys = e8T2 :=
  eq_of_ktreeEq (by decide +kernel)
theorem dv_ok : e8ThreeStab2.simple.map (fun β => (RootTables.ofCert e8Certificate).vecs.getD β []) =
    e8DVN.map fun p => p.1.map fun x : ℕ => (x : ℤ) := by
  decide +kernel
theorem dvn_ok : dvnOK (Tag.rank .E8) e8DVN = true := by decide +kernel

theorem k0 : keyChunk 0 = true := by decide +kernel
theorem k1 : keyChunk 1 = true := by decide +kernel
theorem k2 : keyChunk 2 = true := by decide +kernel
theorem k3 : keyChunk 3 = true := by decide +kernel
theorem k4 : keyChunk 4 = true := by decide +kernel
theorem k5 : keyChunk 5 = true := by decide +kernel
theorem k6 : keyChunk 6 = true := by decide +kernel
theorem k7 : keyChunk 7 = true := by decide +kernel
theorem k8 : keyChunk 8 = true := by decide +kernel
theorem k9 : keyChunk 9 = true := by decide +kernel
theorem k10 : keyChunk 10 = true := by decide +kernel
theorem k11 : keyChunk 11 = true := by decide +kernel
theorem k12 : keyChunk 12 = true := by decide +kernel
theorem k13 : keyChunk 13 = true := by decide +kernel
theorem k14 : keyChunk 14 = true := by decide +kernel
theorem k15 : keyChunk 15 = true := by decide +kernel
theorem k16 : keyChunk 16 = true := by decide +kernel
theorem k17 : keyChunk 17 = true := by decide +kernel
theorem k18 : keyChunk 18 = true := by decide +kernel
theorem k19 : keyChunk 19 = true := by decide +kernel
theorem k20 : keyChunk 20 = true := by decide +kernel
theorem k21 : keyChunk 21 = true := by decide +kernel
theorem k22 : keyChunk 22 = true := by decide +kernel
theorem k23 : keyChunk 23 = true := by decide +kernel
theorem k24 : keyChunk 24 = true := by decide +kernel
theorem k25 : keyChunk 25 = true := by decide +kernel
theorem k26 : keyChunk 26 = true := by decide +kernel
theorem k27 : keyChunk 27 = true := by decide +kernel
theorem k28 : keyChunk 28 = true := by decide +kernel
theorem k29 : keyChunk 29 = true := by decide +kernel

theorem e8ThreeStab2_ok : (e8ThreeStab2.check e8Certificate &&
    decide ((e8ThreeStab2.passing e8Certificate).length ≤ 1)) = true := by
  have hallN : e8ThreeStab2.keys.all (stepKN e8IM e8HT (Tag.rank .E8) e8DVN e8T2) = true :=
    all_of_chunks _ _ 64 30 (fun j hj => by
      interval_cases j
      exacts [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18,
        k19, k20, k21, k22, k23, k24, k25, k26, k27, k28, k29]) drop_ok
  have hallQ : e8ThreeStab2.keys.all (stepKQ e8IM e8HT (Tag.rank .E8)
      (e8DVN.map fun p => p.1.map fun x : ℕ => (x : ℤ)) e8T2) = true :=
    (congrArg (fun f => e8ThreeStab2.keys.all f)
      (funext (stepKQ_eq_N _ _ _ _ _ dvn_ok))).trans hallN
  have hallP : e8ThreeStab2.keys.all (stepKP e8Certificate e8ThreeStab2 e8IM e8HT) = true :=
    (congrArg (fun f => e8ThreeStab2.keys.all f)
      (funext (stepKP_eq _ _ _ _ _ _ dv_ok tree_ok))).trans hallQ
  have hall : e8ThreeStab2.keys.all (stepK e8Certificate e8ThreeStab2) = true :=
    (congrArg (fun f => e8ThreeStab2.keys.all f) (funext (stepK_eq _ _ _ _ lanes_ok))).trans hallP
  rw [check_eq, head_ok, hall, pass_ok]
  all_goals rfl

end CertificateChecks.KernelDirect.C13691
