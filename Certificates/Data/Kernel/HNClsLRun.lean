module

public import Certificates.Data.Kernel.HNClsL

public section

namespace CFSG.KC.HNClsL

open CFSG.KC.Ord CFSG.KC.SlpPc

theorem strictN_eqH (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

theorem sB_eqH (y : Nat) (k : Nat → Bool) : sB y k = k y := by
  cases y <;> rfl

theorem mapS_eqH {α : Type} (f : α → Nat) : ∀ (l : List α) (k : List Nat → Bool),
    mapS f l k = k (l.map f)
  | [], _ => rfl
  | a :: l, k => by
    change sB (f a) (fun x => mapS f l fun xs => k (List.cons x xs)) = _
    rw [sB_eqH, mapS_eqH f l]
    rfl

theorem andB_trueH {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

theorem wordGo_append (mul : Nat → Nat → Nat) (R : Nat → Nat) :
    ∀ (a b : List Nat) (acc : Nat), wordGo mul R (a ++ b) acc = wordGo mul R b (wordGo mul R a acc)
  | [], _, _ => rfl
  | l :: a, b, acc => by
    change CFSG.KC.Loop.strictN (mul acc (R l)) (wordGo mul R (a ++ b)) =
      wordGo mul R b (CFSG.KC.Loop.strictN (mul acc (R l)) (wordGo mul R a))
    rw [strictN_eqH, strictN_eqH]
    exact wordGo_append mul R a b _

theorem wordGo_of_chunks {mul : Nat → Nat → Nat} {R : Nat → Nat} {w : List Nat} {K m : Nat}
    {P : Nat → Nat} (hm : w.length ≤ K * m)
    (h : ∀ i < m, Nat.beq (wordGo mul R ((w.drop (K * i)).take K) (P i)) (P (i + 1)) = true) :
    wordGo mul R w (P 0) = P m := by
  have key : ∀ j ≤ m, wordGo mul R (w.take (K * j)) (P 0) = P j := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      rw [Nat.mul_succ, List.take_add, wordGo_append, ih (by omega)]
      exact Nat.eq_of_beq_eq_true (h j (by omega))
  have e := key m (Nat.le_refl m)
  rwa [List.take_of_length_le hm] at e

theorem nthD_eqH {α : Type} (d : α) : ∀ (l : List α) (i : Nat), nthD d l i = l.getD i d
  | [], _ => by simp [nthD]
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => by
    rw [List.getD_cons_succ, ← nthD_eqH d l i]
    rfl

theorem map_eq_of_nthD {α : Type} {f : α → Nat} {d : α} {e : Nat} {l : List α} {X : List Nat}
    (hl : X.length = l.length) (h : ∀ j < l.length, f (nthD d l j) = nthD e X j) :
    l.map f = X := by
  apply List.ext_getElem (by simp [hl])
  intro j h1 h2
  have h1' : j < l.length := by simpa using h1
  have := h j h1'
  rw [nthD_eqH, nthD_eqH] at this
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1', List.getElem?_eq_getElem h2]
    using this

theorem fun_eq_of_nthD {g : Nat → Nat} {e : Nat} {X : List Nat}
    (hX : ∀ j, X.length ≤ j → g j = e) (h : ∀ j < X.length, g j = nthD e X j) : g = nthD e X := by
  funext j
  by_cases hj : j < X.length
  · exact h j hj
  · rw [hX j (by omega), nthD_eqH]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hj)]

@[expose] noncomputable def restK (mul : Nat → Nat → Nat) (ONE : Nat) (pool : List (List Nat))
    (gens : List Nat) (nQ : Nat) (lines : List (List (Nat × Nat)))
    (fuse : List (Nat × (List (Nat × Nat) × Nat))) (wl : List (List (Nat × Nat)))
    (wits : List (List (List (Nat × Nat)) × Nat)) (tr : List Nat) (F G : Nat → Nat) : Bool :=
  sB (F 0) fun Y =>
    andB (allL (fun j => andB (evC (nthD List.nil pool j)) (Nat.beq (mul (F j) Y) (mul Y (F j))))
      gens)
    (mapS F gens fun GM => treeGo mul GM (lenL gens) tr [ONE] 1 0 0 fun ks n =>
      andB (Nat.beq n nQ) (andB (nodupN ks) (linesGo mul ONE pool F lines fun pks =>
        andB (coverOK ONE ks pks) (mapS (specM mul ONE F) wl fun WM =>
          andB (fuseOK mul ONE pool F (lenL wl) WM Y fuse pks)
            (witsOK mul ONE pool F G Y wits wl WM)))))

theorem treeGo_mono {mul : Nat → Nat → Nat} {GM : List Nat} {ng : Nat}
    {k k' : List Nat → Nat → Bool} (hk : ∀ ks n, k ks n = true → k' ks n = true) :
    ∀ (tr ks : List Nat) (n h l : Nat), treeGo mul GM ng tr ks n h l k = true →
      treeGo mul GM ng tr ks n h l k' = true
  | [], ks, n, h, l, H => by
    obtain ⟨h1, h2⟩ := andB_trueH (a := Nat.beq h n) H
    obtain ⟨h2, h3⟩ := andB_trueH h2
    change andB (Nat.beq h n) (andB (Nat.beq l 0) (k' ks n)) = true
    rw [h1, h2, hk ks n h3]
    rfl
  | t :: tr, ks, n, h, l, H => by
    obtain ⟨h1, h2⟩ := andB_trueH (a := Nat.blt h n) H
    obtain ⟨h2, h3⟩ := andB_trueH h2
    change andB (Nat.blt h n) (andB (Nat.blt l ng)
      (sB (mul (nthD 0 GM l) (nthD 0 ks (Nat.sub (Nat.sub n 1) h))) fun x =>
        (fun (nx : List Nat → Nat → Bool) => Bool.rec (motive := fun _ => Bool)
            (andB (Nat.ble t n) (andB (Nat.beq x (nthD 0 ks (Nat.sub n t))) (nx ks n)))
            (nx (List.cons x ks) (Nat.succ n)) (Nat.beq t 0))
          (fun ks' n' => Bool.rec (motive := fun _ => Bool)
            (treeGo mul GM ng tr ks' n' h (Nat.succ l) k')
            (treeGo mul GM ng tr ks' n' (Nat.succ h) 0 k') (Nat.beq (Nat.succ l) ng)))) = true
    change sB (mul (nthD 0 GM l) (nthD 0 ks (Nat.sub (Nat.sub n 1) h))) (fun x =>
        (fun (nx : List Nat → Nat → Bool) => Bool.rec (motive := fun _ => Bool)
            (andB (Nat.ble t n) (andB (Nat.beq x (nthD 0 ks (Nat.sub n t))) (nx ks n)))
            (nx (List.cons x ks) (Nat.succ n)) (Nat.beq t 0))
          (fun ks' n' => Bool.rec (motive := fun _ => Bool)
            (treeGo mul GM ng tr ks' n' h (Nat.succ l) k)
            (treeGo mul GM ng tr ks' n' (Nat.succ h) 0 k) (Nat.beq (Nat.succ l) ng))) = true at h3
    rw [h1, h2]
    rw [sB_eqH] at h3 ⊢
    have hn : ∀ ks' n', Bool.rec (motive := fun _ => Bool)
        (treeGo mul GM ng tr ks' n' h (Nat.succ l) k)
        (treeGo mul GM ng tr ks' n' (Nat.succ h) 0 k) (Nat.beq (Nat.succ l) ng) = true →
        Bool.rec (motive := fun _ => Bool)
        (treeGo mul GM ng tr ks' n' h (Nat.succ l) k')
        (treeGo mul GM ng tr ks' n' (Nat.succ h) 0 k') (Nat.beq (Nat.succ l) ng) = true := by
      intro ks' n'
      cases Nat.beq (Nat.succ l) ng
      · exact treeGo_mono hk tr ks' n' h (Nat.succ l)
      · exact treeGo_mono hk tr ks' n' (Nat.succ h) 0
    revert h3
    dsimp only
    cases Nat.beq t 0
    · intro h3
      obtain ⟨h4, h5⟩ := andB_trueH h3
      obtain ⟨h5, h6⟩ := andB_trueH h5
      change andB _ (andB _ _) = true
      rw [h4, h5, hn ks n h6]
      rfl
    · exact hn _ _

theorem linesGo_mono {mul : Nat → Nat → Nat} {ONE : Nat} {pool : List (List Nat)}
    {F : Nat → Nat} : ∀ (lines : List (List (Nat × Nat))) (k k' : List (List Nat) → Bool),
      (∀ ps, k ps = true → k' ps = true) → linesGo mul ONE pool F lines k = true →
        linesGo mul ONE pool F lines k' = true
  | [], _, _, hk, H => hk _ H
  | s :: ss, k, k', hk, H => by
    obtain ⟨h1, h2⟩ := andB_trueH (a := evS pool s) H
    change andB (evS pool s) (sB (specM mul ONE F s) fun x1 => sB (mul x1 x1) fun x2 =>
      sB (mul x2 x1) fun x3 => sB (mul x3 x1) fun x4 =>
        andB (Nat.beq (mul x4 x1) ONE) (andB (notB (Nat.beq x1 ONE))
          (linesGo mul ONE pool F ss fun ps => k' (List.cons [x1, x2, x3, x4] ps)))) = true
    change sB (specM mul ONE F s) (fun x1 => sB (mul x1 x1) fun x2 =>
      sB (mul x2 x1) fun x3 => sB (mul x3 x1) fun x4 =>
        andB (Nat.beq (mul x4 x1) ONE) (andB (notB (Nat.beq x1 ONE))
          (linesGo mul ONE pool F ss fun ps => k (List.cons [x1, x2, x3, x4] ps)))) = true at h2
    rw [sB_eqH, sB_eqH, sB_eqH, sB_eqH] at h2
    rw [h1, sB_eqH, sB_eqH, sB_eqH, sB_eqH]
    obtain ⟨h3, h4⟩ := andB_trueH h2
    obtain ⟨h4, h5⟩ := andB_trueH h4
    rw [h3, h4, linesGo_mono ss _ _ (fun ps hp => hk _ hp) h5]
    rfl

theorem restK_of {mul : Nat → Nat → Nat} {ONE : Nat} {pool : List (List Nat)}
    {gens : List Nat} {nQ : Nat} {lines : List (List (Nat × Nat))}
    {fuse : List (Nat × (List (Nat × Nat) × Nat))} {wl : List (List (Nat × Nat))}
    {wits : List (List (List (Nat × Nat)) × Nat)} {tr : List Nat} {F G : Nat → Nat}
    (KS : List Nat) (PKS : List (List Nat)) (WM : List Nat)
    (hg : allL (fun j => andB (evC (nthD List.nil pool j))
      (Nat.beq (mul (F j) (F 0)) (mul (F 0) (F j)))) gens = true)
    (hT : treeGo mul (gens.map F) (lenL gens) tr [ONE] 1 0 0
      (fun ks n => andB (ks == KS) (Nat.beq n nQ)) = true)
    (hN : nodupN KS = true) (hL : linesGo mul ONE pool F lines (fun pks => pks == PKS) = true)
    (hC : coverOK ONE KS PKS = true) (hW : wl.map (specM mul ONE F) = WM)
    (hF : fuseOK mul ONE pool F (lenL wl) WM (F 0) fuse PKS = true)
    (hX : witsOK mul ONE pool F G (F 0) wits wl WM = true) :
    restK mul ONE pool gens nQ lines fuse wl wits tr F G = true := by
  unfold restK
  rw [sB_eqH, mapS_eqH, hg]
  refine treeGo_mono (fun ks n hkn => ?_) _ _ _ _ _ hT
  obtain ⟨e1, e2⟩ := andB_trueH hkn
  rw [beq_iff_eq] at e1
  rw [Nat.beq_eq] at e2
  rw [e1, e2, hN, Nat.beq_refl]
  refine linesGo_mono _ _ _ (fun pks hp => ?_) hL
  rw [beq_iff_eq] at hp
  rw [hp, hC, mapS_eqH, hW, hF, hX]
  rfl

@[expose] noncomputable def invWA (cs : List Nat) : List Nat → List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun c _ ih acc => ih (List.append (invC c) acc)) cs

theorem invWA_eq : ∀ (cs acc : List Nat), invWA cs acc = invW cs ++ acc
  | [], _ => rfl
  | c :: cs, acc => by
    change invWA cs (List.append (invC c) acc) = List.append (invW cs) (invC c) ++ acc
    rw [invWA_eq cs]
    exact (List.append_assoc _ _ _).symm

@[expose] noncomputable def gdL (c k : Nat) : Bool :=
  orB (okC c) (andB (Nat.ble 37 c) (Nat.blt c (Nat.add 37 k)))

@[expose] noncomputable def slpR (mul : Nat → Nat → Nat) (L : Nat → Nat) (E : Nat → List Nat)
    (RA RB : List Nat) (k : Nat) : Bool :=
  andB (gdL (nthD 0 RA k) k) (andB (gdL (nthD 0 RB k) k)
    (andB (Nat.beq (mul (L (nthD 0 RA k)) (L (nthD 0 RB k))) (L (Nat.add 37 k)))
      (List.append (E (nthD 0 RA k)) (E (nthD 0 RB k)) == E (Nat.add 37 k))))

@[expose] noncomputable def gRng (mul : Nat → Nat → Nat) (ONE : Nat) (L : Nat → Nat)
    (pool : List (List Nat)) (lo hi : Nat) (GL : List Nat) (j : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (wordP mul ONE L (invW (nthD List.nil pool j))) (nthD ONE GL j)
    (andB (Nat.ble lo j) (Nat.blt j hi))

theorem gRng_eq {mul : Nat → Nat → Nat} {ONE : Nat} {L : Nat → Nat} {pool : List (List Nat)}
    {lo hi : Nat} {GL : List Nat}
    (h : ∀ j, lo ≤ j → j < hi → wordP mul ONE L (invW (nthD List.nil pool j)) = nthD ONE GL j) :
    (fun j => wordP mul ONE L (invW (nthD List.nil pool j))) = gRng mul ONE L pool lo hi GL := by
  funext j
  unfold gRng
  by_cases h1 : lo ≤ j
  · by_cases h2 : j < hi
    · rw [Nat.ble_eq_true_of_le h1, Nat.blt_eq.mpr h2]
      exact h j h1 h2
    · have e : Nat.blt j hi = false := Bool.eq_false_iff.mpr fun h => h2 (Nat.blt_eq.mp h)
      rw [e]
      cases Nat.ble lo j <;> rfl
  · have e : Nat.ble lo j = false := Bool.eq_false_iff.mpr fun h => h1 (Nat.le_of_ble_eq_true h)
    rw [e]
    rfl

theorem chk_of {mul : Nat → Nat → Nat} {ONE : Nat} {L : Nat → Nat} {pool : List (List Nat)}
    {gens : List Nat} {nQ : Nat} {lines : List (List (Nat × Nat))}
    {fuse : List (Nat × (List (Nat × Nat) × Nat))} {wl : List (List (Nat × Nat))}
    {wits : List (List (List (Nat × Nat)) × Nat)} {tr : List Nat} (PM : List Nat) (G : Nat → Nat)
    (hA : alphOK mul ONE L = true) (hC : allL (allL okC) pool = true)
    (hPM : pool.map (wordP mul ONE L) = PM)
    (hG : (fun j => wordP mul ONE L (invW (nthD List.nil pool j))) = G)
    (hR : restK mul ONE pool gens nQ lines fuse wl wits tr (nthD ONE PM) G = true) :
    chk mul ONE L pool gens nQ lines fuse wl wits tr = true := by
  unfold chk
  rw [mapS_eqH]
  change andB (alphOK mul ONE L) (andB (allL (allL okC) pool)
    (restK mul ONE pool gens nQ lines fuse wl wits tr (nthD ONE (pool.map (wordP mul ONE L)))
      (fun j => wordP mul ONE L (invW (nthD List.nil pool j))))) = true
  rw [hPM, hG, hA, hC, hR]
  rfl

end CFSG.KC.HNClsL

end
