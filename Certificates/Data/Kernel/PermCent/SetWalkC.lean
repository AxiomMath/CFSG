module

public import Certificates.Data.Kernel.PermCent.CV

public section

namespace CFSG.Certificates.Kernel.PkCV

open CFSG.KC.Enum

variable {n : Nat}

@[expose] def inMS (M x : Nat) : Bool := Nat.blt 0 (Nat.land M (Nat.shiftLeft 1 x))

@[expose] noncomputable def closedS (M : Nat) (t : CV n) : Bool :=
  allN n fun x => Bool.rec true (inMS M (img n t.1 x)) (inMS M x)

@[expose] noncomputable def subS (n F M : Nat) : Bool := allN n fun x => Bool.rec true (inMS M x) (inMS F x)

@[expose] noncomputable def masksS (F : Nat) (L : List (List (CV n) × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun hd tl ih => subS n F hd.2 && (tl.all fun e => e.1.all (closedS hd.2)) && ih) L

@[expose] noncomputable def imgsS (n t : Nat) (as : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun a _ ih => img n t a :: ih) as

@[expose] def allInS (M : Nat) (as : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => Bool.rec false ih (inMS M a)) as

variable [Small n]

@[expose] noncomputable def walkS (body : CV n → Bool) (L : List (List (CV n) × Nat)) :
    CV n → List Nat → Bool :=
  List.rec (motive := fun _ => CV n → List Nat → Bool) (fun p _ => body p)
    (fun hd _ ih p as => hd.1.all fun t => strictB (t⁻¹).1 fun ti =>
      Bool.rec true (ih (p * t) (imgsS n ti as)) (allInS hd.2 (imgsS n ti as))) L

@[expose] noncomputable def fixS (F : Nat) (S G : List (CV n)) : Bool :=
  (G.all fun s => decide (s ∈ S)) &&
    (S.all fun s => allN n fun x => !inMS F x || Nat.beq (img n s.1 x) x) &&
    allN n fun x => !(G.all fun s => Nat.beq (img n s.1 x) x) || inMS F x

theorem strictB_eqS (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem walkS_cons (body : CV n → Bool) (T : List (CV n)) (M : Nat) (tl : List (List (CV n) × Nat))
    (p : CV n) (as : List Nat) : walkS body ((T, M) :: tl) p as = T.all fun t =>
      strictB (t⁻¹).1 fun ti =>
        Bool.rec true (walkS body tl (p * t) (imgsS n ti as)) (allInS M (imgsS n ti as)) := rfl

theorem masksS_cons (F : Nat) (T : List (CV n)) (M : Nat) (tl : List (List (CV n) × Nat)) :
    masksS F ((T, M) :: tl) =
      (subS n F M && (tl.all fun e => e.1.all (closedS M)) && masksS F tl) := rfl

theorem fixS_sub {F : Nat} {S G : List (CV n)} (hf : fixS F S G = true) :
    (G.all fun s => decide (s ∈ S)) = true := by
  rw [fixS, Bool.and_eq_true, Bool.and_eq_true] at hf
  exact hf.1.1

theorem allInS_iff (M : Nat) {α : Type*} (g : α → Nat) :
    ∀ fs : List α, allInS M (fs.map g) = true ↔ ∀ f ∈ fs, inMS M (g f) = true
  | [] => by simp [allInS]
  | f :: fs => by
    have ih := allInS_iff M g fs
    change Bool.rec false (allInS M (fs.map g)) (inMS M (g f)) = true ↔ _
    cases h : inMS M (g f)
    · simp [h]
    · simp only [List.mem_cons, forall_eq_or_imp, h, true_and]
      exact ih

theorem closedS_apply {M : Nat} {t : CV n} (h : closedS M t = true) (x : Fin n)
    (hx : inMS M x = true) : inMS M (ev t x) = true := by
  rw [closedS, CFSG.KS.PK.allN_iff] at h
  have h' := h x x.2
  beta_reduce at h'
  rw [hx] at h'
  exact h'

theorem subS_apply {F M : Nat} (h : subS n F M = true) (x : Fin n) (hx : inMS F x = true) :
    inMS M x = true := by
  rw [subS, CFSG.KS.PK.allN_iff] at h
  have h' := h x x.2
  beta_reduce at h'
  rw [hx] at h'
  exact h'

theorem prod_closedS (M : Nat) : ∀ Ls : List (List (CV n)),
    (∀ e ∈ Ls, ∀ t ∈ e, closedS M t = true) →
    ∀ r ∈ productsC Ls, ∀ x : Fin n, inMS M x = true → inMS M (ev r x) = true
  | [], _, r, hr, x, hx => by
    rw [productsC, List.mem_singleton] at hr
    rw [hr, ev_one, Equiv.Perm.one_apply]
    exact hx
  | T :: Ts, h, r, hr, x, hx => by
    rw [productsC, List.mem_flatMap] at hr
    obtain ⟨t, ht, hr⟩ := hr
    obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
    rw [ev_mul, Equiv.Perm.mul_apply]
    exact closedS_apply (h T (List.mem_cons.2 (Or.inl rfl)) t ht) _
      (prod_closedS M Ts (fun e he => h e (List.mem_cons_of_mem _ he)) r' hr' x hx)

theorem pre_inS {F M : Nat} (hs : subS n F M = true) {Ls : List (List (CV n))}
    (hc : ∀ e ∈ Ls, ∀ t ∈ e, closedS M t = true) (q r : CV n) (hr : r ∈ productsC Ls) (y : Fin n)
    (hy : inMS F ((ev (q * r))⁻¹ y) = true) : inMS M ((ev q)⁻¹ y) = true := by
  have e : (ev q)⁻¹ y = ev r ((ev (q * r))⁻¹ y) := by
    rw [ev_mul, mul_inv_rev, Equiv.Perm.mul_apply]
    exact (Equiv.apply_symm_apply (ev r) _).symm
  rw [e]
  exact prod_closedS M Ls hc r hr _ (subS_apply hs _ hy)

theorem inv_stepS (p t : CV n) (y : Fin n) :
    img n (t⁻¹).1 ((ev p)⁻¹ y) = ((ev (p * t))⁻¹ y : Nat) := by
  rw [ev_mul, mul_inv_rev, Equiv.Perm.mul_apply, ← ev_inv]
  rfl

theorem imgsS_map (p t : CV n) : ∀ fs : List (Fin n),
    imgsS n (t⁻¹).1 (fs.map fun f => ((ev p)⁻¹ f : Nat)) = fs.map fun f => ((ev (p * t))⁻¹ f : Nat)
  | [] => rfl
  | f :: fs => by
    change img n (t⁻¹).1 ((ev p)⁻¹ f) :: imgsS n (t⁻¹).1 (fs.map fun f => ((ev p)⁻¹ f : Nat)) = _
    rw [inv_stepS, imgsS_map p t fs]
    rfl

theorem walkS_sound (body : CV n → Bool) (F : Nat) (fs : List (Fin n)) :
    ∀ (L : List (List (CV n) × Nat)) (p : CV n) (as : List Nat), masksS F L = true →
      walkS body L p as = true → as = fs.map (fun f => ((ev p)⁻¹ f : Nat)) →
      ∀ u ∈ productsC (L.map Prod.fst), (∀ f ∈ fs, inMS F ((ev (p * u))⁻¹ f) = true) →
        body (p * u) = true
  | [], p, as, _, hw, _, u, hu, _ => by
    rw [List.map_nil, productsC, List.mem_singleton] at hu
    rw [hu, mul_one]
    exact hw
  | (T, M) :: tl, p, as, hm, hw, ha, u, hu, hg => by
    rw [masksS_cons, Bool.and_eq_true, Bool.and_eq_true] at hm
    obtain ⟨⟨hs, hc⟩, hm⟩ := hm
    have hc' : ∀ e ∈ tl.map Prod.fst, ∀ t ∈ e, closedS M t = true := by
      intro e he t ht
      obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
      exact List.all_eq_true.1 (List.all_eq_true.1 hc e' he') t ht
    rw [List.map_cons, productsC, List.mem_flatMap] at hu
    obtain ⟨t, ht, hu⟩ := hu
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hu
    simp only [← mul_assoc] at hg ⊢
    rw [walkS_cons, List.all_eq_true] at hw
    have hw' := hw t ht
    rw [strictB_eqS] at hw'
    have ea : imgsS n (t⁻¹).1 as = fs.map fun f => ((ev (p * t))⁻¹ f : Nat) := by
      rw [ha]; exact imgsS_map p t fs
    have ia : allInS M (imgsS n (t⁻¹).1 as) = true := by
      rw [ea, allInS_iff]
      intro f hf
      exact pre_inS hs hc' (p * t) r hr f (hg f hf)
    rw [ia] at hw'
    exact walkS_sound body F fs tl (p * t) _ hm hw' ea r hr hg

@[expose] noncomputable def foldF (M : Nat) (k : CV n → List Nat → Nat → Nat) (p : CV n)
    (as : List Nat) (ts : List (CV n)) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun t _ ihT acc => strictN (strictN (t⁻¹).1 fun ti =>
      Bool.rec acc (k (p * t) (imgsS n ti as) acc) (allInS M (imgsS n ti as))) ihT) ts

@[expose] noncomputable def walkF (body : CV n → Nat) (L : List (List (CV n) × Nat)) :
    CV n → List Nat → Nat → Nat :=
  List.rec (motive := fun _ => CV n → List Nat → Nat → Nat) (fun p _ acc => Nat.lor acc (body p))
    (fun hd _ ih p as => foldF hd.2 ih p as hd.1) L

@[expose] noncomputable def bitsF {α : Type*} (f : α → Bool) (xs : List α) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun x _ ih k => Nat.lor (Bool.rec 0 (Nat.shiftLeft 1 k) (f x)) (ih (Nat.succ k))) xs

@[expose] noncomputable def coverF {α : Type*} (g : α → Bool) (r : Nat) (xs : List α) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih k => Bool.rec true (inMS r k) (g x) && ih (Nat.succ k)) xs

theorem strictN_eqS (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem inMS_iff {M k : Nat} : inMS M k = true ↔ M.testBit k = true := by
  change Nat.blt 0 (M &&& (1 <<< k)) = true ↔ _
  rw [Nat.one_shiftLeft, Nat.blt_eq]
  constructor
  · intro h
    cases hb : M.testBit k
    · exfalso
      have h0 : M &&& 2 ^ k = 0 := Nat.eq_of_testBit_eq fun i => by
        rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
        by_cases hi : k = i
        · subst hi
          simp [hb]
        · simp [hi]
      omega
    · rfl
  · intro h
    apply Nat.pos_iff_ne_zero.mpr
    intro h0
    have := Nat.testBit_and M (2 ^ k) k
    rw [h0, Nat.zero_testBit, h, Nat.testBit_two_pow_self] at this
    cases this

theorem inMS_lor {a b k : Nat} (h : inMS (Nat.lor a b) k = true) :
    inMS a k = true ∨ inMS b k = true := by
  rw [inMS_iff, inMS_iff]
  rw [inMS_iff] at h
  change (a ||| b).testBit k = true at h
  rw [Nat.testBit_or, Bool.or_eq_true] at h
  exact h

theorem not_inMS_zero (k : Nat) : inMS 0 k = false := by
  cases h : inMS 0 k
  · rfl
  · rw [inMS_iff, Nat.zero_testBit] at h
    cases h

theorem foldF_sound (M : Nat) (k : CV n → List Nat → Nat → Nat) (p : CV n) (as : List Nat)
    (j : Nat) (X : CV n → Prop) : ∀ ts : List (CV n),
    (∀ t ∈ ts, ∀ as' acc, inMS (k (p * t) as' acc) j = true → inMS acc j = true ∨ X t) →
    ∀ acc, inMS (foldF M k p as ts acc) j = true → inMS acc j = true ∨ ∃ t ∈ ts, X t
  | [], _, acc, h => Or.inl h
  | t :: ts, hk, acc, h => by
    change inMS (strictN (strictN (t⁻¹).1 fun ti =>
      Bool.rec acc (k (p * t) (imgsS n ti as) acc) (allInS M (imgsS n ti as)))
        (foldF M k p as ts)) j = true at h
    rw [strictN_eqS, strictN_eqS] at h
    rcases foldF_sound M k p as j X ts (fun t' ht' => hk t' (List.mem_cons_of_mem _ ht')) _ h with
      h | ⟨t', ht', hx⟩
    · cases hb : allInS M (imgsS n (t⁻¹).1 as)
      · rw [hb] at h
        exact Or.inl h
      · rw [hb] at h
        rcases hk t (List.mem_cons_self ..) _ acc h with h | h
        · exact Or.inl h
        · exact Or.inr ⟨t, List.mem_cons_self .., h⟩
    · exact Or.inr ⟨t', List.mem_cons_of_mem _ ht', hx⟩

theorem walkF_sound (body : CV n → Nat) (j : Nat) :
    ∀ (L : List (List (CV n) × Nat)) (p : CV n) (as : List Nat) (acc : Nat),
      inMS (walkF body L p as acc) j = true →
      inMS acc j = true ∨ ∃ u ∈ productsC (L.map Prod.fst), inMS (body (p * u)) j = true
  | [], p, as, acc, h => by
    rcases inMS_lor h with h | h
    · exact Or.inl h
    · refine Or.inr ⟨1, ?_, ?_⟩
      · rw [List.map_nil, productsC, List.mem_singleton]
      · rwa [mul_one]
  | (T, M) :: tl, p, as, acc, h => by
    change inMS (foldF M (walkF body tl) p as T acc) j = true at h
    rcases foldF_sound M (walkF body tl) p as j
      (fun t => ∃ r ∈ productsC (tl.map Prod.fst), inMS (body (p * t * r)) j = true) T
      (fun t _ as' acc' h' => walkF_sound body j tl (p * t) as' acc' h') acc h with
      h | ⟨t, ht, r, hr, hb⟩
    · exact Or.inl h
    · refine Or.inr ⟨t * r, ?_, ?_⟩
      · rw [List.map_cons, productsC, List.mem_flatMap]
        exact ⟨t, ht, List.mem_map.2 ⟨r, hr, rfl⟩⟩
      · rwa [← mul_assoc]

theorem bitsF_sound {α : Type*} (f : α → Bool) : ∀ (xs : List α) (k j : Nat),
    inMS (bitsF f xs k) j = true → ∃ i, j = k + i ∧ ∃ h : i < xs.length, f xs[i] = true
  | [], k, j, h => by
    change inMS 0 j = true at h
    rw [not_inMS_zero] at h
    cases h
  | x :: xs, k, j, h => by
    change inMS (Nat.lor (Bool.rec 0 (Nat.shiftLeft 1 k) (f x)) (bitsF f xs (Nat.succ k))) j = true
      at h
    rcases inMS_lor h with h | h
    · cases hf : f x
      · rw [hf] at h
        change inMS 0 j = true at h
        rw [not_inMS_zero] at h
        cases h
      · rw [hf] at h
        change inMS (1 <<< k) j = true at h
        rw [inMS_iff, Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_iff] at h
        exact ⟨0, by omega, by simp, by simpa using hf⟩
    · obtain ⟨i, hi, hl, hx⟩ := bitsF_sound f xs (Nat.succ k) j h
      exact ⟨i + 1, by omega, by simpa using hl, by simpa using hx⟩

theorem coverF_sound {α : Type*} (g : α → Bool) (r : Nat) : ∀ (xs : List α) (k : Nat),
    coverF g r xs k = true → ∀ i (h : i < xs.length), g xs[i] = true → inMS r (k + i) = true
  | [], _, _, i, h, _ => by simp at h
  | x :: xs, k, hc, i, h, hg => by
    change (Bool.rec true (inMS r k) (g x) && coverF g r xs (Nat.succ k)) = true at hc
    rw [Bool.and_eq_true] at hc
    cases i with
    | zero =>
      have hx : g x = true := by simpa using hg
      rw [hx] at hc
      simpa using hc.1
    | succ i =>
      have := coverF_sound g r xs (Nat.succ k) hc.2 i (by simpa using h) (by simpa using hg)
      rwa [Nat.succ_add, ← Nat.add_succ] at this

theorem good_of_nrmS {F : Nat} {S G : List (CV n)} (hf : fixS F S G = true) (g : CV n)
    (hn : (G.all fun s => decide (g * s * g⁻¹ ∈ S)) = true) (y : Fin n) (hy : inMS F y = true) :
    inMS F ((ev g)⁻¹ y) = true := by
  rw [fixS, Bool.and_eq_true, Bool.and_eq_true] at hf
  obtain ⟨⟨_, hS⟩, hA⟩ := hf
  rw [CFSG.KS.PK.allN_iff] at hA
  have hfix : ∀ s ∈ S, ev s y = y := by
    intro s hs
    have h := List.all_eq_true.1 hS s hs
    rw [CFSG.KS.PK.allN_iff] at h
    have h' := h y y.2
    beta_reduce at h'
    rw [hy, Bool.not_true, Bool.false_or, Nat.beq_eq] at h'
    exact Fin.ext h'
  set x := (ev g)⁻¹ y
  have hx : ∀ s ∈ G, ev s x = x := by
    intro s hs
    have hm := of_decide_eq_true (List.all_eq_true.1 hn s hs)
    have e := hfix _ hm
    rw [ev_mul, ev_mul, ev_inv, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply] at e
    calc ev s x = (ev g)⁻¹ (ev g (ev s x)) := (Equiv.symm_apply_apply (ev g) _).symm
      _ = x := by rw [e]
  have h := hA x x.2
  beta_reduce at h
  have hG : (G.all fun s => Nat.beq (img n s.1 x) x) = true :=
    List.all_eq_true.2 fun s hs => Nat.beq_eq.mpr (congrArg Fin.val (hx s hs))
  rw [hG, Bool.not_true, Bool.false_or] at h
  exact h

end CFSG.Certificates.Kernel.PkCV

end
