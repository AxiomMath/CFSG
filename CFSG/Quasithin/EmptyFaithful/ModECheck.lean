module

public import CFSG.Quasithin.EmptyFaithful.ModEData
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.ModE

@[expose] def memB (x : ℕ) (L : List ℕ) : Bool :=
  List.rec false (fun y _ ih => Bool.or (Nat.beq y x) ih) L

@[expose] def nodupB (L : List ℕ) : Bool :=
  List.rec true (fun x xs ih => Bool.and (Bool.not (memB x xs)) ih) L

@[expose] def allB (p : ℕ → Bool) (L : List ℕ) : Bool :=
  List.rec true (fun x _ ih => Bool.and (p x) ih) L

@[expose] def cntB (p : ℕ → Bool) (L : List ℕ) : ℕ :=
  List.rec 0 (fun x _ ih => Nat.add (cond (p x) 1 0) ih) L

theorem memB_cons (x y : ℕ) (L : List ℕ) : memB x (y :: L) = (Nat.beq y x || memB x L) := rfl

theorem memB_iff {x : ℕ} {L : List ℕ} : memB x L = true ↔ x ∈ L := by
  induction L with
  | nil => exact ⟨fun h => Bool.noConfusion h, fun h => (List.not_mem_nil h).elim⟩
  | cons y l ih =>
    rw [memB_cons, Bool.or_eq_true, ih, List.mem_cons]
    exact or_congr_left ⟨fun h => (Nat.eq_of_beq_eq_true h).symm, fun h => h ▸ Nat.beq_refl _⟩

theorem nodupB_cons (x : ℕ) (L : List ℕ) : nodupB (x :: L) = (!(memB x L) && nodupB L) := rfl

theorem nodupB_iff {L : List ℕ} : nodupB L = true ↔ L.Nodup := by
  induction L with
  | nil => exact ⟨fun _ => List.nodup_nil, fun _ => rfl⟩
  | cons x xs ih =>
    rw [nodupB_cons, Bool.and_eq_true, ih, List.nodup_cons, Bool.not_eq_true', ← Bool.not_eq_true,
      memB_iff]

theorem allB_cons (p : ℕ → Bool) (x : ℕ) (L : List ℕ) : allB p (x :: L) = (p x && allB p L) := rfl

theorem allB_iff {p : ℕ → Bool} {L : List ℕ} : allB p L = true ↔ ∀ x ∈ L, p x = true := by
  induction L with
  | nil => exact ⟨fun _ x hx => (List.not_mem_nil hx).elim, fun _ => rfl⟩
  | cons x xs ih =>
    rw [allB_cons, Bool.and_eq_true, ih]
    exact ⟨fun h y hy => by
        rcases List.mem_cons.1 hy with rfl | hy
        · exact h.1
        · exact h.2 y hy,
      fun h => ⟨h x (List.mem_cons_self ..), fun y hy => h y (List.mem_cons_of_mem _ hy)⟩⟩

theorem cntB_cons (p : ℕ → Bool) (x : ℕ) (L : List ℕ) :
    cntB p (x :: L) = Nat.add (cond (p x) 1 0) (cntB p L) := rfl

theorem cntB_eq {p : ℕ → Bool} {L : List ℕ} : cntB p L = (L.filter p).length := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    rw [cntB_cons, ih, List.filter_cons]
    cases h : p x <;> simp [Nat.add_comm]

attribute [irreducible] memB nodupB allB cntB

@[expose] def wP (w : List ℕ) : Equiv.Perm (Fin 24) := w.foldl (fun acc k => acc * lt.getD k 1) 1

@[expose] def wK (w : List ℕ) : ℕ := w.foldl (fun acc k => comp acc (ltK.getD k kId)) kId

theorem pk_lt : lt.map pk = ltK := by decide +kernel

theorem pk_getD (l : List (Equiv.Perm (Fin 24))) (n : ℕ) :
    pk (l.getD n 1) = (l.map pk).getD n kId := by
  have h := List.getD_map l 1 (n := n) pk
  rw [pk_one] at h
  exact h.symm

theorem pk_lt_getD (k : ℕ) : pk (lt.getD k 1) = ltK.getD k kId := by
  rw [pk_getD, pk_lt]

theorem pk_foldl (w : List ℕ) (acc : Equiv.Perm (Fin 24)) :
    pk (w.foldl (fun a k => a * lt.getD k 1) acc) =
      w.foldl (fun a k => comp a (ltK.getD k kId)) (pk acc) := by
  induction w generalizing acc with
  | nil => rw [List.foldl_nil, List.foldl_nil]
  | cons k w ih =>
    rw [List.foldl_cons, List.foldl_cons, ih, pk_mul, pk_lt_getD]

theorem pk_wP (w : List ℕ) : pk (wP w) = wK w := by
  rw [wP, wK, pk_foldl, pk_one]

@[expose] def chainR (Lk : List ℕ) (tab : List (ℕ × ℕ × ℕ)) (pre : List ℕ) : Bool :=
  List.rec (motive := fun _ => List ℕ → Bool) (fun _ => true)
    (fun e _ ih pre =>
      Bool.and (Bool.and (memB e.2.1 pre) (Nat.blt e.2.2 6))
        (Bool.and (Nat.beq e.1 (comp e.2.1 (Lk.getD e.2.2 kId))) (ih (e.1 :: pre)))) tab pre

theorem chainR_cons (Lk : List ℕ) (e : ℕ × ℕ × ℕ) (tab : List (ℕ × ℕ × ℕ)) (pre : List ℕ) :
    chainR Lk (e :: tab) pre =
      (memB e.2.1 pre && Nat.blt e.2.2 6 &&
        (Nat.beq e.1 (comp e.2.1 (Lk.getD e.2.2 kId)) && chainR Lk tab (e.1 :: pre))) := rfl

theorem chainR_spec (L : List (Equiv.Perm (Fin 24))) (hlen : L.length = 6)
    (H : Subgroup (Equiv.Perm (Fin 24))) (hL : ∀ x ∈ L, x ∈ H) :
    ∀ (tab : List (ℕ × ℕ × ℕ)) (pre : List ℕ), chainR (L.map pk) tab pre = true →
      (∀ c ∈ pre, ∃ e ∈ H, pk e = c) → ∀ c ∈ tab.map (fun t => t.1) ++ pre, ∃ e ∈ H, pk e = c := by
  intro tab
  induction tab with
  | nil =>
    intro pre _ hpre c hc
    exact hpre c (by simpa using hc)
  | cons e tab ih =>
    intro pre h hpre c hc
    rw [chainR_cons, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨hmem, hk⟩, hbeq, hrest⟩ := h
    have hk6 : e.2.2 < 6 := Nat.le_of_ble_eq_true hk
    obtain ⟨x, hxH, hx⟩ := hpre _ (memB_iff.1 hmem)
    have hLk : L.getD e.2.2 1 ∈ H := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact hL _ (List.getElem_mem _)
    have hnew : ∃ y ∈ H, pk y = e.1 := by
      refine ⟨x * L.getD e.2.2 1, H.mul_mem hxH hLk, ?_⟩
      rw [pk_mul, hx, pk_getD]
      exact (Nat.eq_of_beq_eq_true hbeq).symm
    have ih' := ih (e.1 :: pre) hrest (by
      intro c' hc'
      rcases List.mem_cons.1 hc' with rfl | hc'
      · exact hnew
      · exact hpre c' hc')
    refine ih' c ?_
    simp only [List.map_cons, List.cons_append, List.mem_cons, List.mem_append] at hc ⊢
    tauto

@[expose] def chainC (Lk : List ℕ) (tab : List (ℕ × ℕ × ℕ)) (pre : List ℕ) : Bool :=
  List.rec (motive := fun _ => List ℕ → Bool) (fun _ => true)
    (fun e _ ih pre =>
      Bool.and (Bool.and (memB e.2.1 pre) (Nat.blt e.2.2 6))
        (Bool.and (Nat.beq e.1 (comp (comp (Lk.getD e.2.2 kId) e.2.1)
          (Lk.getD (Nat.mod (Nat.add e.2.2 3) 6) kId))) (ih (e.1 :: pre)))) tab pre

theorem chainC_cons (Lk : List ℕ) (e : ℕ × ℕ × ℕ) (tab : List (ℕ × ℕ × ℕ)) (pre : List ℕ) :
    chainC Lk (e :: tab) pre =
      (memB e.2.1 pre && Nat.blt e.2.2 6 &&
        (Nat.beq e.1 (comp (comp (Lk.getD e.2.2 kId) e.2.1)
          (Lk.getD (Nat.mod (Nat.add e.2.2 3) 6) kId)) && chainC Lk tab (e.1 :: pre))) := rfl

theorem chainC_spec (L : List (Equiv.Perm (Fin 24))) (hlen : L.length = 6)
    (H : Subgroup (Equiv.Perm (Fin 24))) (hL : ∀ x ∈ L, x ∈ H)
    (hinv : ∀ k < 6, L.getD ((k + 3) % 6) 1 = (L.getD k 1)⁻¹) (z : Equiv.Perm (Fin 24)) :
    ∀ (tab : List (ℕ × ℕ × ℕ)) (pre : List ℕ), chainC (L.map pk) tab pre = true →
      (∀ c ∈ pre, ∃ y, (∃ g ∈ H, y = g * z * g⁻¹) ∧ pk y = c) →
      ∀ c ∈ tab.map (fun t => t.1) ++ pre, ∃ y, (∃ g ∈ H, y = g * z * g⁻¹) ∧ pk y = c := by
  intro tab
  induction tab with
  | nil =>
    intro pre _ hpre c hc
    exact hpre c (by simpa using hc)
  | cons e tab ih =>
    intro pre h hpre c hc
    rw [chainC_cons, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨hmem, hk⟩, hbeq, hrest⟩ := h
    have hk6 : e.2.2 < 6 := Nat.le_of_ble_eq_true hk
    obtain ⟨x, ⟨g, hgH, rfl⟩, hx⟩ := hpre _ (memB_iff.1 hmem)
    have hLk : L.getD e.2.2 1 ∈ H := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact hL _ (List.getElem_mem _)
    have hLk' : L.getD ((e.2.2 + 3) % 6) 1 = (L.getD e.2.2 1)⁻¹ := hinv _ hk6
    have hnew : ∃ y, (∃ g' ∈ H, y = g' * z * g'⁻¹) ∧ pk y = e.1 := by
      refine ⟨(L.getD e.2.2 1 * g) * z * (L.getD e.2.2 1 * g)⁻¹,
        ⟨L.getD e.2.2 1 * g, H.mul_mem hLk hgH, rfl⟩, ?_⟩
      have h1 : (L.getD e.2.2 1 * g) * z * (L.getD e.2.2 1 * g)⁻¹ =
          L.getD e.2.2 1 * (g * z * g⁻¹) * L.getD ((e.2.2 + 3) % 6) 1 := by
        rw [hLk', mul_inv_rev]
        group
      rw [h1, pk_mul, pk_mul, hx, pk_getD, pk_getD]
      exact (Nat.eq_of_beq_eq_true hbeq).symm
    have ih' := ih (e.1 :: pre) hrest (by
      intro c' hc'
      rcases List.mem_cons.1 hc' with rfl | hc'
      · exact hnew
      · exact hpre c' hc')
    refine ih' c ?_
    simp only [List.map_cons, List.cons_append, List.mem_cons, List.mem_append] at hc ⊢
    tauto

attribute [irreducible] chainR chainC wP wK

end CFSG.Quasithin.ModE
