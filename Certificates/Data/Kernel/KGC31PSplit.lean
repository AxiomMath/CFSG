module

public import Certificates.Data.Kernel.KGC31PB

public section

namespace CFSG.KC.KGC31P

open CFSG.KC.Enum CFSG.KS

variable (n w : Nat)

@[expose] noncomputable def pallProducts (f : Nat → Bool) : List (List Nat) → Nat → Bool
  | [], g => f g
  | T :: Ts, g => T.all fun t => pallProducts f Ts (pc n w g t)

theorem pfilter_all (f P : Nat → Bool) : ∀ (Ls : List (List Nat)) (g : Nat) (acc : List Nat),
    (pfilterProducts n w f Ls g acc).all P =
      (acc.all P && pallProducts n w (fun x => !f x || P x) Ls g)
  | [], g, acc => by
    unfold pfilterProducts pallProducts
    cases hf : f g
    · simp
    · simp [List.all_cons, Bool.and_comm]
  | T :: Ts, g, acc => by
    unfold pfilterProducts pallProducts
    induction T generalizing acc with
    | nil => simp
    | cons t T ih =>
      rw [List.foldl_cons, ih, pfilter_all f P Ts, List.all_cons, Bool.and_assoc]

theorem foldl_add_shift (h : Nat → Nat) : ∀ (T : List Nat) (c k : Nat),
    T.foldl (fun c t => c + h t) (c + k) = T.foldl (fun c t => c + h t) c + k
  | [], _, _ => rfl
  | t :: T, c, k => by
    rw [List.foldl_cons, List.foldl_cons, show c + k + h t = (c + h t) + k by omega,
      foldl_add_shift h T]

theorem pfilter_countP (f P : Nat → Bool) : ∀ (Ls : List (List Nat)) (g : Nat) (acc : List Nat),
    (pfilterProducts n w f Ls g acc).countP P =
      acc.countP P + pcountProducts n w (fun x => f x && P x) Ls g
  | [], g, acc => by
    unfold pfilterProducts pcountProducts
    cases hf : f g <;> cases hp : P g <;> simp [List.countP_cons, hp]
  | T :: Ts, g, acc => by
    unfold pfilterProducts pcountProducts
    suffices ∀ (T : List Nat) (acc : List Nat) (c : Nat),
        (T.foldl (fun acc t => pfilterProducts n w f Ts (pc n w g t) acc) acc).countP P + c =
          acc.countP P + T.foldl (fun c t =>
            c + pcountProducts n w (fun x => f x && P x) Ts (pc n w g t)) c by
      simpa using this T acc 0
    intro T
    induction T with
    | nil => intro acc c; rfl
    | cons t T ih =>
      intro acc c
      rw [List.foldl_cons, List.foldl_cons, ih, pfilter_countP f P Ts, foldl_add_shift]
      omega

theorem getD_lt {l : List Nat} {i : Nat} (d : Nat) (h : i < l.length) : l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

theorem getD_app_left {l l' : List Nat} {i : Nat} (d : Nat) (h : i < l.length) :
    (l ++ l').getD i d = l.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_right {l l' : List Nat} {i : Nat} (d : Nat) (h : l.length ≤ i) :
    (l ++ l').getD i d = l'.getD (i - l.length) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem all_eq_range (T : List Nat) (h : Nat → Bool) :
    T.all h = (List.range T.length).all fun i => h (T.getD i 0) := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  constructor
  · intro H i hi
    rw [List.mem_range] at hi
    rw [getD_lt _ hi]
    exact H _ (List.getElem_mem hi)
  · intro H x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have := H i (List.mem_range.2 hi)
    rwa [getD_lt _ hi] at this

theorem eq_headD_cons {l : List (List Nat)} (h : (!l.isEmpty) = true) : l = l.headD [] :: l.tail := by
  cases l with
  | nil => exact absurd h (by decide)
  | cons a l => rfl

theorem ne_nil_of_isEmpty {l : List (List Nat)} (h : (!l.isEmpty) = true) : l ≠ [] := by
  intro e
  rw [e] at h
  exact absurd h (by decide)

theorem pall_of_pieces {f : Nat → Bool} {T : List Nat} {Ts : List (List Nat)} {g : Nat}
    (h : ∀ i < T.length, pallProducts n w f Ts (pc n w g (T.getD i 0)) = true) :
    pallProducts n w f (T :: Ts) g = true := by
  unfold pallProducts
  rw [all_eq_range, List.all_eq_true]
  intro i hi
  exact h i (List.mem_range.1 hi)

theorem pall_mono {f f' : Nat → Bool} (hf : ∀ x, f x = true → f' x = true) :
    ∀ (Ls : List (List Nat)) (g : Nat), pallProducts n w f Ls g = true →
      pallProducts n w f' Ls g = true
  | [], g, h => by
    unfold pallProducts at h ⊢
    exact hf g h
  | T :: Ts, g, h => by
    unfold pallProducts at h ⊢
    rw [List.all_eq_true] at h ⊢
    exact fun t ht => pall_mono hf Ts _ (h t ht)

theorem pcount_eq_sum (f : Nat → Bool) (T : List Nat) (Ts : List (List Nat)) (g : Nat) :
    pcountProducts n w f (T :: Ts) g =
      ((List.range T.length).map fun i => pcountProducts n w f Ts (pc n w g (T.getD i 0))).sum := by
  rw [pcountProducts.eq_2]
  have hfold : ∀ (T : List Nat) (c : Nat),
      T.foldl (fun c t => c + pcountProducts n w f Ts (pc n w g t)) c =
        c + (T.map fun t => pcountProducts n w f Ts (pc n w g t)).sum := by
    intro T
    induction T with
    | nil => intro c; simp
    | cons t T ih => intro c; rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]; omega
  rw [hfold, Nat.zero_add]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [getD_lt _ (by simpa using h1)]

theorem sum_range_eq {F : Nat → Nat} {cs : List Nat} :
    ∀ {N : Nat}, cs.length = N → (∀ i < N, Nat.beq (F i) (cs.getD i 0) = true) →
      ((List.range N).map F).sum = cs.sum := by
  intro N
  induction N generalizing cs with
  | zero => intro h _; rw [List.length_eq_zero_iff.1 h]; rfl
  | succ N ih =>
    intro hl h
    obtain ⟨cs', c, rfl⟩ : ∃ cs' c, cs = cs' ++ [c] := by
      refine ⟨cs.dropLast, cs.getLast (by intro e; rw [e] at hl; simp at hl), ?_⟩
      exact (List.dropLast_concat_getLast _).symm
    have hl' : cs'.length = N := by simp at hl; omega
    rw [List.range_succ, List.map_append, List.sum_append, List.sum_append,
      ih hl' fun i hi => by
        have := h i (by omega)
        rwa [getD_app_left _ (by omega)] at this]
    have hN := Nat.eq_of_beq_eq_true (h N (by omega))
    rw [getD_app_right _ (by omega), hl', Nat.sub_self] at hN
    simp [hN]

theorem pcount_of_pieces {f : Nat → Bool} {T : List Nat} {Ts : List (List Nat)} {g : Nat}
    {cs : List Nat} (hl : cs.length = T.length)
    (h : ∀ i < T.length, Nat.beq (pcountProducts n w f Ts (pc n w g (T.getD i 0))) (cs.getD i 0) =
      true) :
    pcountProducts n w f (T :: Ts) g = cs.sum := by
  rw [pcount_eq_sum]
  exact sum_range_eq hl h

@[expose] noncomputable def pgL (g t y : Nat) : Nat :=
  bif Nat.blt y n then pg w (mask w) g (pg w (mask w) t y) else pg w (mask w) (pc n w g t) y

@[expose] noncomputable def pgL2 (a g t y : Nat) : Nat :=
  bif Nat.blt y n then pg w (mask w) a (pgL n w g t y) else pg w (mask w) (pc n w a (pc n w g t)) y

@[expose] noncomputable def pcommL (gs : List Nat) (g t : Nat) : Bool :=
  gs.all fun h => allN n fun i =>
    Nat.beq (pgL n w g t (pg w (mask w) h i)) (pg w (mask w) h (pgL n w g t i))

@[expose] noncomputable def pcountL (fL : Nat → Nat → Bool) : List (List Nat) → Nat → Nat
  | [], _ => 0
  | [T], g => T.foldl (fun c t => c + bif fL g t then 1 else 0) 0
  | T :: Ts, g => T.foldl (fun c t => c + pcountL fL Ts (pc n w g t)) 0

@[expose] noncomputable def pallL (fL : Nat → Nat → Bool) : List (List Nat) → Nat → Bool
  | [], _ => true
  | [T], g => T.all fun t => fL g t
  | T :: Ts, g => T.all fun t => pallL fL Ts (pc n w g t)

theorem pcountL_eq {f : Nat → Bool} {fL : Nat → Nat → Bool} (hf : ∀ g t, fL g t = f (pc n w g t)) :
    ∀ (Ls : List (List Nat)) (g : Nat), Ls ≠ [] → pcountL n w fL Ls g = pcountProducts n w f Ls g
  | [], _, h => absurd rfl h
  | [T], g, _ => by
    unfold pcountL pcountProducts
    congr 1
    funext c t
    unfold pcountProducts
    rw [hf]
    cases f (pc n w g t) <;> rfl
  | T :: T' :: Ts, g, _ => by
    unfold pcountL
    rw [pcountProducts]
    congr 1
    funext c t
    rw [pcountL_eq hf (T' :: Ts) _ (List.cons_ne_nil _ _)]

theorem pallL_eq {f : Nat → Bool} {fL : Nat → Nat → Bool} (hf : ∀ g t, fL g t = f (pc n w g t)) :
    ∀ (Ls : List (List Nat)) (g : Nat), Ls ≠ [] → pallL n w fL Ls g = pallProducts n w f Ls g
  | [], _, h => absurd rfl h
  | [T], g, _ => by
    unfold pallL pallProducts
    congr 1
    funext t
    unfold pallProducts
    rw [hf]
  | T :: T' :: Ts, g, _ => by
    unfold pallL
    rw [pallProducts]
    congr 1
    funext t
    rw [pallL_eq hf (T' :: Ts) _ (List.cons_ne_nil _ _)]

end CFSG.KC.KGC31P

end
