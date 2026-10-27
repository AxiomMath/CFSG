module

public import CFSG.Timmesfeld.Transvection.PresSURel

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.Transvection.Pres
open scoped commutatorElement

namespace RelBuild

variable {r : ℕ}

@[expose] def flip (k : Fin r) (a : Fin r ⊕ Fin r) : Fin r ⊕ Fin r :=
  if idx a = k then Sum.swap a else a

theorem flip_of_idx_eq {k : Fin r} {a : Fin r ⊕ Fin r} (h : idx a = k) :
    flip k a = Sum.swap a :=
  ite_eq_left h

theorem flip_of_idx_ne {k : Fin r} {a : Fin r ⊕ Fin r} (h : idx a ≠ k) : flip k a = a :=
  ite_eq_right h

@[simp] theorem idx_flip (k : Fin r) (a : Fin r ⊕ Fin r) : idx (flip k a) = idx a := by
  by_cases h : idx a = k
  · rw [flip_of_idx_eq h, idx_swap]
  · rw [flip_of_idx_ne h]

@[simp] theorem flip_swap (k : Fin r) (a : Fin r ⊕ Fin r) :
    flip k (Sum.swap a) = Sum.swap (flip k a) := by
  by_cases h : idx a = k
  · rw [flip_of_idx_eq (by rwa [idx_swap]), flip_of_idx_eq h]
  · rw [flip_of_idx_ne (by rwa [idx_swap]), flip_of_idx_ne h]

@[simp] theorem flip_flip (k : Fin r) (a : Fin r ⊕ Fin r) : flip k (flip k a) = a := by
  by_cases h : idx a = k
  · rw [flip_of_idx_eq h, flip_of_idx_eq (by rwa [idx_swap]), Sum.swap_swap]
  · rw [flip_of_idx_ne h, flip_of_idx_ne h]

@[simp] theorem flip_inl_self (k : Fin r) : flip k (Sum.inl k) = Sum.inr k :=
  flip_of_idx_eq rfl

@[simp] theorem flip_inr_self (k : Fin r) : flip k (Sum.inr k) = Sum.inl k :=
  flip_of_idx_eq rfl

theorem eq_swap_of_idx_eq {a b : Fin r ⊕ Fin r} (h : idx a = idx b) (hne : b ≠ a) :
    b = Sum.swap a :=
  (eq_or_eq_swap_of_idx_eq h).resolve_left hne

theorem of_flip {α : Type*} [Fintype α] (Rel : (α → Fin r ⊕ Fin r) → Prop)
    (hRel : ∀ k Q, Rel Q → Rel (flip k ∘ Q)) {P P' : α → Fin r ⊕ Fin r}
    (hidx : ∀ x, idx (P' x) = idx (P x)) (hinj : ∀ x y, idx (P x) = idx (P y) → x = y)
    (h : Rel P) : Rel P' := by
  classical
  suffices key : ∀ S : Finset α, ∀ Q : α → Fin r ⊕ Fin r, (∀ x, x ∉ S → P' x = Q x) →
      (∀ x, idx (Q x) = idx (P x)) → Rel Q → Rel P' from
    key Finset.univ P (fun x hx => absurd (Finset.mem_univ x) hx) (fun _ => rfl) h
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro Q hQ _ hRQ
    have hPQ : P' = Q := funext fun x => hQ x (Finset.notMem_empty x)
    rwa [hPQ]
  | insert x S _ ih =>
    intro Q hQ hidxQ hRQ
    by_cases hxQ : P' x = Q x
    · refine ih Q (fun y hy => ?_) hidxQ hRQ
      by_cases hyx : y = x
      · rw [hyx]
        exact hxQ
      · exact hQ y (by simp [hyx, hy])
    · refine ih (flip (idx (Q x)) ∘ Q) (fun y hy => ?_) (fun y => ?_) (hRel _ _ hRQ)
      · by_cases hyx : y = x
        · subst hyx
          rw [Function.comp_apply, flip_of_idx_eq rfl]
          exact eq_swap_of_idx_eq (by rw [hidx, hidxQ]) hxQ
        · have hne : idx (Q y) ≠ idx (Q x) := fun h' =>
            hyx (hinj y x (by rw [← hidxQ, ← hidxQ, h']))
          rw [Function.comp_apply, flip_of_idx_ne hne]
          exact hQ y (by simp [hyx, hy])
      · rw [Function.comp_apply, idx_flip, hidxQ]

theorem conj_mul₂ {G : Type*} [Group G] (g x y : G) :
    g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) := by
  group

theorem conj_commutatorElement {G : Type*} [Group G] (g x y : G) :
    g * ⁅x, y⁆ * g⁻¹ = ⁅g * x * g⁻¹, g * y * g⁻¹⁆ := by
  simp only [commutatorElement_def]
  group

theorem conj_one {G : Type*} [Group G] (g : G) : g * 1 * g⁻¹ = 1 := by
  group

variable {F : Type*} [Field F] {σ : F ≃+* F}

theorem fixed_norm_mul (hσ : ∀ c, σ (σ c) = c) (s : F) {t : F} (ht : σ t = t) :
    σ (σ s * s * t) = σ s * s * t := by
  rw [map_mul, map_mul, hσ, ht, mul_comm s (σ s)]

theorem fixed_trace (hσ : ∀ c, σ (σ c) = c) (s t : F) :
    σ (s * σ t + σ s * t) = s * σ t + σ s * t := by
  rw [map_add, map_mul, map_mul, hσ, hσ]
  ring

end RelBuild

structure PreRelations (r : ℕ) {F : Type*} [Field F] (σ : F ≃+* F) (G : Type*) [Group G] where
  ξ : Fin r ⊕ Fin r → Fin r ⊕ Fin r → F → G
  ξL : Fin r ⊕ Fin r → F → G
  w : Fin r → G
  swap : ∀ a b, idx a ≠ idx b → ∀ c, ξ b a c = ξ a b (σ c)
  add : ∀ a b, idx a ≠ idx b → ∀ s t, ξ a b (s + t) = ξ a b s * ξ a b t
  addL : ∀ a s t, σ s = s → σ t = t → ξL a (s + t) = ξL a s * ξL a t
  weyl : ∀ k a b, idx a ≠ idx b → ∀ c,
    w k * ξ a b c * (w k)⁻¹ = ξ (RelBuild.flip k a) (RelBuild.flip k b) c
  weylL : ∀ k a c, σ c = c → w k * ξL a c * (w k)⁻¹ = ξL (RelBuild.flip k a) c
  shortLong : ∀ i j : Fin r, i ≠ j → ∀ s t, σ t = t →
    ⁅ξ (.inl j) (.inr i) s, ξL (.inl i) t⁆ =
      ξ (.inl j) (.inl i) (s * t) * ξL (.inl j) (σ s * s * t)
  trace : ∀ i j : Fin r, i ≠ j → ∀ s t,
    ⁅ξ (.inl j) (.inr i) s, ξ (.inl j) (.inl i) t⁆ = ξL (.inl j) (s * σ t + σ s * t)
  commLL : ∀ i j : Fin r, i ≠ j → ∀ s t, σ s = s → σ t = t →
    ⁅ξL (.inl i) s, ξL (.inl j) t⁆ = 1
  commLS : ∀ i j : Fin r, i ≠ j → ∀ s t, σ s = s → ⁅ξL (.inl j) s, ξ (.inl j) (.inr i) t⁆ = 1
  commLS₃ : ∀ i j k : Fin r, i ≠ j → i ≠ k → j ≠ k → ∀ s t, σ s = s →
    ⁅ξL (.inl k) s, ξ (.inl j) (.inr i) t⁆ = 1
  commSS₃ : ∀ i j k : Fin r, i ≠ j → i ≠ k → j ≠ k → ∀ s t,
    ⁅ξ (.inl j) (.inr i) s, ξ (.inl k) (.inr i) t⁆ = 1
  commSS₄ : ∀ i j k l : Fin r, i ≠ j → k ≠ l → i ≠ k → i ≠ l → j ≠ k → j ≠ l → ∀ s t,
    ⁅ξ (.inl j) (.inr i) s, ξ (.inl l) (.inr k) t⁆ = 1

namespace PreRelations

variable {r : ℕ} {F : Type*} [Field F] {σ : F ≃+* F} {G : Type*} [Group G]
  (P : PreRelations r σ G)

theorem map_zero {a b : Fin r ⊕ Fin r} (hab : idx a ≠ idx b) : P.ξ a b 0 = 1 := by
  have h := P.add a b hab 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem mapL_zero (a : Fin r ⊕ Fin r) : P.ξL a 0 = 1 := by
  have h := P.addL a 0 0 (_root_.map_zero σ) (_root_.map_zero σ)
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem commSS_self {a b : Fin r ⊕ Fin r} (hab : idx a ≠ idx b) (s t : F) :
    ⁅P.ξ a b s, P.ξ a b t⁆ = 1 := by
  rw [commutatorElement_eq_one_iff_mul_comm, ← P.add a b hab, ← P.add a b hab, add_comm]

theorem shortLong' (hσ : ∀ c, σ (σ c) = c) {a b : Fin r ⊕ Fin r} (hab : idx a ≠ idx b)
    (s t : F) (ht : σ t = t) :
    ⁅P.ξ a b s, P.ξL (Sum.swap b) t⁆ = P.ξ a (Sum.swap b) (s * t) * P.ξL a (σ s * s * t) := by
  have key := RelBuild.of_flip (fun Q : Fin 2 → Fin r ⊕ Fin r => idx (Q 0) ≠ idx (Q 1) →
      ∀ s t, σ t = t → ⁅P.ξ (Q 0) (Q 1) s, P.ξL (Sum.swap (Q 1)) t⁆ =
        P.ξ (Q 0) (Sum.swap (Q 1)) (s * t) * P.ξL (Q 0) (σ s * s * t))
    (fun k Q hQ hne s t ht => by
      simp only [Function.comp_apply, RelBuild.idx_flip] at hne ⊢
      have h := congrArg (fun g => P.w k * g * (P.w k)⁻¹) (hQ hne s t ht)
      simp only [RelBuild.conj_commutatorElement, RelBuild.conj_mul₂] at h
      rwa [P.weyl k _ _ hne, P.weylL k _ _ ht, P.weyl k _ _ (by rwa [idx_swap]),
        P.weylL k _ _ (RelBuild.fixed_norm_mul hσ s ht), RelBuild.flip_swap] at h)
    (P := ![Sum.inl (idx a), Sum.inr (idx b)]) (P' := ![a, b])
    (fun x => by fin_cases x <;> simp) (fun x y hxy => by fin_cases x <;> fin_cases y <;> simp_all)
    (fun _ s t ht => by simpa using P.shortLong (idx b) (idx a) (Ne.symm hab) s t ht)
  simpa using key hab s t ht

theorem trace' (hσ : ∀ c, σ (σ c) = c) {a b : Fin r ⊕ Fin r} (hab : idx a ≠ idx b) (s t : F) :
    ⁅P.ξ a b s, P.ξ a (Sum.swap b) t⁆ = P.ξL a (s * σ t + σ s * t) := by
  have key := RelBuild.of_flip (fun Q : Fin 2 → Fin r ⊕ Fin r => idx (Q 0) ≠ idx (Q 1) →
      ∀ s t, ⁅P.ξ (Q 0) (Q 1) s, P.ξ (Q 0) (Sum.swap (Q 1)) t⁆ = P.ξL (Q 0) (s * σ t + σ s * t))
    (fun k Q hQ hne s t => by
      simp only [Function.comp_apply, RelBuild.idx_flip] at hne ⊢
      have h := congrArg (fun g => P.w k * g * (P.w k)⁻¹) (hQ hne s t)
      simp only [RelBuild.conj_commutatorElement] at h
      rwa [P.weyl k _ _ hne, P.weyl k _ _ (by rwa [idx_swap]),
        P.weylL k _ _ (RelBuild.fixed_trace hσ s t), RelBuild.flip_swap] at h)
    (P := ![Sum.inl (idx a), Sum.inr (idx b)]) (P' := ![a, b])
    (fun x => by fin_cases x <;> simp) (fun x y hxy => by fin_cases x <;> fin_cases y <;> simp_all)
    (fun _ s t => by simpa using P.trace (idx b) (idx a) (Ne.symm hab) s t)
  simpa using key hab s t

theorem commLL' {a c : Fin r ⊕ Fin r} (hac : c ≠ Sum.swap a) {s t : F} (hs : σ s = s)
    (ht : σ t = t) : ⁅P.ξL a s, P.ξL c t⁆ = 1 := by
  by_cases hca : c = a
  · subst hca
    rw [commutatorElement_eq_one_iff_mul_comm, ← P.addL _ s t hs ht, ← P.addL _ t s ht hs,
      add_comm]
  have hidx : idx a ≠ idx c := idx_ne_of_ne hca hac
  have key := RelBuild.of_flip (fun Q : Fin 2 → Fin r ⊕ Fin r => idx (Q 0) ≠ idx (Q 1) →
      ∀ s t, σ s = s → σ t = t → ⁅P.ξL (Q 0) s, P.ξL (Q 1) t⁆ = 1)
    (fun k Q hQ hne s t hs ht => by
      simp only [Function.comp_apply, RelBuild.idx_flip] at hne ⊢
      have h := congrArg (fun g => P.w k * g * (P.w k)⁻¹) (hQ hne s t hs ht)
      simp only [RelBuild.conj_commutatorElement, RelBuild.conj_one] at h
      rwa [P.weylL k _ _ hs, P.weylL k _ _ ht] at h)
    (P := ![Sum.inl (idx a), Sum.inl (idx c)]) (P' := ![a, c])
    (fun x => by fin_cases x <;> simp) (fun x y hxy => by fin_cases x <;> fin_cases y <;> simp_all)
    (fun _ s t hs ht => by simpa using P.commLL (idx a) (idx c) hidx s t hs ht)
  simpa using key hidx s t hs ht

theorem commLS_self {a d : Fin r ⊕ Fin r} (had : idx a ≠ idx d) {s : F} (hs : σ s = s) (t : F) :
    ⁅P.ξL a s, P.ξ a d t⁆ = 1 := by
  have key := RelBuild.of_flip (fun Q : Fin 2 → Fin r ⊕ Fin r => idx (Q 0) ≠ idx (Q 1) →
      ∀ s t, σ s = s → ⁅P.ξL (Q 0) s, P.ξ (Q 0) (Q 1) t⁆ = 1)
    (fun k Q hQ hne s t hs => by
      simp only [Function.comp_apply, RelBuild.idx_flip] at hne ⊢
      have h := congrArg (fun g => P.w k * g * (P.w k)⁻¹) (hQ hne s t hs)
      simp only [RelBuild.conj_commutatorElement, RelBuild.conj_one] at h
      rwa [P.weylL k _ _ hs, P.weyl k _ _ hne] at h)
    (P := ![Sum.inl (idx a), Sum.inr (idx d)]) (P' := ![a, d])
    (fun x => by fin_cases x <;> simp) (fun x y hxy => by fin_cases x <;> fin_cases y <;> simp_all)
    (fun _ s t hs => by simpa using P.commLS (idx d) (idx a) (Ne.symm had) s t hs)
  simpa using key had s t hs

theorem commLS_cross {a c d : Fin r ⊕ Fin r} (hcd : idx c ≠ idx d) (hac : idx a ≠ idx c)
    (had : idx a ≠ idx d) {s : F} (hs : σ s = s) (t : F) : ⁅P.ξL a s, P.ξ c d t⁆ = 1 := by
  have key := RelBuild.of_flip (fun Q : Fin 3 → Fin r ⊕ Fin r => idx (Q 1) ≠ idx (Q 2) →
      idx (Q 0) ≠ idx (Q 1) → idx (Q 0) ≠ idx (Q 2) →
      ∀ s t, σ s = s → ⁅P.ξL (Q 0) s, P.ξ (Q 1) (Q 2) t⁆ = 1)
    (fun k Q hQ hne h1 h2 s t hs => by
      simp only [Function.comp_apply, RelBuild.idx_flip] at hne h1 h2 ⊢
      have h := congrArg (fun g => P.w k * g * (P.w k)⁻¹) (hQ hne h1 h2 s t hs)
      simp only [RelBuild.conj_commutatorElement, RelBuild.conj_one] at h
      rwa [P.weylL k _ _ hs, P.weyl k _ _ hne] at h)
    (P := ![Sum.inl (idx a), Sum.inl (idx c), Sum.inr (idx d)]) (P' := ![a, c, d])
    (fun x => by fin_cases x <;> simp) (fun x y hxy => by fin_cases x <;> fin_cases y <;> simp_all)
    (fun _ _ _ s t hs => by
      simpa using P.commLS₃ (idx d) (idx c) (idx a) (Ne.symm hcd) (Ne.symm had) (Ne.symm hac)
        s t hs)
  simpa using key hcd hac had s t hs

theorem commLS' {a c d : Fin r ⊕ Fin r} (hcd : idx c ≠ idx d) (hca : c ≠ Sum.swap a)
    (hda : d ≠ Sum.swap a) {s : F} (hs : σ s = s) (t : F) : ⁅P.ξL a s, P.ξ c d t⁆ = 1 := by
  by_cases hac : idx a = idx c
  · obtain rfl : c = a := (eq_or_eq_swap_of_idx_eq hac).resolve_right hca
    exact P.commLS_self hcd hs t
  by_cases had : idx a = idx d
  · obtain rfl : d = a := (eq_or_eq_swap_of_idx_eq had).resolve_right hda
    rw [P.swap d c (Ne.symm hcd)]
    exact P.commLS_self (Ne.symm hcd) hs _
  exact P.commLS_cross hcd hac had hs t

theorem commSS_shared {a b d : Fin r ⊕ Fin r} (hab : idx a ≠ idx b) (hdb : idx d ≠ idx b)
    (had : idx a ≠ idx d) (s t : F) : ⁅P.ξ a b s, P.ξ d b t⁆ = 1 := by
  have key := RelBuild.of_flip (fun Q : Fin 3 → Fin r ⊕ Fin r => idx (Q 0) ≠ idx (Q 1) →
      idx (Q 2) ≠ idx (Q 1) → ∀ s t, ⁅P.ξ (Q 0) (Q 1) s, P.ξ (Q 2) (Q 1) t⁆ = 1)
    (fun k Q hQ h1 h2 s t => by
      simp only [Function.comp_apply, RelBuild.idx_flip] at h1 h2 ⊢
      have h := congrArg (fun g => P.w k * g * (P.w k)⁻¹) (hQ h1 h2 s t)
      simp only [RelBuild.conj_commutatorElement, RelBuild.conj_one] at h
      rwa [P.weyl k _ _ h1, P.weyl k _ _ h2] at h)
    (P := ![Sum.inl (idx a), Sum.inr (idx b), Sum.inl (idx d)]) (P' := ![a, b, d])
    (fun x => by fin_cases x <;> simp) (fun x y hxy => by fin_cases x <;> fin_cases y <;> simp_all)
    (fun _ _ s t => by
      simpa using P.commSS₃ (idx b) (idx a) (idx d) (Ne.symm hab) (Ne.symm hdb) had s t)
  simpa using key hab hdb s t

theorem commSS_disj {a b c d : Fin r ⊕ Fin r} (hab : idx a ≠ idx b) (hcd : idx c ≠ idx d)
    (hac : idx a ≠ idx c) (had : idx a ≠ idx d) (hbc : idx b ≠ idx c) (hbd : idx b ≠ idx d)
    (s t : F) : ⁅P.ξ a b s, P.ξ c d t⁆ = 1 := by
  have key := RelBuild.of_flip (fun Q : Fin 4 → Fin r ⊕ Fin r => idx (Q 0) ≠ idx (Q 1) →
      idx (Q 2) ≠ idx (Q 3) → ∀ s t, ⁅P.ξ (Q 0) (Q 1) s, P.ξ (Q 2) (Q 3) t⁆ = 1)
    (fun k Q hQ h1 h2 s t => by
      simp only [Function.comp_apply, RelBuild.idx_flip] at h1 h2 ⊢
      have h := congrArg (fun g => P.w k * g * (P.w k)⁻¹) (hQ h1 h2 s t)
      simp only [RelBuild.conj_commutatorElement, RelBuild.conj_one] at h
      rwa [P.weyl k _ _ h1, P.weyl k _ _ h2] at h)
    (P := ![Sum.inl (idx a), Sum.inr (idx b), Sum.inl (idx c), Sum.inr (idx d)])
    (P' := ![a, b, c, d])
    (fun x => by fin_cases x <;> simp) (fun x y hxy => by fin_cases x <;> fin_cases y <;> simp_all)
    (fun _ _ s t => by
      simpa using P.commSS₄ (idx b) (idx a) (idx d) (idx c) (Ne.symm hab) (Ne.symm hcd) hbd hbc
        had hac s t)
  simpa using key hab hcd s t

theorem commSS' {a b c d : Fin r ⊕ Fin r} (hab : idx a ≠ idx b) (hcd : idx c ≠ idx d)
    (hca : c ≠ Sum.swap a) (hcb : c ≠ Sum.swap b) (hda : d ≠ Sum.swap a) (hdb : d ≠ Sum.swap b)
    (s t : F) : ⁅P.ξ a b s, P.ξ c d t⁆ = 1 := by
  by_cases h1 : idx c = idx a
  · obtain rfl : c = a := (eq_or_eq_swap_of_idx_eq h1.symm).resolve_right hca
    by_cases h2 : idx d = idx b
    · obtain rfl : d = b := (eq_or_eq_swap_of_idx_eq h2.symm).resolve_right hdb
      exact P.commSS_self hab s t
    rw [P.swap b c (Ne.symm hab), P.swap d c (Ne.symm hcd)]
    exact P.commSS_shared (Ne.symm hab) (Ne.symm hcd) (fun h => h2 h.symm) _ _
  by_cases h1' : idx c = idx b
  · obtain rfl : c = b := (eq_or_eq_swap_of_idx_eq h1'.symm).resolve_right hcb
    by_cases h2 : idx d = idx a
    · obtain rfl : d = a := (eq_or_eq_swap_of_idx_eq h2.symm).resolve_right hda
      rw [P.swap d c hab]
      exact P.commSS_self hab s _
    rw [P.swap d c (Ne.symm hcd)]
    exact P.commSS_shared hab (Ne.symm hcd) (fun h => h2 h.symm) _ _
  by_cases h3 : idx d = idx a
  · obtain rfl : d = a := (eq_or_eq_swap_of_idx_eq h3.symm).resolve_right hda
    rw [P.swap b d (Ne.symm hab)]
    exact P.commSS_shared (Ne.symm hab) hcd (fun h => h1' h.symm) _ _
  by_cases h4 : idx d = idx b
  · obtain rfl : d = b := (eq_or_eq_swap_of_idx_eq h4.symm).resolve_right hdb
    exact P.commSS_shared hab hcd (fun h => h1 h.symm) s t
  exact P.commSS_disj hab hcd (fun h => h1 h.symm) (fun h => h3 h.symm) (fun h => h1' h.symm)
    (fun h => h4 h.symm) s t

theorem short_of_base {i j k : Fin r} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (h : ∀ s t, ⁅P.ξ (.inl j) (.inr i) s, P.ξ (.inl k) (.inr j) t⁆ = P.ξ (.inl k) (.inr i) (s * t))
    {a b d : Fin r ⊕ Fin r} (ha : idx a = i) (hb : idx b = j) (hd : idx d = k) (s t : F) :
    ⁅P.ξ a b s, P.ξ (Sum.swap b) d t⁆ = P.ξ a d (s * t) := by
  have key := RelBuild.of_flip (fun Q : Fin 3 → Fin r ⊕ Fin r => idx (Q 0) ≠ idx (Q 1) →
      idx (Q 1) ≠ idx (Q 2) → idx (Q 0) ≠ idx (Q 2) →
      ∀ s t, ⁅P.ξ (Q 0) (Q 1) s, P.ξ (Sum.swap (Q 1)) (Q 2) t⁆ = P.ξ (Q 0) (Q 2) (s * t))
    (fun k Q hQ h1 h2 h3 s t => by
      simp only [Function.comp_apply, RelBuild.idx_flip] at h1 h2 h3 ⊢
      have h := congrArg (fun g => P.w k * g * (P.w k)⁻¹) (hQ h1 h2 h3 s t)
      simp only [RelBuild.conj_commutatorElement] at h
      rwa [P.weyl k _ _ h1, P.weyl k _ _ (by rwa [idx_swap]), P.weyl k _ _ h3,
        RelBuild.flip_swap] at h)
    (P := ![Sum.inr i, Sum.inl j, Sum.inl k]) (P' := ![a, b, d])
    (fun x => by fin_cases x <;> simp [ha, hb, hd])
    (fun x y hxy => by fin_cases x <;> fin_cases y <;> simp_all)
    (fun _ _ _ s t => by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, Sum.swap_inl]
      rw [P.swap (.inl j) (.inr i) (by simpa using hij.symm),
        P.swap (.inl k) (.inr j) (by simpa using hjk.symm), h,
        P.swap (.inl k) (.inr i) (by simpa using hik.symm), map_mul])
  simpa using key (by simpa [ha, hb] using hij) (by simpa [hb, hd] using hjk)
    (by simpa [ha, hd] using hik) s t

@[expose] def toSURelations (hσ : ∀ c, σ (σ c) = c)
    (hA : ∀ i j k : Fin r, i ≠ j → j ≠ k → i ≠ k → ∀ s t,
      ⁅P.ξ (.inl j) (.inr i) s, P.ξ (.inl k) (.inr j) t⁆ = P.ξ (.inl k) (.inr i) (s * t)) :
    SURelations r σ G where
  ξ := P.ξ
  ξL := P.ξL
  swap := P.swap
  add := P.add
  addL := P.addL
  short _ _ _ hab hbd had s t :=
    P.short_of_base hab hbd had (hA _ _ _ hab hbd had) rfl rfl rfl s t
  shortLong _ _ hab s t ht := P.shortLong' hσ hab s t ht
  trace _ _ hab s t := P.trace' hσ hab s t
  commLL _ _ hac _ _ hs ht := P.commLL' hac hs ht
  commLS _ _ _ hcd hca hda _ t hs := P.commLS' hcd hca hda hs t
  commSS _ _ _ _ hab hcd hca hcb hda hdb s t := P.commSS' hab hcd hca hcb hda hdb s t

@[simp] theorem toSURelations_ξ (hσ : ∀ c, σ (σ c) = c) (hA) :
    (P.toSURelations hσ hA).ξ = P.ξ := rfl

@[simp] theorem toSURelations_ξL (hσ : ∀ c, σ (σ c) = c) (hA) :
    (P.toSURelations hσ hA).ξL = P.ξL := rfl

end PreRelations

end CFSG.Timmesfeld.Transvection
