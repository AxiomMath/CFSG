module

public import CFSG.Certificates.PresentationLetters
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star

public section

namespace CFSG.Sporadic.Bridge.J2

open CFSG.Certificates.CosetEnumeration

@[expose] def decodeW (v : ℕ) : ℤ := if v % 2 = 0 then ((v / 2 : ℕ) : ℤ) else -((v / 2 : ℕ) : ℤ)

@[expose] def posRef (refs : ℕ → ℕ) (f t o q : ℕ) : ℕ :=
  cond (Nat.beq q t) (Nat.mul 2 f) (refs (Nat.add o q))

@[expose] def wsumOK (wt refs : ℕ → ℕ) (f t o tgt : ℕ) : ℕ → List ℕ → ℕ → ℕ → Bool
  | _, [], p, n => Nat.beq p (Nat.add n tgt)
  | q, _ :: w, p, n =>
    cond (Nat.beq (Nat.mod (Nat.add (wt (Nat.div (posRef refs f t o q) 2))
        (posRef refs f t o q)) 2) 0)
      (wsumOK wt refs f t o tgt (Nat.succ q) w
        (Nat.add p (Nat.div (wt (Nat.div (posRef refs f t o q) 2)) 2)) n)
      (wsumOK wt refs f t o tgt (Nat.succ q) w p
        (Nat.add n (Nat.div (wt (Nat.div (posRef refs f t o q) 2)) 2)))

@[expose] def weightOK (wt kind wi ft fo refs tgt : ℕ → ℕ) (rels subs : List (List ℕ))
    (f : ℕ) : Bool :=
  match kind f with
  | 0 => Nat.beq (wt f) 0
  | 2 => wsumOK wt refs f (ft f) (fo f) 0 0 (wordAt rels (wi f)) 0 0
  | 3 => wsumOK wt refs f (ft f) (fo f) (tgt (wi f)) 0 (wordAt subs (wi f)) 0 0
  | _ => true

@[expose] def weightsOK (wt kind wi ft fo refs tgt : ℕ → ℕ) (rels subs : List (List ℕ)) :
    ℕ → ℕ → Bool
  | _, 0 => true
  | lo, n + 1 => and (weightOK wt kind wi ft fo refs tgt rels subs lo)
      (weightsOK wt kind wi ft fo refs tgt rels subs (Nat.succ lo) n)

theorem weightsOK_add (wt kind wi ft fo refs tgt : ℕ → ℕ) (rels subs : List (List ℕ))
    (lo n m : ℕ) :
    weightsOK wt kind wi ft fo refs tgt rels subs lo (n + m) =
      (weightsOK wt kind wi ft fo refs tgt rels subs lo n &&
        weightsOK wt kind wi ft fo refs tgt rels subs (lo + n) m) := by
  induction n generalizing lo with
  | zero => simp [weightsOK]
  | succ n ih =>
    rw [Nat.succ_add, weightsOK, weightsOK, ih, Nat.succ_eq_add_one, Nat.add_right_comm,
      Bool.and_assoc]
    rfl

theorem weightOK_of_weightsOK {wt kind wi ft fo refs tgt : ℕ → ℕ} {rels subs : List (List ℕ)}
    {lo n : ℕ} (h : weightsOK wt kind wi ft fo refs tgt rels subs lo n = true) :
    ∀ f, lo ≤ f → f < lo + n → weightOK wt kind wi ft fo refs tgt rels subs f = true := by
  induction n generalizing lo with
  | zero => intro f h1 h2; omega
  | succ n ih =>
    rw [weightsOK, Bool.and_eq_true] at h
    intro f h1 h2
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact h.1
    · exact ih h.2 f (Nat.succ_le_of_lt hlt) (by rw [Nat.succ_add]; exact h2)

@[expose] def refW (wt : ℕ → ℕ) (r : ℕ) : ℤ :=
  if r % 2 = 0 then decodeW (wt (r / 2)) else -decodeW (wt (r / 2))

@[expose] def walkW (wt refs : ℕ → ℕ) (f t o : ℕ) : ℕ → List ℕ → ℤ
  | _, [] => 0
  | q, _ :: w => refW wt (posRef refs f t o q) + walkW wt refs f t o (q + 1) w

theorem refW_eq (wt : ℕ → ℕ) (r : ℕ) :
    refW wt r = if (wt (r / 2) + r) % 2 = 0 then ((wt (r / 2) / 2 : ℕ) : ℤ)
      else -((wt (r / 2) / 2 : ℕ) : ℤ) := by
  unfold refW decodeW
  rcases Nat.mod_two_eq_zero_or_one r with hr | hr <;>
    rcases Nat.mod_two_eq_zero_or_one (wt (r / 2)) with hv | hv <;>
    simp [hr, hv, Nat.add_mod]

private theorem nat_div_eq (x y : ℕ) : Nat.div x y = x / y := rfl

private theorem nat_mod_eq (x y : ℕ) : Nat.mod x y = x % y := rfl

private theorem beq_true {a b : ℕ} (h : a = b) : Nat.beq a b = true := by
  rw [h]; exact Nat.beq_refl b

private theorem beq_false {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hh : Nat.beq a b with
  | false => rfl
  | true => exact absurd (Nat.eq_of_beq_eq_true hh) h

theorem walkW_of_wsumOK {wt refs : ℕ → ℕ} {f t o tgt : ℕ} :
    ∀ (w : List ℕ) (q p n : ℕ), wsumOK wt refs f t o tgt q w p n = true →
      (p : ℤ) - n + walkW wt refs f t o q w = tgt := by
  intro w
  induction w with
  | nil =>
    intro q p n h
    have := Nat.eq_of_beq_eq_true h
    simp only [walkW, Nat.add_eq] at this ⊢
    omega
  | cons c w ih =>
    intro q p n h
    simp only [wsumOK, nat_div_eq, nat_mod_eq, Nat.add_eq] at h
    simp only [walkW]
    rw [refW_eq]
    generalize posRef refs f t o q = r at h ⊢
    by_cases hpar : (wt (r / 2) + r) % 2 = 0
    · rw [beq_true hpar, Bool.cond_true] at h
      have := ih (q + 1) _ n h
      rw [ite_eq_left hpar]
      simp only [Nat.cast_add] at this
      linarith
    · rw [beq_false hpar, Bool.cond_false] at h
      have := ih (q + 1) p _ h
      rw [ite_eq_right hpar]
      simp only [Nat.cast_add] at this
      linarith

section Sound

variable {G : Type*} [Group G] {A : Type*} [AddCommGroup A]

structure WeightMap (φ : A → G) : Prop where
  map_add : ∀ a b, φ (a + b) = φ a * φ b

namespace WeightMap

variable {φ : A → G}

theorem map_zero (h : WeightMap φ) : φ 0 = 1 := by
  have := h.map_add 0 0
  rw [add_zero] at this
  exact mul_eq_left.mp this.symm

theorem map_neg (h : WeightMap φ) (a : A) : φ (-a) = (φ a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← h.map_add, neg_add_cancel, h.map_zero]

theorem eq_of_mul_mul (h : WeightMap φ) {P Q T V : A} {X : G} (hX : φ T = φ P * X * φ Q)
    (hV : P + V + Q = T) : X = φ V := by
  have hx : X = (φ P)⁻¹ * φ T * (φ Q)⁻¹ := by rw [hX]; group
  rw [hx, ← h.map_neg, ← h.map_neg, ← h.map_add, ← h.map_add, ← hV]
  congr 1
  abel

end WeightMap

@[expose] def sW (W : ℕ → A) (r : ℕ) : A := if r % 2 = 0 then W (r / 2) else -W (r / 2)

@[expose] def walkA (W : ℕ → A) (refs : ℕ → ℕ) (f t o : ℕ) : ℕ → List ℕ → A
  | _, [] => 0
  | q, _ :: w => sW W (posRef refs f t o q) + walkA W refs f t o (q + 1) w

noncomputable def factV (gen : ℕ → G) (L' : ℕ) (pl fx fc fy : ℕ → ℕ) (f : ℕ) : G :=
  rep gen L' pl (fx f) * gen (fc f) * (rep gen L' pl (fy f))⁻¹

private theorem walk_cons_eq' (gen : ℕ → G) (L' : ℕ) (pl : ℕ → ℕ) (cur c y s : ℕ) (w : List ℕ) :
    rep gen L' pl cur * evalWord gen (c :: w) * (rep gen L' pl s)⁻¹ =
      (rep gen L' pl cur * gen c * (rep gen L' pl y)⁻¹) *
        (rep gen L' pl y * evalWord gen w * (rep gen L' pl s)⁻¹) := by
  rw [evalWord_cons]; group

private theorem posRef_of_ne {refs : ℕ → ℕ} {f t o q : ℕ} (h : q ≠ t) :
    posRef refs f t o q = refs (o + q) := by
  unfold posRef
  rw [beq_false h, Bool.cond_false]
  rfl

private theorem posRef_self {refs : ℕ → ℕ} {f t o : ℕ} : posRef refs f t o t = 2 * f := by
  unfold posRef
  rw [Nat.beq_refl, Bool.cond_true]
  rfl

variable {gen : ℕ → G} {L' : ℕ} {pl fx fc fy inv refs : ℕ → ℕ} {φ : A → G} {W : ℕ → A}

theorem ref_eq (hφ : WeightMap φ) {f r cur c : ℕ}
    (htrue : ∀ g < f, factV gen L' pl fx fc fy g = φ (W g)) (hc : gen (inv c) = (gen c)⁻¹)
    (h : refOK fx fc fy inv f r cur c = true) :
    rep gen L' pl cur * gen c * (rep gen L' pl (refNext fx fy r))⁻¹ = φ (sW W r) := by
  unfold refOK at h
  unfold refNext sW
  simp only [nat_div_eq, nat_mod_eq] at h ⊢
  rw [Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨hlt, h⟩ := h
  have hg := htrue _ hlt
  rcases Nat.mod_two_eq_zero_or_one r with hr | hr
  · rw [beq_true hr, Bool.cond_true, Bool.and_eq_true] at h
    rw [beq_true hr, Bool.cond_true, ite_eq_left hr]
    rw [factV, Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2] at hg
    exact hg
  · rw [beq_false (show r % 2 ≠ 0 by omega), Bool.cond_false, Bool.and_eq_true] at h
    rw [beq_false (show r % 2 ≠ 0 by omega), Bool.cond_false, ite_eq_right (by omega),
      hφ.map_neg]
    rw [factV, Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2, hc] at hg
    rw [← hg]
    group

theorem walk_eq_of_lt (hφ : WeightMap φ) {f t o s : ℕ}
    (htrue : ∀ g < f, factV gen L' pl fx fc fy g = φ (W g)) :
    ∀ (w : List ℕ) (q cur : ℕ), (∀ c ∈ w, gen (inv c) = (gen c)⁻¹) →
      walkOK fx fc fy inv refs f t o s q cur w = true → t < q →
      rep gen L' pl cur * evalWord gen w * (rep gen L' pl s)⁻¹ = φ (walkA W refs f t o q w) := by
  intro w
  induction w with
  | nil =>
    intro q cur _ h _
    have hcur : cur = s := Nat.eq_of_beq_eq_true h
    subst hcur
    simp [walkA, hφ.map_zero]
  | cons c w ih =>
    intro q cur hw h htq
    simp only [walkOK, Nat.add_eq] at h
    rw [beq_false (show q ≠ t by omega), Bool.cond_false, Bool.and_eq_true] at h
    obtain ⟨href, hrest⟩ := h
    rw [walk_cons_eq' gen L' pl cur c (refNext fx fy (refs (o + q))) s w,
      ref_eq hφ htrue (hw c (by simp)) href,
      ih (q + 1) _ (fun c' hc' => hw c' (by simp [hc'])) hrest (by omega), ← hφ.map_add]
    simp only [walkA, posRef_of_ne (show q ≠ t by omega)]

theorem walk_eq (hφ : WeightMap φ) {f t o s : ℕ}
    (htrue : ∀ g < f, factV gen L' pl fx fc fy g = φ (W g)) :
    ∀ (w : List ℕ) (q cur : ℕ), (∀ c ∈ w, gen (inv c) = (gen c)⁻¹) →
      walkOK fx fc fy inv refs f t o s q cur w = true → q ≤ t → t < q + w.length →
      ∃ P Q : A, rep gen L' pl cur * evalWord gen w * (rep gen L' pl s)⁻¹ =
        φ P * factV gen L' pl fx fc fy f * φ Q ∧
        P + W f + Q = walkA W refs f t o q w := by
  intro w
  induction w with
  | nil => intro q cur _ _ h1 h2; simp at h2; omega
  | cons c w ih =>
    intro q cur hw h hqt htl
    have hw' : ∀ c' ∈ w, gen (inv c') = (gen c')⁻¹ := fun c' hc' => hw c' (by simp [hc'])
    simp only [walkOK, Nat.add_eq] at h
    rcases Nat.eq_or_lt_of_le hqt with rfl | hlt'
    · rw [Nat.beq_refl, Bool.cond_true] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨hx, hc⟩, hrest⟩ := h
      have hx' := Nat.eq_of_beq_eq_true hx
      have hc' := Nat.eq_of_beq_eq_true hc
      have hr := walk_eq_of_lt hφ (refs := refs) (o := o) (s := s) htrue w (q + 1) (fy f)
        hw' hrest (Nat.lt_succ_self q)
      refine ⟨0, walkA W refs f q o (q + 1) w, ?_, ?_⟩
      · rw [walk_cons_eq' gen L' pl cur c (fy f) s w, hr, hφ.map_zero, one_mul]
        congr 1
        rw [factV, hx', hc']
      · simp only [walkA, zero_add, posRef_self, sW]
        rw [ite_eq_left (by omega), show 2 * f / 2 = f by omega]
    · rw [beq_false (show q ≠ t by omega), Bool.cond_false, Bool.and_eq_true] at h
      obtain ⟨href, hrest⟩ := h
      have hg := ref_eq hφ htrue (hw c (by simp)) href
      obtain ⟨P, Q, hPQ, hsum⟩ := ih (q + 1) _ hw' hrest hlt' (by simp at htl; omega)
      refine ⟨sW W (refs (o + q)) + P, Q, ?_, ?_⟩
      · rw [walk_cons_eq' gen L' pl cur c (refNext fx fy (refs (o + q))) s w, hg, hPQ,
          hφ.map_add]
        group
      · simp only [walkA, ← hsum, posRef_of_ne (show q ≠ t by omega)]
        abel

end Sound

section Pair

variable {G : Type*} [Group G]

@[expose] def pairW (wt₁ wt₂ : ℕ → ℕ) (f : ℕ) : ℤ × ℤ := (decodeW (wt₁ f), decodeW (wt₂ f))

theorem sW_pairW (wt₁ wt₂ : ℕ → ℕ) (r : ℕ) :
    sW (pairW wt₁ wt₂) r = (refW wt₁ r, refW wt₂ r) := by
  unfold sW refW pairW
  split <;> simp

theorem walkA_pairW (wt₁ wt₂ refs : ℕ → ℕ) (f t o : ℕ) :
    ∀ (w : List ℕ) (q : ℕ), walkA (pairW wt₁ wt₂) refs f t o q w =
      (walkW wt₁ refs f t o q w, walkW wt₂ refs f t o q w) := by
  intro w
  induction w with
  | nil => intro q; rfl
  | cons c w ih =>
    intro q
    rw [walkA, walkW, walkW, ih, sW_pairW]
    rfl

theorem factV_eq_of_weights {gen : ℕ → G} {L N F : ℕ}
    {fx fc fy kind wi fs ft fo refs pl inv wt₁ wt₂ tgt₁ tgt₂ : ℕ → ℕ}
    {rels subs : List (List ℕ)} {φ : ℤ × ℤ → G} (hφ : WeightMap φ)
    (hinv : ∀ c ≤ L, gen (inv c) = (gen c)⁻¹)
    (hlet : ∀ w ∈ rels ++ subs, ∀ c ∈ w, c ≤ L)
    (hrels : ∀ w ∈ rels, evalWord gen w = 1)
    (hsubs : ∀ j < subs.length, evalWord gen (wordAt subs j) = φ ((tgt₁ j : ℤ), (tgt₂ j : ℤ)))
    (hfacts : factsOK N (L + 1) fx fc fy kind wi fs ft fo refs pl inv rels subs 0 F = true)
    (hw₁ : weightsOK wt₁ kind wi ft fo refs tgt₁ rels subs 0 F = true)
    (hw₂ : weightsOK wt₂ kind wi ft fo refs tgt₂ rels subs 0 F = true) :
    ∀ f < F, factV gen (L + 1) pl fx fc fy f = φ (pairW wt₁ wt₂ f) := by
  set L' := L + 1
  have hwinv : ∀ w ∈ rels ++ subs, ∀ c ∈ w, gen (inv c) = (gen c)⁻¹ :=
    fun w hw c hc => hinv c (hlet w hw c hc)
  intro f
  induction f using Nat.strong_induction_on with
  | _ f ih =>
    intro hf
    have ih' : ∀ g < f, factV gen L' pl fx fc fy g = φ (pairW wt₁ wt₂ g) :=
      fun g hg => ih g hg (lt_trans hg hf)
    have h := factOK_of_factsOK hfacts f (Nat.zero_le f) (by simpa using hf)
    have h₁ := weightOK_of_weightsOK hw₁ f (Nat.zero_le f) (by simpa using hf)
    have h₂ := weightOK_of_weightsOK hw₂ f (Nat.zero_le f) (by simpa using hf)
    unfold factOK at h
    unfold weightOK at h₁ h₂
    simp only [Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨_, _, h⟩ := h
    split at h
    ·
      next hk =>
      have h₁' : Nat.beq (wt₁ f) 0 = true := by rw [hk] at h₁; exact h₁
      have h₂' : Nat.beq (wt₂ f) 0 = true := by rw [hk] at h₂; exact h₂
      simp only [Bool.and_eq_true, Nat.blt_eq] at h
      obtain ⟨hpl, hcL, hxy⟩ := h
      have hpl' : pl (fy f) = fx f * L' + fc f := by simpa using Nat.eq_of_beq_eq_true hpl
      have hL0 : 0 < L' := by omega
      have hdiv : pl (fy f) / L' = fx f := by
        rw [hpl', Nat.add_comm, Nat.add_mul_div_right _ _ hL0, Nat.div_eq_of_lt hcL,
          Nat.zero_add]
      have hmod : pl (fy f) % L' = fc f := by
        rw [hpl', Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hcL]
      have hy0 : 0 < fy f := lt_of_le_of_lt (Nat.zero_le _) hxy
      have hw0 : pairW wt₁ wt₂ f = 0 := by
        unfold pairW decodeW
        rw [Nat.eq_of_beq_eq_true h₁', Nat.eq_of_beq_eq_true h₂']
        rfl
      rw [hw0, hφ.map_zero, factV, rep_eq gen L' pl hy0 (by rw [hdiv]; exact hxy), hdiv,
        hmod]
      simp
    ·
      next hk =>
      have h₁' : wsumOK wt₁ refs f (ft f) (fo f) 0 0 (wordAt rels (wi f)) 0 0 = true := by
        rw [hk] at h₁; exact h₁
      have h₂' : wsumOK wt₂ refs f (ft f) (fo f) 0 0 (wordAt rels (wi f)) 0 0 = true := by
        rw [hk] at h₂; exact h₂
      simp only [Bool.and_eq_true, Nat.blt_eq] at h
      obtain ⟨h1, h2, h3⟩ := h
      have hwm := wordAt_mem h1
      obtain ⟨P, Q, hPQ, hsum⟩ := walk_eq hφ ih' _ 0 (fs f)
        (hwinv _ (List.mem_append_left _ hwm)) h3 (Nat.zero_le _) (by simpa using h2)
      have e₁ : walkW wt₁ refs f (ft f) (fo f) 0 (wordAt rels (wi f)) = 0 := by
        simpa using walkW_of_wsumOK _ _ _ _ h₁'
      have e₂ : walkW wt₂ refs f (ft f) (fo f) 0 (wordAt rels (wi f)) = 0 := by
        simpa using walkW_of_wsumOK _ _ _ _ h₂'
      rw [walkA_pairW, e₁, e₂] at hsum
      rw [hrels _ hwm, mul_one, mul_inv_cancel] at hPQ
      exact hφ.eq_of_mul_mul (P := P) (Q := Q) (T := 0) (by rw [hφ.map_zero]; exact hPQ) hsum
    ·
      next hk =>
      have h₁' : wsumOK wt₁ refs f (ft f) (fo f) (tgt₁ (wi f)) 0 (wordAt subs (wi f)) 0 0 =
          true := by
        rw [hk] at h₁; exact h₁
      have h₂' : wsumOK wt₂ refs f (ft f) (fo f) (tgt₂ (wi f)) 0 (wordAt subs (wi f)) 0 0 =
          true := by
        rw [hk] at h₂; exact h₂
      simp only [Bool.and_eq_true, Nat.blt_eq] at h
      obtain ⟨h1, h2, h3⟩ := h
      have hwm := wordAt_mem h1
      obtain ⟨P, Q, hPQ, hsum⟩ := walk_eq hφ ih' _ 0 0
        (hwinv _ (List.mem_append_right _ hwm)) h3 (Nat.zero_le _) (by simpa using h2)
      have e₁ : walkW wt₁ refs f (ft f) (fo f) 0 (wordAt subs (wi f)) = tgt₁ (wi f) := by
        simpa using walkW_of_wsumOK _ _ _ _ h₁'
      have e₂ : walkW wt₂ refs f (ft f) (fo f) 0 (wordAt subs (wi f)) = tgt₂ (wi f) := by
        simpa using walkW_of_wsumOK _ _ _ _ h₂'
      rw [walkA_pairW, e₁, e₂] at hsum
      rw [rep_zero, one_mul, inv_one, mul_one, hsubs _ h1] at hPQ
      exact hφ.eq_of_mul_mul (P := P) (Q := Q) hPQ hsum
    · exact absurd h (by simp)

theorem phi_eq_one_of_weights {gen : ℕ → G} {L N F : ℕ}
    {fx fc fy kind wi fs ft fo refs pl inv wt₁ wt₂ tgt₁ tgt₂ : ℕ → ℕ}
    {rels subs : List (List ℕ)} {φ : ℤ × ℤ → G} (hφ : WeightMap φ)
    (hinv : ∀ c ≤ L, gen (inv c) = (gen c)⁻¹) (hε : gen L = 1)
    (hlet : ∀ w ∈ rels ++ subs, ∀ c ∈ w, c ≤ L)
    (hrels : ∀ w ∈ rels, evalWord gen w = 1)
    (hsubs : ∀ j < subs.length, evalWord gen (wordAt subs j) = φ ((tgt₁ j : ℤ), (tgt₂ j : ℤ)))
    (hfacts : factsOK N (L + 1) fx fc fy kind wi fs ft fo refs pl inv rels subs 0 F = true)
    (hw₁ : weightsOK wt₁ kind wi ft fo refs tgt₁ rels subs 0 F = true)
    (hw₂ : weightsOK wt₂ kind wi ft fo refs tgt₂ rels subs 0 F = true)
    {f : ℕ} (hf : f < F) (hxy : fx f = fy f) (hc : fc f = L) :
    φ (pairW wt₁ wt₂ f) = 1 := by
  rw [← factV_eq_of_weights hφ hinv hlet hrels hsubs hfacts hw₁ hw₂ f hf, factV, hc, hε,
    hxy, mul_one, mul_inv_cancel]

theorem wordAt_codes {m : ℕ} : ∀ (ws : List (List (Fin m × Bool))) (j : ℕ), j < ws.length →
    wordAt (codes ws) j = (ws.getD j []).map letterCode
  | [], _, h => absurd h (by simp)
  | _ :: _, 0, _ => rfl
  | _ :: ws, j + 1, h => by
    rw [codes, List.map_cons, wordAt, List.getD_cons_succ]
    exact wordAt_codes ws j (by simpa using h)

theorem phi_eq_one_of_weights_presented {m : ℕ} {rels : Set (FreeGroup (Fin m))} {N F : ℕ}
    {fx fc fy kind wi fs ft fo refs pl wt₁ wt₂ tgt₁ tgt₂ : ℕ → ℕ}
    {φ : ℤ × ℤ → PresentedGroup rels} (hφ : WeightMap φ)
    (relWords subWords : List (List (Fin m × Bool))) (ws : List (List ℕ))
    (hrels : ∀ w ∈ relWords, FreeGroup.mk w ∈ rels)
    (hsubs : ∀ j < subWords.length, PresentedGroup.mk rels (FreeGroup.mk (subWords.getD j [])) =
      φ ((tgt₁ j : ℤ), (tgt₂ j : ℤ)))
    (hws : derivedOK (2 * m) (invLetter m) (codes relWords) ws = true)
    (hfacts : factsOK N (2 * m + 1) fx fc fy kind wi fs ft fo refs pl (invLetter m) ws
      (codes subWords) 0 F = true)
    (hw₁ : weightsOK wt₁ kind wi ft fo refs tgt₁ ws (codes subWords) 0 F = true)
    (hw₂ : weightsOK wt₂ kind wi ft fo refs tgt₂ ws (codes subWords) 0 F = true)
    {f : ℕ} (hf : f < F) (hxy : fx f = fy f) (hc : fc f = 2 * m) :
    φ (pairW wt₁ wt₂ f) = 1 := by
  have hbase : ∀ r ∈ codes relWords, evalWord (presLetter rels) r = 1 := by
    intro w hw
    simp only [codes, List.mem_map] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    rw [evalWord_presLetter]
    exact PresentedGroup.one_of_mem (hrels v hv)
  have hlet : ∀ w ∈ ws ++ codes subWords, ∀ c ∈ w, c ≤ 2 * m := by
    intro w hw c hc
    rcases List.mem_append.mp hw with hw | hw
    · simp only [derivedOK, List.all_eq_true, Bool.and_eq_true, Nat.blt_eq] at hws
      exact Nat.lt_succ_iff.mp ((hws w hw).1 c hc)
    · have := lettersOK_codes subWords
      simp only [lettersOK, List.all_eq_true, Nat.blt_eq] at this
      exact Nat.le_of_lt (this w hw c hc)
  refine phi_eq_one_of_weights (gen := presLetter rels) (inv := invLetter m) hφ
    (fun c hc => presLetter_invLetter rels hc) (presLetter_eps rels) hlet
    (evalWord_of_derivedOK (presLetter_eps rels)
      (fun c hc => presLetter_invLetter rels (Nat.le_of_lt hc)) hbase hws) ?_ hfacts hw₁ hw₂ hf
    hxy hc
  intro j hj
  have hj' : j < subWords.length := by simpa [codes] using hj
  rw [wordAt_codes subWords j hj', evalWord_presLetter]
  exact hsubs j hj'

end Pair

end CFSG.Sporadic.Bridge.J2
