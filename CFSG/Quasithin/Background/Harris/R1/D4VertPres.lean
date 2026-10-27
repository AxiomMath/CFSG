module

public import CFSG.Quasithin.Background.Harris.R1.J2VertHom
public import Certificates.Certificate300204

public section

namespace CFSG.Quasithin.Background.Harris.R1.D4Vert

open CFSG.CosetTable CFSG.Quasithin.Background.Harris.R1.J2Vert

theorem card_PG_l28Tw_le {e₁ e₄ : Bool}
    (h : e₁ = true ∨ e₄ = true) :
    Finite (PG 3 (l28Tw e₁ e₄)) ∧ Nat.card (PG 3 (l28Tw e₁ e₄)) ≤ 504 :=
  Certificates.certificate300204.2.1 e₁ e₄ h

theorem card_PG_h_le :
    Finite (PG 4 hRels) ∧ Nat.card (PG 4 hRels) ≤ 258048 :=
  Certificates.certificate300204.2.2.1

theorem card_PG_n_le :
    Finite (PG 5 nRels) ∧ Nat.card (PG 5 nRels) ≤ 86016 :=
  Certificates.certificate300204.2.2.2

section Words

variable {X : Type*} [Group X]

@[expose] def evalWord {m : ℕ} (g : Fin m → X) (r : List (Fin m × Bool)) : X :=
  (r.map fun p => if p.2 then g p.1 else (g p.1)⁻¹).prod

theorem evalWord_cons {m : ℕ} (g : Fin m → X) (p : Fin m × Bool) (r : List (Fin m × Bool)) :
    evalWord g (p :: r) = (if p.2 then g p.1 else (g p.1)⁻¹) * evalWord g r := by
  simp [evalWord]

theorem evalWord_nil {m : ℕ} (g : Fin m → X) : evalWord g [] = 1 := rfl

theorem evalWord_append {m : ℕ} (g : Fin m → X) (r s : List (Fin m × Bool)) :
    evalWord g (r ++ s) = evalWord g r * evalWord g s := by
  simp [evalWord]

@[expose] def liftW (r : List (Fin 2 × Bool)) : List (Fin 3 × Bool) :=
  r.map fun p => (p.1.castSucc, p.2)

theorem evalWord_liftW (a b z : X) (r : List (Fin 2 × Bool)) :
    evalWord ![a, b, z] (liftW r) = evalWord ![a, b] r := by
  have h : ∀ i : Fin 2, (![a, b, z] : Fin 3 → X) i.castSucc = ![a, b] i := by
    intro i
    fin_cases i <;> rfl
  simp [evalWord, liftW, h, List.map_map, Function.comp_def]

variable {z a b : X}

theorem commute_evalWord (hza : Commute z a) (hzb : Commute z b) (r : List (Fin 2 × Bool)) :
    Commute z (evalWord ![a, b] r) := by
  induction r with
  | nil => simp [evalWord]
  | cons p r ih =>
    rw [evalWord_cons]
    refine Commute.mul_right ?_ ih
    obtain ⟨x, s⟩ := p
    fin_cases x <;> cases s <;> simp [hza, hzb, hza.inv_right, hzb.inv_right]

theorem evalWord_twist (hz2 : z * z = 1) (hza : Commute z a) (hzb : Commute z b) (i j : ℕ)
    (r : List (Fin 2 × Bool)) :
    evalWord ![a * z ^ i, b * z ^ j] r = evalWord ![a, b] r *
      z ^ (i * r.countP (fun p => p.1 == 0) + j * r.countP (fun p => p.1 == 1)) := by
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hzi : ∀ n : ℕ, (z ^ n)⁻¹ = z ^ n := fun n => by rw [← inv_pow, hzinv]
  induction r with
  | nil => simp [evalWord]
  | cons p r ih =>
    rw [evalWord_cons, ih, evalWord_cons]
    have hc := commute_evalWord hza hzb r
    obtain ⟨x, s⟩ := p
    have key : ∀ (c : X) (n : ℕ), Commute z c → ∀ N N' : ℕ, n + N = N' →
        (if s then c * z ^ n else (c * z ^ n)⁻¹) * (evalWord ![a, b] r * z ^ N) =
          (if s then c else c⁻¹) * evalWord ![a, b] r * z ^ N' := by
      intro c n hcz N N' hN
      subst hN
      have h1 : Commute (z ^ n) (evalWord ![a, b] r) := hc.pow_left n
      have h2 : Commute (z ^ n) c⁻¹ := (hcz.inv_right).pow_left n
      cases s
      · simp only [Bool.false_eq_true, ite_false, mul_inv_rev, hzi, pow_add]
        rw [mul_assoc, ← mul_assoc (z ^ n), h2.eq, mul_assoc, mul_assoc c⁻¹, ← mul_assoc (z ^ n),
          h1.eq]
        simp only [mul_assoc]
      · simp only [ite_true, pow_add]
        rw [mul_assoc, mul_assoc c, ← mul_assoc (z ^ n), h1.eq]
        simp only [mul_assoc]
    fin_cases x
    · simp only [List.countP_cons]
      refine key a i hza _ _ ?_
      simp
      ring
    · simp only [List.countP_cons]
      refine key b j hzb _ _ ?_
      simp
      ring

@[expose] def l28R (i : ℕ) : List (Fin 2 × Bool) := l28Rels.getD i []

theorem l28Rels_eq : l28Rels = [l28R 0, l28R 1, l28R 2, l28R 3] := by decide

theorem mem_l28Rels {r : List (Fin 2 × Bool)} :
    r ∈ l28Rels ↔ r = l28R 0 ∨ r = l28R 1 ∨ r = l28R 2 ∨ r = l28R 3 := by
  rw [l28Rels_eq]
  simp

theorem l28Tw_eq (e₁ e₄ : Bool) : l28Tw e₁ e₄ =
    [[(2, true), (2, true)], [(2, true), (0, true), (2, false), (0, false)],
      [(2, true), (1, true), (2, false), (1, false)],
      liftW (l28R 0) ++ (if e₁ then [(2, false)] else []), liftW (l28R 1), liftW (l28R 2),
      liftW (l28R 3) ++ (if e₄ then [(2, false)] else [])] := by
  cases e₁ <;> cases e₄ <;> decide

theorem countP_l28R :
    (l28R 0).countP (fun p => p.1 == 0) = 2 ∧ (l28R 0).countP (fun p => p.1 == 1) = 0 ∧
    (l28R 1).countP (fun p => p.1 == 0) = 0 ∧ (l28R 1).countP (fun p => p.1 == 1) = 3 ∧
    (l28R 2).countP (fun p => p.1 == 0) = 7 ∧ (l28R 2).countP (fun p => p.1 == 1) = 7 ∧
    (l28R 3).countP (fun p => p.1 == 0) = 14 ∧ (l28R 3).countP (fun p => p.1 == 1) = 14 := by
  decide

variable {z a b : X}

theorem pow_of_mul_self (hz2 : z * z = 1) (n : ℕ) : z ^ n = 1 ∨ z ^ n = z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases ih with h | h
    · right
      rw [pow_succ, h, one_mul]
    · left
      rw [pow_succ, h, hz2]

end Words

section Lift

variable {X : Type*} [Group X] {z a b : X}

theorem l28_lift_aux (hz2 : z * z = 1) (hza : Commute z a)
    (hzb : Commute z b) (hbig : 504 < Nat.card (Subgroup.closure ({a, b, z} : Set X)))
    (h0 : evalWord ![a, b] (l28R 0) = 1 ∨ evalWord ![a, b] (l28R 0) = z)
    (h1 : evalWord ![a, b] (l28R 1) = 1) (h2 : evalWord ![a, b] (l28R 2) = 1)
    (h3 : evalWord ![a, b] (l28R 3) = 1 ∨ evalWord ![a, b] (l28R 3) = z) :
    ∀ r ∈ l28Rels, evalWord ![a, b] r = 1 := by
  classical
  by_cases hA : evalWord ![a, b] (l28R 0) = 1 ∧ evalWord ![a, b] (l28R 3) = 1
  · intro r hr
    rcases mem_l28Rels.1 hr with rfl | rfl | rfl | rfl
    exacts [hA.1, h1, h2, hA.2]
  exfalso
  set e₁ : Bool := decide (evalWord ![a, b] (l28R 0) = z) with he₁
  set e₄ : Bool := decide (evalWord ![a, b] (l28R 3) = z) with he₄
  have hne : e₁ = true ∨ e₄ = true := by
    by_contra hc
    simp only [not_or, Bool.not_eq_true, he₁, he₄, decide_eq_false_iff_not] at hc
    exact hA ⟨h0.resolve_right hc.1, h3.resolve_right hc.2⟩
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hev : evalWord ![a, b, z] [(2, false)] = z := by simp [evalWord, hzinv]
  have hcomm : ∀ c : X, Commute z c → z * (c * (z⁻¹ * c⁻¹)) = 1 := fun c h => by
    rw [← mul_assoc, ← mul_assoc, h.mul_inv_cancel, mul_inv_cancel]
  have hrel : ∀ r ∈ l28Tw e₁ e₄, evalWord ![a, b, z] r = 1 := by
    intro r hr
    rw [l28Tw_eq] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [evalWord, hz2]
    · simpa [evalWord] using hcomm a hza
    · simpa [evalWord] using hcomm b hzb
    · rw [evalWord_append, evalWord_liftW]
      cases hz : e₁
      · have : evalWord ![a, b] (l28R 0) ≠ z := by simpa [he₁] using hz
        simp only [Bool.false_eq_true, ite_false, evalWord_nil, mul_one]
        exact h0.resolve_right this
      · have : evalWord ![a, b] (l28R 0) = z := by simpa [he₁] using hz
        simp only [ite_true, hev, this, hz2]
    · rw [evalWord_liftW, h1]
    · rw [evalWord_liftW, h2]
    · rw [evalWord_append, evalWord_liftW]
      cases hz : e₄
      · have : evalWord ![a, b] (l28R 3) ≠ z := by simpa [he₄] using hz
        simp only [Bool.false_eq_true, ite_false, evalWord_nil, mul_one]
        exact h3.resolve_right this
      · have : evalWord ![a, b] (l28R 3) = z := by simpa [he₄] using hz
        simp only [ite_true, hev, this, hz2]
  obtain ⟨hfin, hle⟩ := card_PG_l28Tw_le (e₁ := e₁) (e₄ := e₄) hne
  have hp : ∀ r ∈ l28Tw e₁ e₄,
      (r.map fun p => if p.2 then (![a, b, z] : Fin 3 → X) p.1 else (![a, b, z] p.1)⁻¹).prod = 1 :=
    hrel
  have hr := range_pgHom hp
  have hcard := Nat.card_le_card_of_surjective _ (pgHom hp).rangeRestrict_surjective
  rw [hr] at hcard
  have hrange : Set.range (![a, b, z] : Fin 3 → X) = {a, b, z} := by
    ext x
    simp
    tauto
  rw [hrange] at hcard
  exact absurd (hbig.trans_le (hcard.trans hle)) (lt_irrefl _)

theorem closure_twist_eq (i j : ℕ) :
    Subgroup.closure ({a * z ^ i, b * z ^ j, z} : Set X) = Subgroup.closure ({a, b, z} : Set X) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    have hz : z ∈ Subgroup.closure ({a, b, z} : Set X) := Subgroup.subset_closure (by simp)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact mul_mem (Subgroup.subset_closure (by simp)) (pow_mem hz i)
    · exact mul_mem (Subgroup.subset_closure (by simp)) (pow_mem hz j)
    · exact hz
  · rw [Subgroup.closure_le]
    have hz : z ∈ Subgroup.closure ({a * z ^ i, b * z ^ j, z} : Set X) :=
      Subgroup.subset_closure (by simp)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact (Subgroup.mul_mem_cancel_right _ (pow_mem hz i)).1 (Subgroup.subset_closure (by simp))
    · exact (Subgroup.mul_mem_cancel_right _ (pow_mem hz j)).1 (Subgroup.subset_closure (by simp))
    · exact hz

theorem exists_l28_lift (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hza : z * a = a * z) (hzb : z * b = b * z)
    (hrel : ∀ r ∈ l28Rels,
      (r.map fun p => if p.2 then ![a, b] p.1 else (![a, b] p.1)⁻¹).prod = 1 ∨
      (r.map fun p => if p.2 then ![a, b] p.1 else (![a, b] p.1)⁻¹).prod = z)
    (hbig : 504 < Nat.card (Subgroup.closure ({a, b, z} : Set X))) [Finite X] :
    ∃ a' b' : X, (a' = a ∨ a' = a * z) ∧ (b' = b ∨ b' = b * z) ∧
      ∀ r ∈ l28Rels,
        (r.map fun p => if p.2 then ![a', b'] p.1 else (![a', b'] p.1)⁻¹).prod = 1 := by
  have hrel' : ∀ r ∈ l28Rels, evalWord ![a, b] r = 1 ∨ evalWord ![a, b] r = z := hrel
  have hza' : Commute z a := hza
  have hzb' : Commute z b := hzb
  have hodd : ∀ n : ℕ, z ^ (2 * n + 1) = z := fun n => by
    rw [pow_succ, pow_mul, sq, hz2, one_pow, one_mul]
  have heven : ∀ n : ℕ, z ^ (2 * n) = 1 := fun n => by
    rw [pow_mul, sq, hz2, one_pow]
  have hz3 : z ^ 3 = z := hodd 1
  have hz7 : z ^ 7 = z := hodd 3
  have hz14 : z ^ 14 = 1 := heven 7
  have hclosed : ∀ u v : X, (u = 1 ∨ u = z) → (v = 1 ∨ v = z) → u * v = 1 ∨ u * v = z := by
    rintro u v (rfl | rfl) (rfl | rfl) <;> simp [hz2]
  have hcz : ∀ n : ℕ, Commute z (z ^ n) := fun n => (Commute.refl z).pow_right n
  have key : ∀ i j : ℕ, (i = 0 ∨ i = 1) → (j = 0 ∨ j = 1) →
      evalWord ![a, b] (l28R 1) * z ^ (j * 3) = 1 →
      evalWord ![a, b] (l28R 2) * z ^ (i * 7 + j * 7) = 1 →
      ∃ a' b' : X, (a' = a ∨ a' = a * z) ∧ (b' = b ∨ b' = b * z) ∧
        ∀ r ∈ l28Rels, evalWord ![a', b'] r = 1 := by
    intro i j hi hj e1 e2
    have tw := fun k => evalWord_twist (i := i) (j := j) hz2 hza' hzb' (l28R k)
    obtain ⟨c00, c01, c10, c11, c20, c21, c30, c31⟩ := countP_l28R
    have t0 := tw 0
    have t1 := tw 1
    have t2 := tw 2
    have t3 := tw 3
    rw [c00, c01] at t0
    rw [c10, c11] at t1
    rw [c20, c21] at t2
    rw [c30, c31] at t3
    refine ⟨a * z ^ i, b * z ^ j, ?_, ?_, ?_⟩
    · rcases hi with rfl | rfl <;> simp
    · rcases hj with rfl | rfl <;> simp
    · refine l28_lift_aux hz2 (hza'.mul_right (hcz i)) (hzb'.mul_right (hcz j)) ?_ ?_ ?_ ?_ ?_
      · rwa [closure_twist_eq]
      · rw [t0]
        exact hclosed _ _ (hrel' _ (mem_l28Rels.2 (Or.inl rfl)))
          (pow_of_mul_self hz2 _)
      · rw [t1]
        simpa using e1
      · rw [t2]
        exact e2
      · rw [t3]
        exact hclosed _ _ (hrel' _ (mem_l28Rels.2 (Or.inr (Or.inr (Or.inr rfl)))))
          (pow_of_mul_self hz2 _)
  have hv1 := hrel' _ (mem_l28Rels.2 (Or.inr (Or.inl rfl)))
  have hv2 := hrel' _ (mem_l28Rels.2 (Or.inr (Or.inr (Or.inl rfl))))
  rcases hv1 with h1 | h1 <;> rcases hv2 with h2 | h2
  · exact key 0 0 (Or.inl rfl) (Or.inl rfl) (by simp [h1]) (by simp [h2])
  · exact key 1 0 (Or.inr rfl) (Or.inl rfl) (by simp [h1]) (by simp [h2, hz7, hz2])
  · exact key 1 1 (Or.inr rfl) (Or.inr rfl) (by simp [h1, hz3, hz2]) (by simp [h2, hz14])
  · exact key 0 1 (Or.inl rfl) (Or.inr rfl) (by simp [h1, hz3, hz2]) (by simp [h2, hz7, hz2])

end Lift

end CFSG.Quasithin.Background.Harris.R1.D4Vert
