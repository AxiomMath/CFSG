module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.J2Inspect

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B.J2

open Subgroup CFSG.RankThree.PartTwo.Sec4.Sporadic.J2
  CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.J2 CFSG.ComponentClassification.J2Cover
open CFSG.Monster.B.Co2 (Rep)
open CFSG.LocalAnalysis.ComponentInitial.FourGroup (kleinFourOf mem_kleinFourOf card_kleinFourOf
  kleinFourOf_le)
open scoped commutatorElement Pointwise

@[expose] def pk (t : List ℕ) : ℕ := t.foldr (fun v acc => v + 512 * acc) 0

@[expose] def ev (c p : ℕ) : ℕ := c / 512 ^ p % 512

@[expose] def eqOn (f g : ℕ → ℕ) : Bool := (List.range 315).all fun p => f p == g p

@[expose] def neOn (f g : ℕ → ℕ) : Bool := (List.range 315).any fun p => f p != g p

@[expose] def ct (i : ℕ) : ℕ := pk vA[i]!.toList

@[expose] def cz : ℕ := pk zArr.toList

@[expose] def cx : ℕ := pk xArr.toList

@[expose] def okL (t : Array ℕ) : Bool := t.size == 315 && t.toList.all fun v => v < 512

@[expose] def vS (j : ℕ) : Bool :=
  neOn (ev (ct (3 * j))) id && neOn (ev (ct (3 * j + 1))) id &&
    neOn (ev (ct (3 * j))) (ev (ct (3 * j + 1))) &&
    eqOn (fun p => ev (ct (3 * j)) (ev (ct (3 * j)) p)) id &&
    eqOn (fun p => ev (ct (3 * j + 1)) (ev (ct (3 * j + 1)) p)) id &&
    eqOn (fun p => ev (ct (3 * j)) (ev (ct (3 * j + 1)) p)) (ev (ct (3 * j + 2))) &&
    eqOn (fun p => ev (ct (3 * j + 1)) (ev (ct (3 * j)) p)) (ev (ct (3 * j + 2)))

@[expose] def vN (j : ℕ) : Bool :=
  [cz, cx].all fun e => (List.range 3).all fun p => (List.range 3).any fun q =>
    eqOn (fun r => ev e (ev (ct (3 * j + p)) r)) (fun r => ev (ct (3 * j + q)) (ev e r))

@[expose] def vC (j : ℕ) : Bool :=
  (List.range 3).all fun p => (List.range 3).any fun q => [cz, cx].any fun e =>
    eqOn (ev (ct (3 * j + p)))
      (fun r => ev (ct (3 * j + q)) (ev e (ev (ct (3 * j + q)) (ev e (ev e r)))))

theorem codes_ok : (okL zArr && okL xArr && (List.range 18).all fun i => okL vA[i]!) = true := by
  decide +kernel

theorem vS_ok : (List.range 6).all vS = true := by decide +kernel

theorem vN_ok : (List.range 6).all vN = true := by decide +kernel

theorem vC_ok : (List.range 6).all vC = true := by decide +kernel

theorem ev_pk {t : List ℕ} (ht : ∀ v ∈ t, v < 512) (p : ℕ) : ev (pk t) p = t.getD p 0 := by
  induction t generalizing p with
  | nil => simp [ev, pk]
  | cons v t ih =>
    have hv : v < 512 := ht v (by simp)
    have ih' := ih (fun w hw => ht w (by simp [hw]))
    have hc : pk (v :: t) = v + 512 * pk t := rfl
    rcases p with _ | p
    · simp only [ev, hc, pow_zero, Nat.div_one, List.getD_cons_zero]
      omega
    · have e : (v + 512 * pk t) / 512 = pk t := by omega
      have ih'' := ih' p
      simp only [ev] at ih'' ⊢
      rw [List.getD_cons_succ, ← ih'', hc, pow_succ', ← Nat.div_div_eq_div_mul, e]

theorem ev_of_okL {t : Array ℕ} (h : okL t = true) {p : ℕ} (hp : p < 315) :
    ev (pk t.toList) p = t[p]! := by
  simp only [okL, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  have hp' : p < t.size := by omega
  rw [ev_pk h2, getElem!_pos t p hp', List.getD_eq_getElem _ _ (by simpa using hp')]
  simp

theorem eqOn_spec {f g : ℕ → ℕ} (h : eqOn f g = true) {p : ℕ} (hp : p < 315) : f p = g p := by
  simp only [eqOn, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h p hp

theorem neOn_spec {f g : ℕ → ℕ} (h : neOn f g = true) : ∃ p < 315, f p ≠ g p := by
  simp only [neOn, List.any_eq_true, List.mem_range, bne_iff_ne] at h
  exact h

@[expose] def RepF (f : ℕ → ℕ) (g : GJ) : Prop := ∀ x : Fin 315, ((g.1 x : Fin 315) : ℕ) = f x

theorem repF_mul {f f' : ℕ → ℕ} {g h : GJ} (hg : RepF f g) (hh : RepF f' h) :
    RepF (fun p => f (f' p)) (g * h) := by
  intro x
  change ((g.1 (h.1 x) : Fin 315) : ℕ) = f (f' x)
  rw [← hh x, ← hg]

theorem repF_one : RepF id (1 : GJ) := fun _ => rfl

theorem eq_of_repF {f f' : ℕ → ℕ} {g h : GJ} (hg : RepF f g) (hh : RepF f' h)
    (e : ∀ p < 315, f p = f' p) : g = h := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  apply Fin.ext
  rw [hg x, hh x, e x x.2]

theorem ne_of_repF {f f' : ℕ → ℕ} {g h : GJ} (hg : RepF f g) (hh : RepF f' h)
    (e : ∃ p < 315, f p ≠ f' p) : g ≠ h := by
  rintro rfl
  obtain ⟨p, hp, hne⟩ := e
  exact hne ((hg ⟨p, hp⟩).symm.trans (hh ⟨p, hp⟩))

theorem repF_of_rep {t : Array ℕ} {g : GJ} (hr : Rep 315 t g.1) (h : okL t = true) :
    RepF (ev (pk t.toList)) g := fun x => by
  rw [ev_of_okL h x.2, hr x]

theorem okL_vA {i : ℕ} (hi : i < 18) : okL vA[i]! = true := by
  have h := codes_ok
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  exact h.2 i hi

theorem okL_z : okL zArr = true := by
  have h := codes_ok
  simp only [Bool.and_eq_true] at h
  exact h.1.1

theorem okL_x : okL xArr = true := by
  have h := codes_ok
  simp only [Bool.and_eq_true] at h
  exact h.1.2

theorem conj_closed_of_closure {G : Type*} [Group G] [Finite G] {S : Set G} {L : List G}
    (h : ∀ y ∈ L, ∀ g ∈ S, y * g * y⁻¹ ∈ S) :
    ∀ y ∈ closure {x | x ∈ L}, ∀ g ∈ S, y * g * y⁻¹ ∈ S := by
  intro y hy
  induction hy using Subgroup.closure_induction with
  | mem y hy => exact h y hy
  | one => intro g hg; simpa using hg
  | mul a b _ _ ha hb =>
    intro g hg
    have e : a * b * g * (a * b)⁻¹ = a * (b * g * b⁻¹) * a⁻¹ := by group
    rw [e]
    exact ha _ (hb g hg)
  | inv a _ ha =>
    have hpow : ∀ n : ℕ, ∀ g ∈ S, a ^ n * g * (a ^ n)⁻¹ ∈ S := by
      intro n
      induction n with
      | zero => intro g hg; simpa using hg
      | succ n ih =>
        intro g hg
        have e : a ^ (n + 1) * g * (a ^ (n + 1))⁻¹ = a * (a ^ n * g * (a ^ n)⁻¹) * a⁻¹ := by
          rw [pow_succ']
          group
        rw [e]
        exact ha _ (ih g hg)
    have hinv : a⁻¹ = a ^ (orderOf a - 1) := by
      have h1 : a ^ (orderOf a - 1) * a = 1 := by
        rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos a), pow_orderOf_eq_one]
      exact (eq_inv_of_mul_eq_one_left h1).symm
    rw [hinv]
    exact hpow _

set_option linter.unusedSectionVars false


theorem repF_tJ {i : ℕ} (hi : i < 18) : RepF (ev (ct i)) (tJ i) :=
  repF_of_rep (rep_tJ hi) (okL_vA hi)

theorem repF_z : RepF (ev cz) zJ := repF_of_rep rep_z okL_z

theorem repF_x : RepF (ev cx) xJ := repF_of_rep rep_x okL_x

theorem tJ_eq_one {i : ℕ} (hi : 18 ≤ i) : tJ i = 1 := by
  unfold tJ
  rw [dif_neg (by omega)]

theorem tJ_facts {j : ℕ} (hj : j < 6) :
    tJ (3 * j) ≠ 1 ∧ tJ (3 * j + 1) ≠ 1 ∧ tJ (3 * j) ≠ tJ (3 * j + 1) ∧
      tJ (3 * j) * tJ (3 * j) = 1 ∧ tJ (3 * j + 1) * tJ (3 * j + 1) = 1 ∧
      tJ (3 * j) * tJ (3 * j + 1) = tJ (3 * j + 2) ∧
      tJ (3 * j + 1) * tJ (3 * j) = tJ (3 * j + 2) := by
  have h := List.all_eq_true.1 vS_ok j (List.mem_range.2 hj)
  simp only [vS, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩ := h
  have r0 := repF_tJ (show 3 * j < 18 by omega)
  have r1 := repF_tJ (show 3 * j + 1 < 18 by omega)
  have r2 := repF_tJ (show 3 * j + 2 < 18 by omega)
  exact ⟨ne_of_repF r0 repF_one (neOn_spec a1), ne_of_repF r1 repF_one (neOn_spec a2),
    ne_of_repF r0 r1 (neOn_spec a3),
    eq_of_repF (repF_mul r0 r0) repF_one fun _ hp => eqOn_spec a4 hp,
    eq_of_repF (repF_mul r1 r1) repF_one fun _ hp => eqOn_spec a5 hp,
    eq_of_repF (repF_mul r0 r1) r2 fun _ hp => eqOn_spec a6 hp,
    eq_of_repF (repF_mul r1 r0) r2 fun _ hp => eqOn_spec a7 hp⟩

theorem tJ_sq0 (j : ℕ) : tJ (3 * j) * tJ (3 * j) = 1 := by
  by_cases hj : j < 6
  · exact (tJ_facts hj).2.2.2.1
  · rw [tJ_eq_one (i := 3 * j) (by omega), mul_one]

theorem tJ_sq1 (j : ℕ) : tJ (3 * j + 1) * tJ (3 * j + 1) = 1 := by
  by_cases hj : j < 6
  · exact (tJ_facts hj).2.2.2.2.1
  · rw [tJ_eq_one (i := 3 * j + 1) (by omega), mul_one]

theorem tJ_mul_eq (j : ℕ) : tJ (3 * j) * tJ (3 * j + 1) = tJ (3 * j + 2) := by
  by_cases hj : j < 6
  · exact (tJ_facts hj).2.2.2.2.2.1
  · rw [tJ_eq_one (i := 3 * j) (by omega), tJ_eq_one (i := 3 * j + 1) (by omega),
      tJ_eq_one (i := 3 * j + 2) (by omega), mul_one]

theorem tJ_comm (j : ℕ) : tJ (3 * j) * tJ (3 * j + 1) = tJ (3 * j + 1) * tJ (3 * j) := by
  by_cases hj : j < 6
  · exact (tJ_facts hj).2.2.2.2.2.1.trans (tJ_facts hj).2.2.2.2.2.2.symm
  · rw [tJ_eq_one (i := 3 * j) (by omega), tJ_eq_one (i := 3 * j + 1) (by omega)]

@[expose] noncomputable def VJ (j : ℕ) : Subgroup GJ :=
  kleinFourOf (tJ (3 * j)) (tJ (3 * j + 1)) (tJ_sq0 j) (tJ_sq1 j) (tJ_comm j)

theorem mem_VJ {j : ℕ} {v : GJ} : v ∈ VJ j ↔ v = 1 ∨ ∃ p < 3, v = tJ (3 * j + p) := by
  rw [VJ, mem_kleinFourOf, tJ_mul_eq j]
  constructor
  · rintro (h | h | h | h)
    · exact Or.inl h
    · exact Or.inr ⟨0, by norm_num, h⟩
    · exact Or.inr ⟨1, by norm_num, h⟩
    · exact Or.inr ⟨2, by norm_num, h⟩
  · rintro (h | ⟨p, hp, rfl⟩)
    · exact Or.inl h
    · interval_cases p
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))

theorem tJ_mem_VJ (j : ℕ) {q : ℕ} (hq : q < 3) : tJ (3 * j + q) ∈ VJ j :=
  mem_VJ.2 (Or.inr ⟨q, hq, rfl⟩)

theorem card_VJ {j : ℕ} (hj : j < 6) : Nat.card (VJ j) = 4 :=
  card_kleinFourOf (tJ_facts hj).1 (tJ_facts hj).2.1 (tJ_facts hj).2.2.1

theorem tJ_sq {j q : ℕ} (hq : q < 3) : tJ (3 * j + q) * tJ (3 * j + q) = 1 := by
  interval_cases q
  · exact tJ_sq0 j
  · exact tJ_sq1 j
  · calc tJ (3 * j + 2) * tJ (3 * j + 2) =
          tJ (3 * j) * (tJ (3 * j + 1) * tJ (3 * j)) * tJ (3 * j + 1) := by
          rw [← tJ_mul_eq j]; simp only [mul_assoc]
      _ = tJ (3 * j) * tJ (3 * j) * (tJ (3 * j + 1) * tJ (3 * j + 1)) := by
          rw [← tJ_comm j]; simp only [mul_assoc]
      _ = 1 := by rw [tJ_sq0, tJ_sq1, one_mul]

theorem tJ_inv {j q : ℕ} (hq : q < 3) : (tJ (3 * j + q))⁻¹ = tJ (3 * j + q) :=
  inv_eq_of_mul_eq_one_right (tJ_sq hq)

theorem zJ_inv : zJ⁻¹ = zJ * zJ :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact z_cube)

theorem xJ_inv : xJ⁻¹ = xJ * xJ :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact x_cube)

theorem card_E0 : Nat.card (Ej 0) = 9 :=
  (CFSG.RankThree.Asc83Table.ex27Basis x_cube y_cube z_comm_x z_comm_y z_ne_one 0).card

theorem conj_tJ_mem {j : ℕ} (hj : j < 6) {e : GJ} {c : ℕ} (hc : c = cz ∨ c = cx)
    (hr : RepF (ev c) e) {p : ℕ} (hp : p < 3) : e * tJ (3 * j + p) * e⁻¹ ∈ VJ j := by
  have h := List.all_eq_true.1 vN_ok j (List.mem_range.2 hj)
  unfold vN at h
  have hcm : c ∈ [cz, cx] := hc.elim (fun e => e ▸ List.mem_cons_self ..)
    (fun e => e ▸ List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have h1 := List.all_eq_true.1 h c hcm
  obtain ⟨q, hq, h3⟩ := List.any_eq_true.1 (List.all_eq_true.1 h1 p (List.mem_range.2 hp))
  have hq3 := List.mem_range.1 hq
  have h4 : e * tJ (3 * j + p) = tJ (3 * j + q) * e :=
    eq_of_repF (repF_mul hr (repF_tJ (by omega))) (repF_mul (repF_tJ (by omega)) hr)
      fun _ hr' => eqOn_spec h3 hr'
  rw [h4, mul_inv_cancel_right]
  exact tJ_mem_VJ j hq3

theorem E0_le_normalizer_VJ {j : ℕ} (hj : j < 6) : Ej 0 ≤ normalizer (VJ j : Set GJ) := by
  have key : ∀ {e : GJ} {c : ℕ}, (c = cz ∨ c = cx) → RepF (ev c) e →
      e ∈ normalizer (VJ j : Set GJ) := by
    intro e c hc hr
    refine mem_normalizer_of_conj_mem fun v hv => ?_
    rcases mem_VJ.1 hv with rfl | ⟨p, hp, rfl⟩
    · rw [mul_one, mul_inv_cancel]
      exact one_mem _
    · exact conj_tJ_mem hj hc hr hp
  rw [Ej_zero, closure_le]
  rintro e (rfl | rfl)
  · exact key (Or.inl rfl) repF_z
  · exact key (Or.inr rfl) repF_x

theorem VJ_eq_commutator {j : ℕ} (hj : j < 6) : VJ j = ⁅VJ j, Ej 0⁆ := by
  apply le_antisymm
  · intro v hv
    rcases mem_VJ.1 hv with rfl | ⟨p, hp, rfl⟩
    · exact one_mem _
    have h := List.all_eq_true.1 vC_ok j (List.mem_range.2 hj)
    unfold vC at h
    obtain ⟨q, hq, h2⟩ := List.any_eq_true.1 (List.all_eq_true.1 h p (List.mem_range.2 hp))
    obtain ⟨c, hc, h3⟩ := List.any_eq_true.1 h2
    have hq3 := List.mem_range.1 hq
    have r := repF_tJ (show 3 * j + q < 18 by omega)
    have r' := repF_tJ (show 3 * j + p < 18 by omega)
    rcases List.mem_cons.1 hc with hc | hc
    · rw [hc] at h3
      have he : tJ (3 * j + p) = tJ (3 * j + q) * zJ * tJ (3 * j + q) * (zJ * zJ) :=
        eq_of_repF r' (repF_mul (repF_mul (repF_mul r repF_z) r) (repF_mul repF_z repF_z))
          fun _ hr' => eqOn_spec h3 hr'
      have hc : tJ (3 * j + p) = ⁅tJ (3 * j + q), zJ⁆ := by
        rw [commutatorElement_def, tJ_inv hq3, zJ_inv]
        exact he
      rw [hc]
      exact commutator_mem_commutator (tJ_mem_VJ j hq3) zJ_mem_E0
    · rw [List.mem_singleton.1 hc] at h3
      have he : tJ (3 * j + p) = tJ (3 * j + q) * xJ * tJ (3 * j + q) * (xJ * xJ) :=
        eq_of_repF r' (repF_mul (repF_mul (repF_mul r repF_x) r) (repF_mul repF_x repF_x))
          fun _ hr' => eqOn_spec h3 hr'
      have hc : tJ (3 * j + p) = ⁅tJ (3 * j + q), xJ⁆ := by
        rw [commutatorElement_def, tJ_inv hq3, xJ_inv]
        exact he
      rw [hc]
      exact commutator_mem_commutator (tJ_mem_VJ j hq3) xJ_mem_E0
  · rw [commutator_le]
    intro v hv f hf
    have hfv : f * v⁻¹ * f⁻¹ ∈ VJ j :=
      (mem_normalizer_iff.mp (E0_le_normalizer_VJ hj hf) v⁻¹).mp (inv_mem hv)
    have e : ⁅v, f⁆ = v * (f * v⁻¹ * f⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact mul_mem hv hfv

@[expose] noncomputable def sgOf (j : ℕ) : List GJ := [zJ, xJ, tJ (3 * j), tJ (3 * j + 1)]

theorem closure_sgOf (j : ℕ) : closure {x | x ∈ sgOf j} = Ej 0 ⊔ VJ j := by
  apply le_antisymm
  · rw [closure_le]
    intro g hg
    simp only [sgOf, List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact mem_sup_left zJ_mem_E0
    · exact mem_sup_left xJ_mem_E0
    · exact mem_sup_right (tJ_mem_VJ j (q := 0) (by norm_num))
    · exact mem_sup_right (tJ_mem_VJ j (q := 1) (by norm_num))
  · refine sup_le ?_ ?_
    · rw [Ej_zero]
      exact closure_mono (by
        intro g hg
        rcases hg with rfl | rfl
        · change zJ ∈ sgOf j; simp [sgOf]
        · change xJ ∈ sgOf j; simp [sgOf])
    · exact kleinFourOf_le (subset_closure (show tJ (3 * j) ∈ sgOf j by simp [sgOf]))
        (subset_closure (show tJ (3 * j + 1) ∈ sgOf j by simp [sgOf]))

theorem card_E0_sup_VJ_eq {j : ℕ} (hj : j < 6) : Nat.card (Ej 0 ⊔ VJ j : Subgroup GJ) = 36 := by
  have hle : Nat.card (Ej 0 ⊔ VJ j : Subgroup GJ) ≤ 36 := by
    have e := coe_mul_of_left_le_normalizer_right (Ej 0) (VJ j) (E0_le_normalizer_VJ hj)
    have h1 : Nat.card (Ej 0 ⊔ VJ j : Subgroup GJ) =
        Nat.card ((Ej 0 : Set GJ) * (VJ j : Set GJ)) := by
      rw [← e]
      rfl
    rw [h1]
    calc Nat.card ((Ej 0 : Set GJ) * (VJ j : Set GJ))
        ≤ Nat.card (Ej 0 : Set GJ) * Nat.card (VJ j : Set GJ) := Set.natCard_mul_le
      _ = 36 := by
        change Nat.card (Ej 0) * Nat.card (VJ j) = 36
        rw [card_E0, card_VJ hj]
  have h9 : 9 ∣ Nat.card (Ej 0 ⊔ VJ j : Subgroup GJ) := by
    have := Subgroup.card_dvd_of_le (le_sup_left : Ej 0 ≤ Ej 0 ⊔ VJ j)
    rwa [card_E0] at this
  have h4 : 4 ∣ Nat.card (Ej 0 ⊔ VJ j : Subgroup GJ) := by
    have := Subgroup.card_dvd_of_le (le_sup_right : VJ j ≤ Ej 0 ⊔ VJ j)
    rwa [card_VJ hj] at this
  have h36 : 36 ∣ Nat.card (Ej 0 ⊔ VJ j : Subgroup GJ) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h9 h4
  have := Nat.le_of_dvd Nat.card_pos h36
  omega

end CFSG.RankThree.PartTwo.Sec14.Ronan148B.J2

end
