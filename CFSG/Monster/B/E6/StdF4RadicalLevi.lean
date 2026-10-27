module

public import Certificates.Certificate16036

public noncomputable section

namespace CFSG.Monster.B.E6.StdF4Radical

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Overlap CFSG.Monster.B.E6.StdF4
open CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open scoped commutatorElement

theorem isRoot_of_check {v : Fin Tag.E6.rank → ℤ}
    (h : (List.range 72).any (fun l => List.ofFn (e6Certificate.root l) == List.ofFn v) = true) :
    IsRoot Tag.E6 v := by
  simp only [List.any_eq_true, List.mem_range] at h
  obtain ⟨l, hl, he⟩ := h
  rw [← RootCertificate.eq_of_ofFn_beq (τ := Tag.E6) he]
  exact RootCertificate.isRoot_root e6Certificate_check l
    (by rw [e6Certificate_roots_length]; exact hl)

theorem not_isRoot_of_check {v : Fin Tag.E6.rank → ℤ}
    (h : (List.range 72).all (fun l => List.ofFn (e6Certificate.root l) != List.ofFn v) = true) :
    ¬IsRoot Tag.E6 v := by
  intro hv
  obtain ⟨l, hl, rfl⟩ := (RootCertificate.isRoot_iff e6Certificate_check).1 hv
  simp only [List.all_eq_true, List.mem_range, bne_iff_ne, ne_eq] at h
  exact h l (by rw [← e6Certificate_roots_length]; exact hl) rfl

@[expose] def leviGen :
    Fin 6 → ModGL Tag.E6 K :=
  ![X1 (ei 3), X1 (-ei 3), X1 (ei 2) * X1 (ei 4), X1 (-ei 2) * X1 (-ei 4),
    X1 (ei 0) * X1 (ei 5), X1 (-ei 0) * X1 (-ei 5)]

@[expose] def leviL0 :
    Subgroup (ModGL Tag.E6 K) := Subgroup.closure (Set.range leviGen)

theorem isRoot_levRoot
    {c : ℕ} (hc : c < 10) :
    IsRoot Tag.E6 (levRoot c) := by
  have h : (List.range 10).all (fun c => (List.range 72).any fun l =>
      List.ofFn (e6Certificate.root l) == List.ofFn (levRoot c)) = true :=
    Certificates.certificate16036.1
  simp only [List.all_eq_true, List.mem_range] at h
  exact isRoot_of_check (h c hc)

theorem levRoot_one {c : ℕ} (hc : c < 10) :
    levRoot c 1 = 0 := by
  have h : (List.range 10).all (fun c => levRoot c 1 == 0) = true :=
    Certificates.certificate16036.2.1
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h c hc

theorem levRoot_ne
    {c : ℕ} (hc : c < 10) {k : ℕ} (hk : k < 21) : levRoot c ≠ rr k := by
  intro h
  have := congrFun h 1
  rw [levRoot_one hc] at this
  have := rr_one_pos hk
  omega

theorem levRoot_ne_neg
    {c : ℕ} (hc : c < 10) {k : ℕ} (hk : k < 21) : levRoot c ≠ -rr k := by
  intro h
  have := congrFun h 1
  rw [levRoot_one hc, Pi.neg_apply] at this
  have := rr_one_pos hk
  omega

theorem levAddCheck :
    (List.range 10).all (fun c => (List.range 21).all fun k =>
    if levAdd c k < 21 then List.ofFn (rr (levAdd c k)) == List.ofFn (levRoot c + rr k)
    else (List.range 21).all fun l => List.ofFn (rr l) != List.ofFn (levRoot c + rr k)) = true :=
  Certificates.certificate16036.2.2.1

theorem conjW_lt {c k : ℕ} (hk : k < 21) : ∀ j ∈ conjW c k, j < 21 := by
  intro j hj
  unfold conjW at hj
  split_ifs at hj with h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    exacts [h, hk]
  · rw [List.mem_singleton.1 hj]
    exact hk

theorem conj_xr
    {c : ℕ} (hc : c < 10) {k : ℕ} (hk : k < 21) :
    X1 (levRoot c) * xr k * (X1 (levRoot c))⁻¹ = evalW (conjW c k) := by
  have h := levAddCheck
  simp only [List.all_eq_true, List.mem_range] at h
  have hck := h c hc k hk
  have hne := levRoot_ne hc hk
  have hne' := levRoot_ne_neg hc hk
  unfold conjW
  split_ifs at hck ⊢ with hl
  · have he : rr (levAdd c k) = levRoot c + rr k := RootCertificate.eq_of_ofFn_beq hck
    have hr : IsRoot Tag.E6 (levRoot c + rr k) := he ▸ isRoot_rr hl
    rw [conj_eq_commutator_mul, xr, X1_commutator (isRoot_levRoot hc) (isRoot_rr hk) hne hne' hr,
      ← he]
    simp only [evalW, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rfl
  · have hr : ¬IsRoot Tag.E6 (levRoot c + rr k) := by
      intro hr
      have h1 : 0 < (levRoot c + rr k) 1 := by
        rw [Pi.add_apply, levRoot_one hc, zero_add]
        exact rr_one_pos hk
      obtain ⟨l, hl', he⟩ := exists_rr_eq hr h1
      simp only [List.all_eq_true, List.mem_range, bne_iff_ne, ne_eq] at hck
      exact hck l hl' (by rw [he])
    rw [xr, X1_commute (isRoot_levRoot hc) (isRoot_rr hk) hne hne' hr, mul_inv_cancel_right,
      evalW_singleton]
    rfl

theorem conj_evalW
    {c : ℕ} (hc : c < 10) :
    ∀ w : List ℕ, (∀ k ∈ w, k < 21) →
      X1 (levRoot c) * evalW w * (X1 (levRoot c))⁻¹ = evalW (w.flatMap (conjW c))
  | [], _ => by simp [evalW_nil]
  | k :: w, hw => by
    have hk := hw k (List.mem_cons_self ..)
    rw [evalW_cons, List.flatMap_cons, evalW_append, ← conj_xr hc hk,
      ← conj_evalW hc w (fun j hj => hw j (List.mem_cons_of_mem _ hj))]
    group

theorem flatMap_conjW_lt (c : ℕ) {w : List ℕ} (hw : ∀ k ∈ w, k < 21) :
    ∀ j ∈ w.flatMap (conjW c), j < 21 := by
  intro j hj
  obtain ⟨k, hk, hj⟩ := List.mem_flatMap.1 hj
  exact conjW_lt (hw k hk) j hj

theorem leviGen_eq
    (k : Fin 6) : leviGen k =
    match (k : ℕ) with
    | 0 => X1 (levRoot 0)
    | 1 => X1 (levRoot 1)
    | 2 => X1 (levRoot 2) * X1 (levRoot 3)
    | 3 => X1 (levRoot 4) * X1 (levRoot 5)
    | 4 => X1 (levRoot 6) * X1 (levRoot 7)
    | _ => X1 (levRoot 8) * X1 (levRoot 9) := by
  fin_cases k <;> rfl

theorem conj_double
    {c c' : ℕ} (hc : c < 10) (hc' : c' < 10) (w : List ℕ)
    (hw : ∀ k ∈ w, k < 21) :
    X1 (levRoot c) * X1 (levRoot c') * evalW w * (X1 (levRoot c) * X1 (levRoot c'))⁻¹ =
      evalW ((w.flatMap (conjW c')).flatMap (conjW c)) := by
  rw [← conj_evalW hc _ (flatMap_conjW_lt c' hw), ← conj_evalW hc' w hw]
  group

theorem leviGen_conj_evalW
    (k : Fin 6) (w : List ℕ) (hw : ∀ j ∈ w, j < 21) :
    leviGen k * evalW w * (leviGen k)⁻¹ = evalW (leviConjW k w) := by
  rw [leviGen_eq]
  fin_cases k
  · exact conj_evalW (by norm_num) w hw
  · exact conj_evalW (by norm_num) w hw
  · exact conj_double (by norm_num) (by norm_num) w hw
  · exact conj_double (by norm_num) (by norm_num) w hw
  · exact conj_double (by norm_num) (by norm_num) w hw
  · exact conj_double (by norm_num) (by norm_num) w hw

theorem leviConjW_lt (k : ℕ) {w : List ℕ} (hw : ∀ j ∈ w, j < 21) :
    ∀ j ∈ leviConjW k w, j < 21 := by
  unfold leviConjW
  split
  · exact flatMap_conjW_lt _ hw
  · exact flatMap_conjW_lt _ hw
  all_goals exact flatMap_conjW_lt _ (flatMap_conjW_lt _ hw)

theorem headD_mem {i : ℕ} (hi : i < 15) : (orbIdx i).headD 0 ∈ orbIdx i := by
  interval_cases i <;> decide

theorem lprod_orbIdx_mem
    {u : ℕ → Bool} {i : ℕ} (hi : i < 15)
    (hu : ∀ k ∈ orbIdx i, u k = u ((orbIdx i).headD 0)) : lprod xr (orbIdx i) u ∈ radicalQ := by
  have e : lprod xr (orbIdx i) u = lprod xr (orbIdx i) fun _ => u ((orbIdx i).headD 0) :=
    lprod_congr hu
  rw [e]
  cases u ((orbIdx i).headD 0)
  · simp only [lprod, Bool.false_eq_true, ite_false]
    rw [List.prod_eq_one fun x hx => by
      obtain ⟨_, _, rfl⟩ := List.mem_map.1 hx
      rfl]
    exact one_mem _
  · simp only [lprod, ite_true]
    exact qr_mem_radicalQ hi

theorem nfM_mem_radicalQ
    {m : ℕ} (hm : inQMask m = true) : nfM m ∈ radicalQ := by
  simp only [inQMask, List.all_eq_true, List.mem_range, beq_iff_eq] at hm
  rw [nfM, ← range_flatMap_orbIdx]
  have e : ∀ L : List ℕ, (∀ i ∈ L, i < 15) →
      lprod xr (L.flatMap orbIdx) (fun i => m.testBit i) =
        (L.map fun i => lprod xr (orbIdx i) fun i => m.testBit i).prod := by
    intro L
    induction L with
    | nil => intro; rfl
    | cons i L ih =>
      intro hL
      rw [List.flatMap_cons, lprod_append, ih (fun j hj => hL j (List.mem_cons_of_mem _ hj)),
        List.map_cons, List.prod_cons]
  rw [e _ (fun i hi => List.mem_range.1 hi)]
  refine list_prod_mem fun x hx => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  exact lprod_orbIdx_mem (List.mem_range.1 hi) (hm i (List.mem_range.1 hi))

theorem leviQCheck :
    (List.range 6).all (fun k => (List.range 15).all fun i =>
    inQMask (nfWM (leviConjW k (orbIdx i)))) = true :=
  Certificates.certificate16036.2.2.2.1

theorem leviTCheck :
    (List.range 6).all (fun k => nfWM (leviConjW k [20]) == nfWM [20]) = true :=
  Certificates.certificate16036.2.2.2.2.1

@[expose] def zProdM
    (m : ℕ) : ModGL Tag.E6 K :=
  ((List.range 7).map fun j => if m.testBit j then zB j else 1).prod

theorem evalW_flatMap
    {α : Type*} (L : List α) (f : α → List ℕ) :
    evalW (L.flatMap f) = (L.map fun a => evalW (f a)).prod := by
  induction L with
  | nil => rfl
  | cons a L ih => rw [List.flatMap_cons, evalW_append, ih, List.map_cons, List.prod_cons]

theorem zProdM_eq
    (m : ℕ) : zProdM m = evalW (zWordOf m) := by
  rw [zWordOf, evalW_flatMap, zProdM]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  split_ifs
  · rfl
  · rfl

theorem zWordOf_lt (m : ℕ) : ∀ j ∈ zWordOf m, j < 21 := by
  intro j hj
  obtain ⟨i, hi, hj⟩ := List.mem_flatMap.1 hj
  split_ifs at hj
  · exact orbIdx_lt (zIdx_lt (List.mem_range.1 hi)) j hj
  · exact absurd hj (List.not_mem_nil)

theorem centerCheck :
    (List.range 6).all (fun k => (List.range 7).all fun i =>
    if hk : k < 6 then if hi : i < 7 then
      nfWM (leviConjW k (orbIdx (zIdx i))) == nfWM (zWordOf (centerCols ⟨k, hk⟩ ⟨i, hi⟩))
    else false else false) = true :=
  Certificates.certificate16036.2.2.2.2.2.1

theorem leviGen_conj_zB
    (k : Fin 6) (i : Fin 7) :
    leviGen k * zB i * (leviGen k)⁻¹ = zProdM (centerCols k i) := by
  have h := centerCheck
  simp only [List.all_eq_true, List.mem_range] at h
  have hki := h k k.2 i i.2
  simp only [k.2, i.2, dite_true, beq_iff_eq] at hki
  have hw := orbIdx_lt (zIdx_lt i.2)
  rw [zB, qr, leviGen_conj_evalW k _ hw, zProdM_eq]
  exact evalW_eq_of_nfWM_eq (leviConjW_lt _ hw) (zWordOf_lt _) hki

theorem levPairCheck :
    (List.range 4).all (fun p =>
    let a := levRoot (2 * p + 2); let b := levRoot (2 * p + 3)
    (List.range 72).all (fun l => List.ofFn (e6Certificate.root l) != List.ofFn (a + b)) &&
      List.ofFn a != List.ofFn b && List.ofFn a != List.ofFn (-b)) = true :=
  Certificates.certificate16036.2.2.2.2.2.2.1

theorem levRoot_comm
    {p : ℕ} (hp : p < 4) :
    X1 (levRoot (2 * p + 2)) * X1 (levRoot (2 * p + 3)) =
      X1 (levRoot (2 * p + 3)) * X1 (levRoot (2 * p + 2)) := by
  have h := levPairCheck
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h p hp
  refine X1_commute (isRoot_levRoot (by omega)) (isRoot_levRoot (by omega))
    (fun e => h2 (by rw [e])) (fun e => h3 (by rw [e])) (not_isRoot_of_check ?_)
  simpa [List.all_eq_true, bne_iff_ne] using h1

theorem mul_self_of_comm
    {a b : Fin Tag.E6.rank → ℤ} (h : X1 a * X1 b = X1 b * X1 a) :
    X1 a * X1 b * (X1 a * X1 b) = 1 := by
  calc X1 a * X1 b * (X1 a * X1 b) = X1 a * (X1 b * X1 a) * X1 b := by group
    _ = X1 a * (X1 a * X1 b) * X1 b := by rw [h]
    _ = 1 := by rw [← mul_assoc, X1_mul_self, one_mul, X1_mul_self]

theorem leviGen_mul_self
    (k : Fin 6) : leviGen k * leviGen k = 1 := by
  rw [leviGen_eq]
  fin_cases k
  · exact X1_mul_self _
  · exact X1_mul_self _
  · exact mul_self_of_comm (levRoot_comm (p := 0) (by norm_num))
  · exact mul_self_of_comm (levRoot_comm (p := 1) (by norm_num))
  · exact mul_self_of_comm (levRoot_comm (p := 2) (by norm_num))
  · exact mul_self_of_comm (levRoot_comm (p := 3) (by norm_num))

theorem leviGen_inv
    (k : Fin 6) : (leviGen k)⁻¹ = leviGen k :=
  inv_eq_of_mul_eq_one_left (leviGen_mul_self k)

theorem levRhoCheck :
    (List.range 10).all (fun c =>
    List.ofFn (rho (levRoot c)) == List.ofFn (levRoot ([0, 1, 3, 2, 5, 4, 7, 6, 9, 8].getD c 0)))
    = true :=
  Certificates.certificate16036.2.2.2.2.2.2.2.1

theorem rho_levRoot {c : ℕ} (hc : c < 10) :
    rho (levRoot c) = levRoot ([0, 1, 3, 2, 5, 4, 7, 6, 9, 8].getD c 0) := by
  have h := levRhoCheck
  simp only [List.all_eq_true, List.mem_range] at h
  exact RootCertificate.eq_of_ofFn_beq (h c hc)

theorem height_levRoot_pos :
    [0, 2, 3, 6, 7].all (fun c => decide (0 < height (levRoot c))) =
    true :=
  Certificates.certificate16036.2.2.2.2.2.2.2.2.1

theorem height_levRoot_neg :
    [1, 4, 5, 8, 9].all (fun c => decide (height (levRoot c) < 0)) =
    true :=
  Certificates.certificate16036.2.2.2.2.2.2.2.2.2

theorem single_mem_groupJ
    {a : Fin Tag.E6.rank → ℤ} (ha : IsRoot Tag.E6 a)
    (hpos : 0 < height a ∨ height a < 0) (hr : rho a = a) : X1 a ∈ groupJ := by
  refine mem_groupJ_of_twistHom ?_ (pinnedX_mem_adjointGroup _ _) ?_ (betaGL_X1 a)
  · rcases hpos with h | h
    exacts [Or.inl (X1_mem_posUnipotent ha h), Or.inr (X1_mem_negUnipotent ha h)]
  · rw [twistHom_X1 ha]
    exact congrArg X1 hr

theorem pair_mem_groupJ
    {a b : Fin Tag.E6.rank → ℤ} (ha : IsRoot Tag.E6 a) (hb : IsRoot Tag.E6 b)
    (hpos : (0 < height a ∧ 0 < height b) ∨ (height a < 0 ∧ height b < 0)) (hra : rho a = b)
    (hrb : rho b = a) (hc : X1 a * X1 b = X1 b * X1 a) : X1 a * X1 b ∈ groupJ := by
  refine mem_groupJ_of_twistHom ?_ (mul_mem (pinnedX_mem_adjointGroup _ _)
    (pinnedX_mem_adjointGroup _ _)) ?_ (by rw [map_mul, betaGL_X1, betaGL_X1])
  · rcases hpos with ⟨h, h'⟩ | ⟨h, h'⟩
    · exact Or.inl (mul_mem (X1_mem_posUnipotent ha h) (X1_mem_posUnipotent hb h'))
    · exact Or.inr (mul_mem (X1_mem_negUnipotent ha h) (X1_mem_negUnipotent hb h'))
  · rw [map_mul, twistHom_X1 ha, twistHom_X1 hb, ← rho, ← rho, hra, hrb, hc]

theorem levRoot_pos
    {c : ℕ} (hc : c ∈ [0, 2, 3, 6, 7]) : 0 < height (levRoot c) := by
  have h := height_levRoot_pos
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact h c hc

theorem levRoot_neg
    {c : ℕ} (hc : c ∈ [1, 4, 5, 8, 9]) : height (levRoot c) < 0 := by
  have h := height_levRoot_neg
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact h c hc

theorem leviGen_mem_groupJ
    (k : Fin 6) : leviGen k ∈ groupJ := by
  rw [leviGen_eq]
  fin_cases k
  · exact single_mem_groupJ (isRoot_levRoot (by norm_num)) (Or.inl (levRoot_pos (by decide)))
      (rho_levRoot (c := 0) (by norm_num))
  · exact single_mem_groupJ (isRoot_levRoot (by norm_num)) (Or.inr (levRoot_neg (by decide)))
      (rho_levRoot (c := 1) (by norm_num))
  · exact pair_mem_groupJ (isRoot_levRoot (by norm_num)) (isRoot_levRoot (by norm_num))
      (Or.inl ⟨levRoot_pos (by decide), levRoot_pos (by decide)⟩)
      (rho_levRoot (c := 2) (by norm_num)) (rho_levRoot (c := 3) (by norm_num))
      (levRoot_comm (p := 0) (by norm_num))
  · exact pair_mem_groupJ (isRoot_levRoot (by norm_num)) (isRoot_levRoot (by norm_num))
      (Or.inr ⟨levRoot_neg (by decide), levRoot_neg (by decide)⟩)
      (rho_levRoot (c := 4) (by norm_num)) (rho_levRoot (c := 5) (by norm_num))
      (levRoot_comm (p := 1) (by norm_num))
  · exact pair_mem_groupJ (isRoot_levRoot (by norm_num)) (isRoot_levRoot (by norm_num))
      (Or.inl ⟨levRoot_pos (by decide), levRoot_pos (by decide)⟩)
      (rho_levRoot (c := 6) (by norm_num)) (rho_levRoot (c := 7) (by norm_num))
      (levRoot_comm (p := 2) (by norm_num))
  · exact pair_mem_groupJ (isRoot_levRoot (by norm_num)) (isRoot_levRoot (by norm_num))
      (Or.inr ⟨levRoot_neg (by decide), levRoot_neg (by decide)⟩)
      (rho_levRoot (c := 8) (by norm_num)) (rho_levRoot (c := 9) (by norm_num))
      (levRoot_comm (p := 3) (by norm_num))

theorem leviL0_le_groupJ :
    leviL0 ≤ groupJ := by
  rw [leviL0, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  exact leviGen_mem_groupJ k

theorem leviGen_conj_qr
    (k : Fin 6) {i : ℕ} (hi : i < 15) :
    leviGen k * qr i * (leviGen k)⁻¹ ∈ radicalQ := by
  have h := leviQCheck
  simp only [List.all_eq_true, List.mem_range] at h
  have hw := orbIdx_lt hi
  rw [qr, leviGen_conj_evalW k _ hw, evalW_eq_nfM _ (leviConjW_lt _ hw)]
  exact nfM_mem_radicalQ (h k k.2 i hi)

theorem mem_normalizer_radicalQ
    {g : ModGL Tag.E6 K} (hg : g⁻¹ = g)
    (h : ∀ i < 15, g * qr i * g⁻¹ ∈ radicalQ) :
    g ∈ Subgroup.normalizer (radicalQ : Set (ModGL Tag.E6 K)) := by
  have hmap : ∀ x ∈ radicalQ, g * x * g⁻¹ ∈ radicalQ := by
    intro x hx
    rw [radicalQ_eq_closure] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      exact h i hi
    | one => simp
    | mul x y _ _ ihx ihy =>
      have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [e]
      exact mul_mem ihx ihy
    | inv x _ ihx =>
      have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem ihx
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hmap x, fun hx => ?_⟩
  have := hmap _ hx
  rwa [show g * (g * x * g⁻¹) * g⁻¹ = x by
    calc g * (g * x * g⁻¹) * g⁻¹ = g⁻¹ * (g * x * g⁻¹) * g := by rw [hg]
      _ = x := by group] at this

theorem leviL0_le_normalizer_radicalQ :
    leviL0 ≤ Subgroup.normalizer (radicalQ : Set (ModGL Tag.E6 K)) := by
  rw [leviL0, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  exact mem_normalizer_radicalQ (leviGen_inv k) fun i hi => leviGen_conj_qr k hi

theorem normalizer_radicalQ_le_normalizer_radicalZ :
    Subgroup.normalizer (radicalQ : Set (ModGL Tag.E6 K)) ≤
      Subgroup.normalizer (radicalZ : Set (ModGL Tag.E6 K)) := by
  intro g hg
  have hg' : g⁻¹ ∈ Subgroup.normalizer (radicalQ : Set (ModGL Tag.E6 K)) := inv_mem hg
  have key : ∀ x ∈ Subgroup.normalizer (radicalQ : Set (ModGL Tag.E6 K)), ∀ z ∈ radicalZ,
      x * z * x⁻¹ ∈ radicalZ := by
    intro x hx z hz
    have hx' : x⁻¹ ∈ Subgroup.normalizer (radicalQ : Set (ModGL Tag.E6 K)) := inv_mem hx
    obtain ⟨hzQ, hzc⟩ := mem_radicalZ_iff'.1 hz
    refine mem_radicalZ_iff'.2 ⟨(Subgroup.mem_normalizer_iff.1 hx z).1 hzQ, fun h hh => ?_⟩
    have h1 : x⁻¹ * h * x⁻¹⁻¹ ∈ radicalQ := (Subgroup.mem_normalizer_iff.1 hx' h).1 hh
    have h2 := hzc _ h1
    rw [inv_inv] at h2
    calc h * (x * z * x⁻¹) = x * ((x⁻¹ * h * x) * z) * x⁻¹ := by group
      _ = x * (z * (x⁻¹ * h * x)) * x⁻¹ := by rw [h2]
      _ = x * z * x⁻¹ * h := by group
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨key g hg z, fun hz => ?_⟩
  have := key g⁻¹ hg' _ hz
  rwa [show g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z by group] at this

theorem leviL0_le_normalizer_radicalZ :
    leviL0 ≤ Subgroup.normalizer (radicalZ : Set (ModGL Tag.E6 K)) :=
  leviL0_le_normalizer_radicalQ.trans normalizer_radicalQ_le_normalizer_radicalZ

theorem leviGen_comm_rootInvM
    (k : Fin 6) : leviGen k * rootInvM = rootInvM * leviGen k := by
  have h := leviTCheck
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have hw : ∀ j ∈ [20], j < 21 := by simp
  have e := leviGen_conj_evalW k [20] hw
  rw [evalW_eq_of_nfWM_eq (leviConjW_lt _ hw) hw (h k k.2), evalW_singleton, xr_twenty] at e
  calc leviGen k * rootInvM = (leviGen k * rootInvM * (leviGen k)⁻¹) * leviGen k := by group
    _ = rootInvM * leviGen k := by rw [e]

theorem leviL0_le_centralizer :
    leviL0 ≤ Subgroup.centralizer {rootInvM} := by
  rw [leviL0, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  exact Subgroup.mem_centralizer_singleton_iff.2 (leviGen_comm_rootInvM k)

end CFSG.Monster.B.E6.StdF4Radical
