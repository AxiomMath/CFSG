module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonTwoTransvections

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix Subgroup CFSG.Assembly.LowTwoRank

section TwoByTwo

variable {K : Type*} [Field K]

theorem mul_self_fin_two (M : Matrix (Fin 2) (Fin 2) K) :
    M * M = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

theorem mul_self_eq_zero_of_pow_eq_zero {M : Matrix (Fin 2) (Fin 2) K} {k : ℕ}
    (hk : M ^ k = 0) : M * M = 0 := by
  rcases k with _ | k
  · rw [pow_zero] at hk
    have h := congrFun (congrFun hk 0) 0
    simp at h
  have hdet : M.det = 0 := by
    have h := congrArg Matrix.det hk
    rw [Matrix.det_pow, Matrix.det_zero] at h
    exact pow_eq_zero_iff (Nat.succ_ne_zero k) |>.mp h
  have hsq : M * M = M.trace • M := by
    rw [mul_self_fin_two, hdet, zero_smul, sub_zero]
  have hpow : ∀ j : ℕ, M ^ (j + 1) = M.trace ^ j • M := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, ih, smul_mul_assoc, hsq, smul_smul, ← pow_succ]
  rw [hpow k] at hk
  rcases smul_eq_zero.mp hk with h | h
  · rcases k with _ | k
    · simp at h
    · rw [hsq, (pow_eq_zero_iff (Nat.succ_ne_zero k)).mp h, zero_smul]
  · rw [h, zero_mul]

end TwoByTwo

section GLTwo

variable {p : ℕ} [Fact p.Prime]

theorem mem_statedSL_iff {n : ℕ} {L : Type} [Field L] (A : GL (Fin n) L) :
    A ∈ StatedSL n L ↔ (A : Matrix (Fin n) (Fin n) L).det = 1 :=
  CFSG.Open.StatedAPI.mem_statedSL_iff

instance statedSL_normal (n : ℕ) (L : Type) [Field L] : (StatedSL n L).Normal := by
  constructor
  intro A hA g
  rw [mem_statedSL_iff] at hA ⊢
  simp only [Units.val_mul, Matrix.det_mul, hA, mul_one]
  rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]

theorem sub_one_mul_self_eq_zero (u : GL (Fin 2) (ZMod p)) (hu : u ^ p = 1) :
    ((u : Matrix (Fin 2) (Fin 2) (ZMod p)) - 1) * ((u : Matrix (Fin 2) (Fin 2) (ZMod p)) - 1) =
      0 := by
  apply mul_self_eq_zero_of_pow_eq_zero (k := p)
  rw [sub_pow_char_of_commute p (Commute.one_right _), one_pow, ← Units.val_pow_eq_pow_val, hu,
    Units.val_one, sub_self]

theorem det_eq_one_of_pow_eq_one (u : GL (Fin 2) (ZMod p)) (hu : u ^ p = 1) :
    (u : Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1 := by
  have h := congrArg (fun g : GL (Fin 2) (ZMod p) => (g : Matrix (Fin 2) (Fin 2) (ZMod p)).det) hu
  simp only [Units.val_pow_eq_pow_val, Matrix.det_pow, Units.val_one, Matrix.det_one,
    ZMod.pow_card] at h
  exact h

theorem entries_of_sub_one_mul_self {U : Matrix (Fin 2) (Fin 2) (ZMod p)}
    (h : (U - 1) * (U - 1) = 0) :
    (U 0 0 - 1) * (U 0 0 - 1) + U 0 1 * U 1 0 = 0 ∧
      (U 0 0 - 1) * U 0 1 + U 0 1 * (U 1 1 - 1) = 0 ∧
      U 1 0 * (U 0 0 - 1) + (U 1 1 - 1) * U 1 0 = 0 ∧
      U 1 0 * U 0 1 + (U 1 1 - 1) * (U 1 1 - 1) = 0 := by
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  have h11 := congrFun (congrFun h 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.one_apply] at h00 h01 h10 h11
  exact ⟨by linear_combination h00, by linear_combination h01, by linear_combination h10,
    by linear_combination h11⟩

end GLTwo

section NormalForms

variable {p : ℕ} [Fact p.Prime]

theorem exists_conj_transvection (u : GL (Fin 2) (ZMod p)) (hu : u ^ p = 1) (hu1 : u ≠ 1) :
    ∃ g : GL (Fin 2) (ZMod p), (u : Matrix (Fin 2) (Fin 2) (ZMod p)) *
      (g : Matrix (Fin 2) (Fin 2) (ZMod p)) =
        (g : Matrix (Fin 2) (Fin 2) (ZMod p)) * !![1, 1; 0, 1] := by
  obtain ⟨e00, e01, e10, e11⟩ := entries_of_sub_one_mul_self (sub_one_mul_self_eq_zero u hu)
  set U := (u : Matrix (Fin 2) (Fin 2) (ZMod p)) with hU
  by_cases hc : U 1 0 = 0
  · have ha : U 0 0 = 1 := by
      rw [hc, mul_zero, add_zero] at e00
      linear_combination mul_self_eq_zero.mp e00
    have hd : U 1 1 = 1 := by
      rw [hc, zero_mul, zero_add] at e11
      linear_combination mul_self_eq_zero.mp e11
    have hb : U 0 1 ≠ 0 := by
      intro hb
      apply hu1
      apply Units.ext
      rw [Units.val_one, ← hU]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![U 0 1, 0; 0, 1]
      (by rw [Matrix.det_fin_two_of]; exact fun h => hb (by linear_combination h)), ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two, ha, hc,
        hd]
  · refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![U 0 0 - 1, 1; U 1 0, 0]
      (by rw [Matrix.det_fin_two_of]; exact fun h => hc (by linear_combination -h)), ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination e00
    · linear_combination e10

theorem exists_conj_pair (w : GL (Fin 2) (ZMod p)) (hw : w ^ p = 1)
    (hX : ∀ n : ℕ, (w : Matrix (Fin 2) (Fin 2) (ZMod p)) ≠ !![1, (n : ZMod p); 0, 1]) :
    ∃ (k : GL (Fin 2) (ZMod p)) (c : ZMod p), c ≠ 0 ∧
      (k : Matrix (Fin 2) (Fin 2) (ZMod p)) * !![1, 1; 0, 1] =
        !![1, c; 0, 1] * (k : Matrix (Fin 2) (Fin 2) (ZMod p)) ∧
      (k : Matrix (Fin 2) (Fin 2) (ZMod p)) * (w : Matrix (Fin 2) (Fin 2) (ZMod p)) =
        !![1, 0; 1, 1] * (k : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
  obtain ⟨e00, e01, e10, e11⟩ := entries_of_sub_one_mul_self (sub_one_mul_self_eq_zero w hw)
  set W := (w : Matrix (Fin 2) (Fin 2) (ZMod p)) with hW
  have hc : W 1 0 ≠ 0 := by
    intro hc
    have ha : W 0 0 = 1 := by
      rw [hc, mul_zero, add_zero] at e00
      linear_combination mul_self_eq_zero.mp e00
    have hd : W 1 1 = 1 := by
      rw [hc, zero_mul, zero_add] at e11
      linear_combination mul_self_eq_zero.mp e11
    apply hX (W 0 1).val
    rw [ZMod.natCast_zmod_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hc, hd]
  have hd : W 1 1 = 2 - W 0 0 := by
    have h : W 1 0 * (W 0 0 + W 1 1 - 2) = 0 := by linear_combination e10
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hc
    · linear_combination h
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![W 1 0, 1 - W 0 0; 0, 1]
    (by rw [Matrix.det_fin_two_of]; exact fun h => hc (by linear_combination h)), W 1 0, hc, ?_,
    ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals first
      | ring1
      | linear_combination hd
      | linear_combination e00 + (1 - W 0 0) * hd

end NormalForms

section Generation

variable {p : ℕ} [Fact p.Prime]

@[expose] def upperGL (r : ZMod p) : GL (Fin 2) (ZMod p) :=
  SpecialLinearGroup.toGL ⟨!![1, r; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def lowerGL : GL (Fin 2) (ZMod p) :=
  SpecialLinearGroup.toGL ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩

theorem coe_upperGL (r : ZMod p) :
    (upperGL r : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, r; 0, 1] := rfl

theorem coe_lowerGL :
    ((lowerGL : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 0; 1, 1] := rfl

theorem upperGL_one_pow (n : ℕ) : upperGL (1 : ZMod p) ^ n = upperGL (n : ZMod p) := by
  induction n with
  | zero =>
    apply Units.ext
    rw [pow_zero, Units.val_one, coe_upperGL, Nat.cast_zero]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  | succ n ih =>
    apply Units.ext
    rw [pow_succ, Units.val_mul, ih, coe_upperGL, coe_upperGL, coe_upperGL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem closure_upperGL_lowerGL (r : ZMod p) (hr : r ≠ 0) :
    Subgroup.closure {upperGL r, lowerGL} = StatedSL 2 (ZMod p) := by
  set X : SpecialLinearGroup (Fin 2) (ZMod p) := ⟨!![1, r; 0, 1], by simp [Matrix.det_fin_two]⟩
    with hXdef
  set Y : SpecialLinearGroup (Fin 2) (ZMod p) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
    with hYdef
  have h : Subgroup.closure ({X, Y} : Set (SpecialLinearGroup (Fin 2) (ZMod p))) = ⊤ :=
    CFSG.Glauberman.Dickson.standard_two_transvections_generate_of_finrank_one
      (p := p) (K := ZMod p) r hr (Module.finrank_self (ZMod p))
  have hX : upperGL r = SpecialLinearGroup.toGL X := rfl
  have hY : (lowerGL : GL (Fin 2) (ZMod p)) = SpecialLinearGroup.toGL Y := rfl
  rw [hX, hY, ← Set.image_pair, ← MonoidHom.map_closure, h, ← MonoidHom.range_eq_map,
    statedSL_eq_range_toGL]

theorem map_conj_of_normal {G : Type*} [Group G] {N : Subgroup G} (hN : N.Normal) (g : G) :
    N.map (MulAut.conj g).toMonoidHom = N := by
  apply le_antisymm
  · rintro _ ⟨n, hn, rfl⟩
    exact hN.conj_mem n hn g
  · intro n hn
    refine ⟨g⁻¹ * n * g, ?_, ?_⟩
    · simpa using hN.conj_mem n hn g⁻¹
    · simp [mul_assoc]

theorem closure_pair_eq_statedSL (u w : GL (Fin 2) (ZMod p)) (hu : u ^ p = 1) (hu1 : u ≠ 1)
    (hw : w ^ p = 1) (huw : w ∉ zpowers u) :
    Subgroup.closure {u, w} = StatedSL 2 (ZMod p) := by
  obtain ⟨g, hg⟩ := exists_conj_transvection u hu hu1
  have hgu : g⁻¹ * u * g = upperGL 1 := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Matrix.mul_assoc, hg, ← Matrix.mul_assoc, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mul, coe_upperGL]
  set w₁ := g⁻¹ * w * g with hw₁def
  have hw₁ : w₁ ^ p = 1 := by
    have h := map_pow (MulAut.conj g⁻¹) w p
    rw [hw, map_one] at h
    rw [hw₁def, show g⁻¹ * w * g = MulAut.conj g⁻¹ w by simp]
    exact h.symm
  have hX : ∀ n : ℕ, (w₁ : Matrix (Fin 2) (Fin 2) (ZMod p)) ≠ !![1, (n : ZMod p); 0, 1] := by
    intro n hn
    apply huw
    have hw₁n : w₁ = upperGL 1 ^ n := by
      rw [upperGL_one_pow]
      exact Units.ext hn
    have hw' : w = u ^ n := by
      have h1 : w = g * w₁ * g⁻¹ := by rw [hw₁def]; group
      have h2 : u = g * upperGL 1 * g⁻¹ := by rw [← hgu]; group
      rw [h1, hw₁n, h2, conj_pow]
    rw [hw']
    exact pow_mem (mem_zpowers u) n
  obtain ⟨k, c, hc, hk1, hk2⟩ := exists_conj_pair w₁ hw₁ hX
  have hku : (k * g⁻¹) * u * (k * g⁻¹)⁻¹ = upperGL c := by
    have h : k * upperGL 1 = upperGL c * k := by
      apply Units.ext
      change (k : Matrix (Fin 2) (Fin 2) (ZMod p)) *
          ((upperGL 1 : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) =
        ((upperGL c : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) *
          (k : Matrix (Fin 2) (Fin 2) (ZMod p))
      rw [coe_upperGL, coe_upperGL]
      exact hk1
    calc (k * g⁻¹) * u * (k * g⁻¹)⁻¹ = k * (g⁻¹ * u * g) * k⁻¹ := by group
      _ = upperGL c := by rw [hgu, h, mul_inv_cancel_right]
  have hkw : (k * g⁻¹) * w * (k * g⁻¹)⁻¹ = lowerGL := by
    have h : k * w₁ = lowerGL * k := by
      apply Units.ext
      change (k : Matrix (Fin 2) (Fin 2) (ZMod p)) * (w₁ : Matrix (Fin 2) (Fin 2) (ZMod p)) =
        ((lowerGL : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) *
          (k : Matrix (Fin 2) (Fin 2) (ZMod p))
      rw [coe_lowerGL]
      exact hk2
    calc (k * g⁻¹) * w * (k * g⁻¹)⁻¹ = k * w₁ * k⁻¹ := by rw [hw₁def]; group
      _ = lowerGL := by rw [h, mul_inv_cancel_right]
  apply Subgroup.map_injective (f := (MulAut.conj (k * g⁻¹)).toMonoidHom)
    (MulAut.conj (k * g⁻¹)).injective
  rw [map_conj_of_normal (statedSL_normal 2 (ZMod p)), MonoidHom.map_closure, Set.image_pair]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [hku, hkw, closure_upperGL_lowerGL c hc]

end Generation

section Dickson

variable {p : ℕ} [Fact p.Prime]

theorem not_sq_dvd_card_GL_two : ¬ p ^ 2 ∣ Nat.card (GL (Fin 2) (ZMod p)) := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_le
  have hcard : Nat.card (GL (Fin 2) (ZMod p)) = p * ((p - 1) * ((p + 1) * (p - 1))) := by
    rw [Matrix.card_GL_field, Fin.prod_univ_two, ZMod.card]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    rw [show p ^ 2 - 1 = (p + 1) * (p - 1) by rw [← Nat.sq_sub_sq, one_pow],
      show p ^ 2 - p = p * (p - 1) by rw [Nat.mul_sub_one, sq]]
    ring
  have hcop1 : Nat.Coprime p (p - 1) :=
    (Nat.coprime_self_sub_right hp1).mpr (Nat.coprime_one_right p)
  have hcop2 : Nat.Coprime p (p + 1) := Nat.coprime_self_add_right.mpr (Nat.coprime_one_right p)
  have hcop : Nat.Coprime p ((p - 1) * ((p + 1) * (p - 1))) :=
    Nat.Coprime.mul_right hcop1 (Nat.Coprime.mul_right hcop2 hcop1)
  rw [hcard, sq]
  intro h
  have h' := Nat.dvd_of_mul_dvd_mul_left (Fact.out : p.Prime).pos h
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop h')

theorem exists_zpowers_eq_of_card_eq {G : Type*} [Group G] {K : Subgroup G}
    (hK : Nat.card K = p) : ∃ x ∈ K, x ^ p = 1 ∧ x ≠ 1 ∧ zpowers x = K := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (Fact.out : p.Prime).ne_zero)
  have hne : K ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot K).mp
    (by rw [hK]; exact (Fact.out : p.Prime).one_lt)
  obtain ⟨⟨x, hxK⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hord : orderOf x = p := by
    have hdvd : orderOf x ∣ p := by
      rw [← hK, ← Subgroup.orderOf_mk x hxK]
      exact orderOf_dvd_natCard _
    rcases (Nat.dvd_prime Fact.out).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1'
    · exact h
  refine ⟨x, hxK, by rw [← hord]; exact pow_orderOf_eq_one x, hx1', ?_⟩
  apply Subgroup.eq_of_le_of_card_ge ((zpowers_le).mpr hxK)
  rw [Nat.card_zpowers, hord, hK]

theorem dickson_gl_two (H : Subgroup (GL (Fin 2) (ZMod p))) (hpH : p ∣ Nat.card H) :
    (∃ P : Sylow p H, (P : Subgroup H).Normal ∧ Nat.card P = p) ∨
      StatedSL 2 (ZMod p) ≤ H := by
  classical
  have hsyl : ∀ P : Sylow p H, Nat.card P = p := by
    intro P
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
    have hne := P.ne_bot_of_dvd_card hpH
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact hne (Subgroup.card_eq_one.mp hk)
    have hdvd : p ^ k ∣ Nat.card (GL (Fin 2) (ZMod p)) := by
      rw [← hk]
      exact (Subgroup.card_subgroup_dvd_card _).trans (Subgroup.card_subgroup_dvd_card H)
    have hk1 : k ≤ 1 := by
      by_contra h
      exact not_sq_dvd_card_GL_two ((pow_dvd_pow p (by omega)).trans hdvd)
    rw [hk, show k = 1 by omega, pow_one]
  obtain P : Sylow p H := default
  by_cases hPn : (P : Subgroup H).Normal
  · exact Or.inl ⟨P, hPn, hsyl P⟩
  right
  obtain ⟨Q, hQP⟩ : ∃ Q : Sylow p H, Q ≠ P := by
    by_contra hall
    push Not at hall
    have : Subsingleton (Sylow p H) := ⟨fun a b => (hall a).trans (hall b).symm⟩
    exact hPn (Sylow.normal_of_subsingleton P)
  set P' := (P : Subgroup H).map H.subtype with hP'
  set Q' := (Q : Subgroup H).map H.subtype with hQ'
  have hP'card : Nat.card P' = p := by
    rw [hP', Subgroup.card_map_of_injective H.subtype_injective, hsyl P]
  have hQ'card : Nat.card Q' = p := by
    rw [hQ', Subgroup.card_map_of_injective H.subtype_injective, hsyl Q]
  obtain ⟨u, huP, hu, hu1, hzu⟩ := exists_zpowers_eq_of_card_eq hP'card
  obtain ⟨w, hwQ, hw, -, hzw⟩ := exists_zpowers_eq_of_card_eq hQ'card
  have huw : w ∉ zpowers u := by
    intro h
    rw [hzu] at h
    have hle : Q' ≤ P' := by
      rw [← hzw]
      exact (zpowers_le).mpr h
    have : Finite P' := Nat.finite_of_card_ne_zero
      (by rw [hP'card]; exact (Fact.out : p.Prime).ne_zero)
    have heq : Q' = P' := Subgroup.eq_of_le_of_card_ge hle (by rw [hP'card, hQ'card])
    exact hQP (Sylow.ext (Subgroup.map_injective H.subtype_injective heq))
  rw [← closure_pair_eq_statedSL u w hu hu1 hw huw, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact Subgroup.map_subtype_le _ huP
  · exact Subgroup.map_subtype_le _ hwQ

theorem dickson_gl_two_closure (S : Set (GL (Fin 2) (ZMod p))) (hS : ∀ g ∈ S, orderOf g = p) :
    Subgroup.closure S = ⊥ ∨ Nat.card (Subgroup.closure S) = p ∨
      Subgroup.closure S = StatedSL 2 (ZMod p) := by
  classical
  set H := Subgroup.closure S with hH
  rcases S.eq_empty_or_nonempty with hS0 | ⟨s, hs⟩
  · left
    rw [hH, hS0, Subgroup.closure_empty]
  right
  have hpH : p ∣ Nat.card H := by
    have h := Subgroup.orderOf_dvd_natCard H (Subgroup.subset_closure hs)
    rwa [hS s hs] at h
  rcases dickson_gl_two H hpH with ⟨P, hPn, hPcard⟩ | hSL
  · left
    have : Subsingleton (Sylow p H) := by
      have := Sylow.unique_of_normal P hPn
      infer_instance
    have hle : H ≤ (P : Subgroup H).map H.subtype := by
      refine (Subgroup.closure_le _).mpr ?_
      intro t ht
      have htH : t ∈ H := Subgroup.subset_closure ht
      have hpt : IsPGroup p (zpowers (⟨t, htH⟩ : H)) := IsPGroup.of_card (n := 1)
        (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hS t ht, pow_one])
      obtain ⟨R, hR⟩ := hpt.exists_le_sylow
      rw [Subsingleton.elim R P] at hR
      exact ⟨⟨t, htH⟩, hR (mem_zpowers _), rfl⟩
    have heq : H = (P : Subgroup H).map H.subtype :=
      le_antisymm hle (Subgroup.map_subtype_le _)
    rw [heq, Subgroup.card_map_of_injective H.subtype_injective, hPcard]
  · right
    refine le_antisymm ?_ hSL
    refine (Subgroup.closure_le _).mpr ?_
    intro t ht
    rw [SetLike.mem_coe, mem_statedSL_iff]
    have h := pow_orderOf_eq_one t
    rw [hS t ht] at h
    exact det_eq_one_of_pow_eq_one t h

end Dickson

end CFSG.RankThree.SubgroupLists
