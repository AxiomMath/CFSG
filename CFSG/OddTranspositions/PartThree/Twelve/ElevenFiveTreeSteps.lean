module

public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveForm
public import CFSG.OddTranspositions.PartThree.Eleven.Five.FiveFormAux
public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveTreeExtension
public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveTreeBase

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix

@[expose] def IsFiveTree (k : ℕ) (ε π : Bool) (W : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5))
    {d : ℕ} (b : Fin d → Fin (k + 1) → ZMod 5) (p : Fin d → Fin d) : Prop :=
  (∀ i, b i ∈ W ∧ fiveForm k ε (b i) (b i) ≠ 0 ∧
    (IsSquare (fiveForm k ε (b i) (b i)) ↔ π = true)) ∧
  LinearIndependent (ZMod 5) b ∧
  (∀ i : Fin d, (i : ℕ) ≠ 0 → (p i : ℕ) < (i : ℕ) ∧ fiveForm k ε (b i) (b (p i)) ≠ 0) ∧
  (∀ i j : Fin d, fiveForm k ε (b i) (b j) ≠ 0 →
    i = j ∨ ((i : ℕ) ≠ 0 ∧ j = p i) ∨ ((j : ℕ) ≠ 0 ∧ i = p j))

@[expose] def IsFiveAnchor (k : ℕ) (ε : Bool) (W : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5))
    {d : ℕ} (b : Fin d → Fin (k + 1) → ZMod 5) (j : Fin d) : Prop :=
  ∃ c ∈ W, (∀ i, fiveForm k ε c (b i) = if i = j then 1 else 0) ∧
    ¬ IsSquare (fiveForm k ε c c * fiveForm k ε (b j) (b j))

private lemma exists_alpha_factor : ∀ t q : ZMod 5, ¬ IsSquare t → q ≠ 0 →
    ∃ α : ZMod 5, (α = 1 ∨ α = 2) ∧
      (1 - α ^ 2 * t = 3 ∨ 1 - α ^ 2 * t = 4) ∧ IsSquare (q * (1 - α ^ 2 * t)) := by
  decide

private lemma zmod5_div_four_nonsquare (t : ZMod 5) (ht : ¬ IsSquare t) :
    ¬ IsSquare (t / 4) := by
  have h4 : (4 : ZMod 5)⁻¹ = 4 :=
    inv_eq_of_mul_eq_one_right (by decide : (4 : ZMod 5) * 4 = 1)
  rw [div_eq_mul_inv, h4]
  revert t
  decide

private lemma zmod5_inv_three_nonsquare : ¬ IsSquare ((3 : ZMod 5)⁻¹) := by
  have h : (3 : ZMod 5)⁻¹ = 2 :=
    inv_eq_of_mul_eq_one_right (by decide : (3 : ZMod 5) * 2 = 1)
  rw [h]
  decide

private lemma fiveForm_add_smul_self (k : ℕ) (ε : Bool) (a b : ZMod 5)
    (x y : Fin (k + 1) → ZMod 5) :
    fiveForm k ε (a • x + b • y) (a • x + b • y) =
      a ^ 2 * fiveForm k ε x x + 2 * a * b * fiveForm k ε x y +
        b ^ 2 * fiveForm k ε y y := by
  rw [fiveForm_add_left, fiveForm_add_right, fiveForm_add_right,
    fiveForm_smul_smul, fiveForm_smul_smul, fiveForm_smul_smul, fiveForm_smul_smul,
    fiveForm_comm k ε y x]
  ring

private lemma fiveForm_add_smul_left (k : ℕ) (ε : Bool) (a b : ZMod 5)
    (x y z : Fin (k + 1) → ZMod 5) :
    fiveForm k ε (a • x + b • y) z = a * fiveForm k ε x z + b * fiveForm k ε y z := by
  rw [fiveForm_add_left, fiveForm_smul_left, fiveForm_smul_left]

private lemma fiveForm_sub_smul_self (k : ℕ) (ε : Bool) (c : ZMod 5)
    (x y : Fin (k + 1) → ZMod 5) :
    fiveForm k ε (x - c • y) (x - c • y) =
      fiveForm k ε x x - 2 * c * fiveForm k ε x y + c ^ 2 * fiveForm k ε y y := by
  rw [fiveForm_sub_left, fiveForm_sub_right, fiveForm_sub_right, fiveForm_smul_smul,
    fiveForm_smul_right, fiveForm_smul_left, fiveForm_comm k ε y x]
  ring

private lemma anchor_old_norm (Bcc qb α f : ZMod 5) (hqb : qb ≠ 0)
    (hf0 : 1 - Bcc * α ^ 2 * qb ≠ 0) (hf : f = 1 - α ^ 2 * (Bcc * qb)) :
    (Bcc + (α * qb * Bcc / (qb * f)) ^ 2 * (qb * f)) * qb = Bcc * qb / f := by
  subst hf
  field_simp
  ring

private lemma anchor_new_norm (qb f : ZMod 5) (hqb : qb ≠ 0) (hf : f ≠ 0) :
    ((qb * f)⁻¹ * (qb * f)⁻¹ * (qb * f)) * qb = f⁻¹ := by
  field_simp

theorem exists_fiveNondeg_hyperplane {k : ℕ} {ε : Bool}
    {W : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)} (hW : IsFiveNondeg k ε W)
    (h1 : 1 ≤ Module.finrank (ZMod 5) W) :
    ∃ H ≤ W, IsFiveNondeg k ε H ∧ Module.finrank (ZMod 5) H + 1 = Module.finrank (ZMod 5) W := by
  have hWne : W ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at h1
    exact absurd h1 (by decide)
  have hex : ∃ n ∈ W, fiveForm k ε n n ≠ 0 := by
    by_contra h
    push Not at h
    refine hWne ((Submodule.eq_bot_iff W).mpr fun x hx => ?_)
    refine (isFiveNondeg_iff.1 hW) x hx fun y hy => ?_
    have hxy := h (x + y) (add_mem hx hy)
    have hx0 := h x hx
    have hy0 := h y hy
    rw [fiveForm_add_left, fiveForm_add_right, fiveForm_add_right,
      hx0, hy0, fiveForm_comm k ε y x] at hxy
    have h2 : (2 : ZMod 5) * fiveForm k ε x y = 0 := by
      ring_nf at hxy ⊢
      exact hxy
    exact (mul_eq_zero.mp h2).resolve_left (by decide)
  obtain ⟨n, hnW, hnQ⟩ := hex
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hnQ (by simp [fiveForm])
  have hUW : Submodule.span (ZMod 5) {n} ≤ W :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hnW)
  refine ⟨W ⊓ fiveOrth k ε (Submodule.span (ZMod 5) {n}), inf_le_left,
    isFiveNondeg_inf_fiveOrth hW (isFiveNondeg_span_singleton hnQ) hUW, ?_⟩
  have hdim := finrank_inf_fiveOrth_add hW hUW
  have hspan1 : Module.finrank (ZMod 5) (Submodule.span (ZMod 5) {n}) = 1 :=
    finrank_span_singleton (K := ZMod 5) hn0
  omega

theorem exists_fiveTree_leaf {k : ℕ} {ε π : Bool}
    {W H : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)} (hW : IsFiveNondeg k ε W)
    (hH : IsFiveNondeg k ε H) (hHW : H ≤ W)
    (hdim : Module.finrank (ZMod 5) H + 1 = Module.finrank (ZMod 5) W)
    {d : ℕ} {b : Fin d → Fin (k + 1) → ZMod 5}
    {p : Fin d → Fin d} {j : Fin d} (hb : IsFiveTree k ε π H b p)
    (hj : IsFiveAnchor k ε H b j) :
    ∃ x ∈ W, x ∉ H ∧ fiveForm k ε x (b j) ≠ 0 ∧
      IsFiveTree k ε π W (Fin.snoc b x : Fin (d + 1) → Fin (k + 1) → ZMod 5)
        (Fin.snoc (fun i => (p i).castSucc) j.castSucc : Fin (d + 1) → Fin (d + 1)) ∧
      ∃ j' : Fin (d + 1),
        IsFiveAnchor k ε W (Fin.snoc b x : Fin (d + 1) → Fin (k + 1) → ZMod 5) j' := by
  unfold IsFiveTree at hb
  obtain ⟨hb1, hbli, hbpar, hbgr⟩ := hb
  have hbmem : ∀ i, b i ∈ H := fun i => (hb1 i).1
  have hbQ : ∀ i, fiveForm k ε (b i) (b i) ≠ 0 := fun i => (hb1 i).2.1
  have hbπ : ∀ i, IsSquare (fiveForm k ε (b i) (b i)) ↔ π = true := fun i => (hb1 i).2.2
  unfold IsFiveAnchor at hj
  obtain ⟨c, hcH, hcdual, hct⟩ := hj
  have hd0 : d ≠ 0 := by have := j.isLt; omega
  have haux : ∃ n ∈ W, n ∈ fiveOrth k ε H ∧ n ∉ H ∧ fiveForm k ε n n ≠ 0 := by
    let N : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5) := W ⊓ fiveOrth k ε H
    have hNnd : IsFiveNondeg k ε N := isFiveNondeg_inf_fiveOrth hW hH hHW
    have hNdim : Module.finrank (ZMod 5) N + Module.finrank (ZMod 5) H =
        Module.finrank (ZMod 5) W := finrank_inf_fiveOrth_add hW hHW
    have hN1 : Module.finrank (ZMod 5) N = 1 := by omega
    have hNne : N ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hN1
      exact absurd hN1 (by decide)
    obtain ⟨n, hnN, hn0⟩ := (Submodule.ne_bot_iff N).mp hNne
    have hnH : n ∉ H := by
      intro hnH
      exact hn0 ((isFiveNondeg_iff.1 hH) n hnH (fun y hy => (mem_fiveOrth.mp hnN.2) y hy))
    have hNspan : N = Submodule.span (ZMod 5) {n} :=
      @eq_span_singleton_of_mem_of_finrank_eq_one (ZMod 5) (Fin (k + 1) → ZMod 5) _ _
        (Pi.Function.module (Fin (k + 1)) (ZMod 5) (ZMod 5)) N n hN1 hnN hn0
    have hnQ : fiveForm k ε n n ≠ 0 := by
      intro hQ0
      have hrad : ∀ y ∈ N, fiveForm k ε n y = 0 := by
        intro y hy
        have hy' : y ∈ Submodule.span (ZMod 5) {n} := hNspan ▸ hy
        rw [Submodule.mem_span_singleton] at hy'
        obtain ⟨ν, rfl⟩ := hy'
        rw [fiveForm_smul_right, hQ0, mul_zero]
      exact hn0 ((isFiveNondeg_iff.1 hNnd) n hnN hrad)
    exact ⟨n, hnN.1, hnN.2, hnH, hnQ⟩
  obtain ⟨n, hnW, hnorth, hnH, hnQ⟩ := haux
  have hnb : ∀ i, fiveForm k ε n (b i) = 0 :=
    fun i => (mem_fiveOrth.mp hnorth) (b i) (hbmem i)
  have hcn : fiveForm k ε c n = 0 := by
    rw [fiveForm_comm]; exact (mem_fiveOrth.mp hnorth) c hcH
  let qb : ZMod 5 := fiveForm k ε (b j) (b j)
  let t : ZMod 5 := fiveForm k ε c c * qb
  have htns : ¬ IsSquare t := hct
  obtain ⟨α, hα12, hf34, hsq⟩ :=
    exists_alpha_factor t (qb * fiveForm k ε n n) htns (mul_ne_zero (hbQ j) hnQ)
  let f : ZMod 5 := 1 - α ^ 2 * t
  have hf_ne : f ≠ 0 := by
    rcases hf34 with h | h <;> rw [show f = 1 - α ^ 2 * t from rfl, h] <;> decide
  obtain ⟨μ', hμ'⟩ := hsq
  let μ : ZMod 5 := μ' * (fiveForm k ε n n)⁻¹
  have hμQn : μ ^ 2 * fiveForm k ε n n = qb * f := by
    have hμ'2 : μ' ^ 2 = (qb * fiveForm k ε n n) * f := by rw [pow_two, hμ']
    simp only [μ]
    rw [mul_pow, hμ'2]
    field_simp
  have hμ_ne : μ ≠ 0 := by
    intro hμ0
    have h0 : qb * f = 0 := by rw [← hμQn, hμ0]; ring
    exact mul_ne_zero (hbQ j) hf_ne h0
  let a : ZMod 5 := α * qb
  have ha_ne : a ≠ 0 := by
    simp only [a]
    exact mul_ne_zero (by rcases hα12 with h | h <;> rw [h] <;> decide) (hbQ j)
  let x : Fin (k + 1) → ZMod 5 := a • c + μ • n
  have hxW : x ∈ W := by
    rw [show x = a • c + μ • n from rfl]
    exact add_mem (Submodule.smul_mem W a (hHW hcH)) (Submodule.smul_mem W μ hnW)
  have hxH : x ∉ H := by
    intro hxHmem
    have hμnH : μ • n ∈ H := by
      have h : x - a • c ∈ H := Submodule.sub_mem H hxHmem (Submodule.smul_mem H a hcH)
      have hxsub : x - a • c = μ • n := by
        rw [show x = a • c + μ • n from rfl]
        exact add_sub_cancel_left (a • c) (μ • n)
      rwa [hxsub] at h
    have hnHmem : n ∈ H := by
      have h := Submodule.smul_mem H (μ⁻¹) hμnH
      rwa [smul_smul, inv_mul_cancel₀ hμ_ne, one_smul] at h
    exact hnH hnHmem
  have hQx : fiveForm k ε x x = qb := by
    rw [show x = a • c + μ • n from rfl, fiveForm_add_smul_self]
    simp only [hcn, mul_zero, add_zero]
    rw [hμQn]
    simp only [a, f, t, qb]
    ring
  have hBxi : ∀ i : Fin d, fiveForm k ε x (b i) = a * (if i = j then 1 else 0) := by
    intro i
    rw [show x = a • c + μ • n from rfl, fiveForm_add_smul_left, hcdual i, hnb i,
      mul_zero, add_zero]
  have hBxj_ne : fiveForm k ε x (b j) ≠ 0 := by
    rw [hBxi j, if_pos rfl, mul_one]
    exact ha_ne
  refine ⟨x, hxW, hxH, hBxj_ne, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      cases i using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last]
        exact ⟨hxW, by rw [hQx]; exact hbQ j, by rw [hQx]; exact hbπ j⟩
      | cast i =>
        simp only [Fin.snoc_castSucc]
        exact ⟨hHW (hbmem i), hbQ i, hbπ i⟩
    · refine (@linearIndependent_finSnoc (ZMod 5) (Fin (k + 1) → ZMod 5) _ _
        (Pi.Function.module (Fin (k + 1)) (ZMod 5) (ZMod 5)) x d b).mpr ⟨hbli, ?_⟩
      intro hxspan
      exact hxH (Submodule.span_le.mpr (by rintro y ⟨i, rfl⟩; exact hbmem i) hxspan)
    · intro i hi
      cases i using Fin.lastCases with
      | last =>
        refine ⟨by simp, ?_⟩
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        rw [hBxi j, if_pos rfl, mul_one]
        exact ha_ne
      | cast i =>
        have hi' : (i : ℕ) ≠ 0 := by simpa using hi
        obtain ⟨hlt, hne⟩ := hbpar i hi'
        refine ⟨by simpa using hlt, ?_⟩
        simpa only [Fin.snoc_castSucc] using hne
    · intro i i' hij
      cases i using Fin.lastCases with
      | last =>
        cases i' using Fin.lastCases with
        | last => exact Or.inl rfl
        | cast i' =>
          refine Or.inr (Or.inl ⟨by simpa using hd0, ?_⟩)
          simp only [Fin.snoc_last, Fin.snoc_castSucc] at hij
          rw [hBxi i'] at hij
          have h_eq : i' = j := by
            by_contra hne
            rw [if_neg hne, mul_zero] at hij
            exact hij rfl
          subst h_eq
          rw [Fin.snoc_last]
      | cast i =>
        cases i' using Fin.lastCases with
        | last =>
          refine Or.inr (Or.inr ⟨by simpa using hd0, ?_⟩)
          simp only [Fin.snoc_castSucc, Fin.snoc_last] at hij
          rw [fiveForm_comm] at hij
          rw [hBxi i] at hij
          have h_eq : i = j := by
            by_contra hne
            rw [if_neg hne, mul_zero] at hij
            exact hij rfl
          subst h_eq
          rw [Fin.snoc_last]
        | cast i' =>
          simp only [Fin.snoc_castSucc] at hij
          rcases hbgr i i' hij with h | h | h
          · exact Or.inl (by rw [h])
          · exact Or.inr (Or.inl ⟨by simpa using h.1,
              by simp only [Fin.snoc_castSucc]; rw [h.2]⟩)
          · exact Or.inr (Or.inr ⟨by simpa using h.1,
              by simp only [Fin.snoc_castSucc]; rw [h.2]⟩)
  · let y : Fin (k + 1) → ZMod 5 := μ • n
    have hyQ : fiveForm k ε y y = qb * f := by
      rw [show y = μ • n from rfl, fiveForm_smul_smul]
      rw [show μ * μ = μ ^ 2 by ring, hμQn]
    have hy_ne : fiveForm k ε y y ≠ 0 := by
      rw [hyQ]; exact mul_ne_zero (hbQ j) hf_ne
    have hyb : ∀ i : Fin d, fiveForm k ε y (b i) = 0 := by
      intro i
      rw [show y = μ • n from rfl, fiveForm_smul_left, hnb i, mul_zero]
    have hyx : fiveForm k ε y x = fiveForm k ε y y := by
      have h1 : fiveForm k ε y (a • c) = 0 := by
        rw [show y = μ • n from rfl, fiveForm_smul_left, fiveForm_smul_right,
          fiveForm_comm k ε n c, hcn, mul_zero, mul_zero]
      rw [show x = a • c + μ • n from rfl, fiveForm_add_right, h1,
        show μ • n = y from rfl, zero_add]
    have hf34' : f = 3 ∨ f = 4 := hf34
    rcases hf34' with hf3 | hf4
    ·
      have hyW : y ∈ W := Submodule.smul_mem W μ hnW
      let c'' : Fin (k + 1) → ZMod 5 := (fiveForm k ε y y)⁻¹ • y
      have hc''W : c'' ∈ W := Submodule.smul_mem W (fiveForm k ε y y)⁻¹ hyW
      have hQc'' : fiveForm k ε c'' c'' * qb = (3 : ZMod 5)⁻¹ := by
        rw [show c'' = (fiveForm k ε y y)⁻¹ • y from rfl, fiveForm_smul_smul, hyQ]
        rw [anchor_new_norm qb f (hbQ j) hf_ne, hf3]
      have hc''dual : ∀ i : Fin (d + 1),
          fiveForm k ε c'' ((Fin.snoc b x : Fin (d + 1) → Fin (k + 1) → ZMod 5) i) =
            if i = Fin.last d then 1 else 0 := by
        intro i
        cases i using Fin.lastCases with
        | last =>
          rw [Fin.snoc_last, show c'' = (fiveForm k ε y y)⁻¹ • y from rfl,
            fiveForm_smul_left, hyx, inv_mul_cancel₀ hy_ne, if_pos rfl]
        | cast i' =>
          rw [Fin.snoc_castSucc, show c'' = (fiveForm k ε y y)⁻¹ • y from rfl,
            fiveForm_smul_left, hyb i', mul_zero]
          have hne : (i'.castSucc : Fin (d + 1)) ≠ Fin.last d := by
            intro h
            have h' := congrArg Fin.val h
            simp at h'
            omega
          rw [if_neg hne]
      have hc''ns : ¬ IsSquare (fiveForm k ε c'' c'' *
          fiveForm k ε ((Fin.snoc b x : Fin (d + 1) → Fin (k + 1) → ZMod 5) (Fin.last d))
            ((Fin.snoc b x : Fin (d + 1) → Fin (k + 1) → ZMod 5) (Fin.last d))) := by
        rw [Fin.snoc_last, hQx, hQc'']
        exact zmod5_inv_three_nonsquare
      exact ⟨Fin.last d, c'', hc''W, hc''dual, hc''ns⟩
    ·
      let c' : Fin (k + 1) → ZMod 5 :=
        c - (a * fiveForm k ε c c / fiveForm k ε y y) • y
      have hyW : y ∈ W := Submodule.smul_mem W μ hnW
      have hc'W : c' ∈ W :=
        Submodule.sub_mem W (hHW hcH)
          (Submodule.smul_mem W (a * fiveForm k ε c c / fiveForm k ε y y) hyW)
      have hcy : fiveForm k ε c y = 0 := by
        rw [show y = μ • n from rfl, fiveForm_smul_right, hcn, mul_zero]
      have hcx : fiveForm k ε c x = a * fiveForm k ε c c := by
        rw [show x = a • c + μ • n from rfl, fiveForm_add_right, fiveForm_smul_right,
          fiveForm_smul_right, hcn, mul_zero, add_zero]
      have hc'x : fiveForm k ε c' x = 0 := by
        rw [show c' = c - (a * fiveForm k ε c c / fiveForm k ε y y) • y from rfl,
          fiveForm_sub_left, fiveForm_smul_left, hcx, hyx,
          div_mul_cancel₀ (a * fiveForm k ε c c) hy_ne, sub_self]
      have hQc' : fiveForm k ε c' c' * qb = t / 4 := by
        have hf0 : 1 - fiveForm k ε c c * α ^ 2 * qb ≠ 0 := by
          have h : f = 1 - fiveForm k ε c c * α ^ 2 * qb := by
            rw [show f = 1 - α ^ 2 * t from rfl,
              show t = fiveForm k ε c c * qb from rfl]
            ring
          rwa [h] at hf_ne
        have h := anchor_old_norm (fiveForm k ε c c) qb α f (hbQ j) hf0
          (by rw [show f = 1 - α ^ 2 * t from rfl,
            show t = fiveForm k ε c c * qb from rfl])
        rw [show c' = c - (a * fiveForm k ε c c / fiveForm k ε y y) • y from rfl,
          fiveForm_sub_smul_self, hcy, hyQ]
        simp only [a]
        rw [show (fiveForm k ε c c - 2 * (α * qb * fiveForm k ε c c / (qb * f)) * 0 +
              (α * qb * fiveForm k ε c c / (qb * f)) ^ 2 * (qb * f)) * qb =
            (fiveForm k ε c c + (α * qb * fiveForm k ε c c / (qb * f)) ^ 2 * (qb * f)) * qb by
          ring]
        rw [h, show fiveForm k ε c c * qb = t from rfl, hf4]
      have hc'dual : ∀ i : Fin (d + 1),
          fiveForm k ε c' ((Fin.snoc b x : Fin (d + 1) → Fin (k + 1) → ZMod 5) i) =
            if i = j.castSucc then 1 else 0 := by
        intro i
        cases i using Fin.lastCases with
        | last =>
          rw [Fin.snoc_last, hc'x]
          have hne : (Fin.last d : Fin (d + 1)) ≠ j.castSucc := by
            intro h
            have h' := congrArg Fin.val h
            simp at h'
            omega
          rw [if_neg hne]
        | cast i' =>
          rw [Fin.snoc_castSucc, show c' = c - (a * fiveForm k ε c c /
            fiveForm k ε y y) • y from rfl, fiveForm_sub_left, fiveForm_smul_left,
            hyb i']
          simp only [mul_zero, sub_zero]
          rw [hcdual i']
          by_cases h : i' = j
          · rw [if_pos h, if_pos (by rw [h])]
          · rw [if_neg h, if_neg (fun hc => h (Fin.castSucc_inj.mp hc))]
      have hc'ns : ¬ IsSquare (fiveForm k ε c' c' *
          fiveForm k ε ((Fin.snoc b x : Fin (d + 1) → Fin (k + 1) → ZMod 5) j.castSucc)
            ((Fin.snoc b x : Fin (d + 1) → Fin (k + 1) → ZMod 5) j.castSucc)) := by
        rw [Fin.snoc_castSucc, show fiveForm k ε (b j) (b j) = qb from rfl, hQc']
        exact zmod5_div_four_nonsquare t htns
      exact ⟨j.castSucc, c', hc'W, hc'dual, hc'ns⟩

theorem fiveReflectionGroupIn_eq_sup_of_hyperplane {k : ℕ} {ε π : Bool}
    {A H : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)} (hA : IsFiveNondeg k ε A)
    (hH : IsFiveNondeg k ε H) (hHA : H ≤ A)
    (hdim : Module.finrank (ZMod 5) H + 1 = Module.finrank (ZMod 5) A)
    (h4 : 4 ≤ Module.finrank (ZMod 5) H) {x : Fin (k + 1) → ZMod 5} (hxA : x ∈ A) (hxH : x ∉ H)
    (hx : fiveForm k ε x x ≠ 0) (hxπ : IsSquare (fiveForm k ε x x) ↔ π = true)
    {h : Fin (k + 1) → ZMod 5} (hh : h ∈ H) (hxh : fiveForm k ε x h ≠ 0) :
    fiveReflectionGroupIn k ε π A =
      fiveReflectionGroupIn k ε π H ⊔ Subgroup.closure {fiveReflOf k ε x} := by
  refine le_antisymm ?_ ?_
  · rw [fiveReflectionGroupIn]
    refine (Subgroup.closure_le (K := _)).mpr ?_
    rintro g ⟨y, hyA, hyQ, hyπ, hgform⟩
    obtain ⟨v, hv, hQ, hπ, hgv⟩ :=
      eq_fiveReflOf_of_mem_fiveReflectionsIn ⟨y, hyA, hyQ, hyπ, hgform⟩
    rw [hgv]
    exact fiveReflOf_mem_fiveReflectionGroupIn_sup_of_hyperplane hA hH hHA hdim h4 hxA hxH hx
      hxπ hh hxh hv hQ hπ
  · refine sup_le (fiveReflectionGroupIn_mono hHA) ?_
    refine (Subgroup.closure_le (K := _)).mpr ?_
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact fiveReflOf_mem_fiveReflectionGroupIn hxA hx hxπ

theorem fiveForm_e11G3_mulVec {k : ℕ} {ε : Bool} {q : ZMod 5}
    {b : Fin 3 → Fin (k + 1) → ZMod 5}
    (hgram : ∀ i j, fiveForm k ε (b i) (b j) = q * e11G3 i j) (c : Fin 3 → ZMod 5)
    (j : Fin 3) :
    fiveForm k ε (∑ i, c i • b i) (b j) = q * (e11G3.mulVec c) j := by
  rw [fiveForm_sum_smul_left, e11G3_mulVec_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hgram i j, e11G3_symm j i]
  ring

theorem e11G3_mulVec_eq_zero_of_sum_eq_zero {k : ℕ} {ε : Bool} {q : ZMod 5}
    {b : Fin 3 → Fin (k + 1) → ZMod 5}
    (hgram : ∀ i j, fiveForm k ε (b i) (b j) = q * e11G3 i j) (hq : q ≠ 0)
    {c : Fin 3 → ZMod 5} (hc : ∑ i, c i • b i = 0) : e11G3.mulVec c = 0 := by
  funext j
  have h := fiveForm_e11G3_mulVec hgram c j
  rw [hc] at h
  have h0 : fiveForm k ε 0 (b j) = 0 := by simp [fiveForm]
  rw [h0] at h
  exact (mul_eq_zero.mp h.symm).resolve_left hq

theorem linearIndependent_e11G3 {k : ℕ} {ε : Bool} {q : ZMod 5}
    {b : Fin 3 → Fin (k + 1) → ZMod 5}
    (hgram : ∀ i j, fiveForm k ε (b i) (b j) = q * e11G3 i j) (hq : q ≠ 0) :
    LinearIndependent (ZMod 5) b := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h := congrArg e11G3inv.mulVec (e11G3_mulVec_eq_zero_of_sum_eq_zero hgram hq hc)
  rw [Matrix.mulVec_mulVec, e11G3_inv_mul, Matrix.one_mulVec, Matrix.mulVec_zero] at h
  exact fun i => congrFun h i

theorem finrank_span_e11G3 {k : ℕ} {ε : Bool} {q : ZMod 5}
    {b : Fin 3 → Fin (k + 1) → ZMod 5}
    (hgram : ∀ i j, fiveForm k ε (b i) (b j) = q * e11G3 i j) (hq : q ≠ 0) :
    Module.finrank (ZMod 5) (Submodule.span (ZMod 5) (Set.range b)) = 3 := by
  rw [finrank_span_eq_card (linearIndependent_e11G3 hgram hq), Fintype.card_fin]

theorem isFiveNondeg_span_e11G3 {k : ℕ} {ε : Bool} {q : ZMod 5}
    {b : Fin 3 → Fin (k + 1) → ZMod 5}
    (hgram : ∀ i j, fiveForm k ε (b i) (b j) = q * e11G3 i j) (hq : q ≠ 0) :
    IsFiveNondeg k ε (Submodule.span (ZMod 5) (Set.range b)) := by
  rw [isFiveNondeg_iff]
  intro x hx hxorth
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ZMod 5)).mp hx
  have hc0 : c = 0 := by
    have hsys : e11G3.mulVec c = 0 := by
      funext j
      have h := fiveForm_e11G3_mulVec hgram c j
      have hzero : fiveForm k ε (∑ i, c i • b i) (b j) = 0 :=
        hxorth (b j) (Submodule.subset_span ⟨j, rfl⟩)
      rw [hzero] at h
      exact (mul_eq_zero.mp h.symm).resolve_left hq
    have h := congrArg (fun v => e11G3inv.mulVec v) hsys
    rw [Matrix.mulVec_mulVec, e11G3_inv_mul, Matrix.one_mulVec, Matrix.mulVec_zero] at h
    exact h
  rw [hc0]
  simp

theorem exists_e11G3_path {k : ℕ} {ε : Bool} {W : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)}
    (hW : IsFiveNondeg k ε W) (h4 : 4 ≤ Module.finrank (ZMod 5) W) {q : ZMod 5} (hq : q ≠ 0) :
    ∃ b : Fin 3 → Fin (k + 1) → ZMod 5, (∀ i, b i ∈ W) ∧
      ∀ i j, fiveForm k ε (b i) (b j) = q * e11G3 i j := by
  obtain ⟨b0, hb0W, hb0Q⟩ := exists_fiveForm_eq_of_nondeg hW (by omega) (c := q)
  have hb00 : b0 ≠ 0 := by
    rintro rfl
    exact hq (by simpa [fiveForm] using hb0Q.symm)
  let L : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5) := Submodule.span (ZMod 5) {b0}
  have hLnd : IsFiveNondeg k ε L :=
    isFiveNondeg_span_singleton (by rw [hb0Q]; exact hq)
  have hLW : L ≤ W := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hb0W)
  have hNnd : IsFiveNondeg k ε (W ⊓ fiveOrth k ε L) := isFiveNondeg_inf_fiveOrth hW hLnd hLW
  have hNdim := finrank_inf_fiveOrth_add hW hLW
  have hL1 : Module.finrank (ZMod 5) L = 1 := finrank_span_singleton (K := ZMod 5) hb00
  have hN3 : 3 ≤ Module.finrank (ZMod 5) ↥(W ⊓ fiveOrth k ε L) := by omega
  obtain ⟨u, huN, hu0, huQ⟩ := exists_fiveForm_eq_zero_of_nondeg hNnd hN3
  obtain ⟨u', hu'N, hBuu', hu'Q⟩ := exists_fiveForm_hyperbolic_partner hNnd huN huQ hu0
  have huNb0 : fiveForm k ε u b0 = 0 :=
    (mem_fiveOrth.mp huN.2) b0 (Submodule.mem_span_singleton_self b0)
  have hu'Nb0 : fiveForm k ε u' b0 = 0 :=
    (mem_fiveOrth.mp hu'N.2) b0 (Submodule.mem_span_singleton_self b0)
  have hb0u : fiveForm k ε b0 u = 0 := by rw [fiveForm_comm]; exact huNb0
  have hb0u' : fiveForm k ε b0 u' = 0 := by rw [fiveForm_comm]; exact hu'Nb0
  have huW : u ∈ W := huN.1
  have hu'W : u' ∈ W := hu'N.1
  let b : Fin 3 → Fin (k + 1) → ZMod 5 := ![b0, b0 + u, (2 * q) • u' + (4 : ZMod 5) • u]
  have hB00 : fiveForm k ε b0 b0 = q := hb0Q
  have hB01 : fiveForm k ε b0 (b0 + u) = q := by
    rw [fiveForm_add_right, hB00, hb0u, add_zero]
  have hB02 : fiveForm k ε b0 ((2 * q) • u' + (4 : ZMod 5) • u) = 0 := by
    rw [fiveForm_add_right, fiveForm_smul_right, fiveForm_smul_right, hb0u', hb0u,
      mul_zero, mul_zero, add_zero]
  have hB10 : fiveForm k ε (b0 + u) b0 = q := by rw [fiveForm_comm]; exact hB01
  have hB11 : fiveForm k ε (b0 + u) (b0 + u) = q := by
    rw [fiveForm_add_left, fiveForm_add_right, fiveForm_add_right, hB00, hb0u, huNb0, huQ]
    ring
  have hB12 : fiveForm k ε (b0 + u) ((2 * q) • u' + (4 : ZMod 5) • u) = 2 * q := by
    rw [fiveForm_add_left, fiveForm_add_right, fiveForm_add_right, fiveForm_smul_right,
      fiveForm_smul_right, fiveForm_smul_right, fiveForm_smul_right, hb0u', hb0u, hBuu', huQ]
    ring
  have hB20 : fiveForm k ε ((2 * q) • u' + (4 : ZMod 5) • u) b0 = 0 := by
    rw [fiveForm_comm]; exact hB02
  have hB21 : fiveForm k ε ((2 * q) • u' + (4 : ZMod 5) • u) (b0 + u) = 2 * q := by
    rw [fiveForm_comm]; exact hB12
  have hB22 : fiveForm k ε ((2 * q) • u' + (4 : ZMod 5) • u)
      ((2 * q) • u' + (4 : ZMod 5) • u) = q := by
    rw [fiveForm_add_smul_self, hu'Q, huQ, mul_zero, mul_zero, zero_add, add_zero,
      fiveForm_comm k ε u' u, hBuu', mul_one]
    have h16 : (2 : ZMod 5) * 2 * 4 = 1 := by decide
    calc 2 * (2 * q) * 4 = ((2 : ZMod 5) * 2 * 4) * q := by ring
      _ = 1 * q := by rw [h16]
      _ = q := one_mul q
  refine ⟨b, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hb0W
    · exact W.add_mem hb0W huW
    · exact W.add_mem (W.smul_mem (2 * q) hu'W) (W.smul_mem (4 : ZMod 5) huW)
  · intro i j
    fin_cases i
    · fin_cases j
      · change fiveForm k ε b0 b0 = q * e11G3 0 0
        rw [hB00, show e11G3 0 0 = 1 by decide]
        ring
      · change fiveForm k ε b0 (b0 + u) = q * e11G3 0 1
        rw [hB01, show e11G3 0 1 = 1 by decide]
        ring
      · change fiveForm k ε b0 ((2 * q) • u' + (4 : ZMod 5) • u) = q * e11G3 0 2
        rw [hB02, show e11G3 0 2 = 0 by decide]
        ring
    · fin_cases j
      · change fiveForm k ε (b0 + u) b0 = q * e11G3 1 0
        rw [hB10, show e11G3 1 0 = 1 by decide]
        ring
      · change fiveForm k ε (b0 + u) (b0 + u) = q * e11G3 1 1
        rw [hB11, show e11G3 1 1 = 1 by decide]
        ring
      · change fiveForm k ε (b0 + u) ((2 * q) • u' + (4 : ZMod 5) • u) = q * e11G3 1 2
        rw [hB12, show e11G3 1 2 = 2 by decide]
        ring
    · fin_cases j
      · change fiveForm k ε ((2 * q) • u' + (4 : ZMod 5) • u) b0 = q * e11G3 2 0
        rw [hB20, show e11G3 2 0 = 0 by decide]
        ring
      · change fiveForm k ε ((2 * q) • u' + (4 : ZMod 5) • u) (b0 + u) = q * e11G3 2 1
        rw [hB21, show e11G3 2 1 = 2 by decide]
        ring
      · change fiveForm k ε ((2 * q) • u' + (4 : ZMod 5) • u)
          ((2 * q) • u' + (4 : ZMod 5) • u) = q * e11G3 2 2
        rw [hB22, show e11G3 2 2 = 1 by decide]
        ring

private theorem e11G3_parent : ∀ i : Fin 3, (i : ℕ) ≠ 0 →
    ((![0, 0, 1] i : Fin 3) : ℕ) < (i : ℕ) ∧ e11G3 i (![0, 0, 1] i) ≠ 0 := by
  decide

private theorem e11G3_offdiag : ∀ i j : Fin 3, e11G3 i j ≠ 0 →
    i = j ∨ ((i : ℕ) ≠ 0 ∧ j = (![0, 0, 1] i : Fin 3)) ∨
      ((j : ℕ) ≠ 0 ∧ i = (![0, 0, 1] j : Fin 3)) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl ⟨by decide, by decide⟩)
      | exact Or.inr (Or.inr ⟨by decide, by decide⟩)
      | exact absurd (by decide) hij

theorem isFiveTree_e11G3 {k : ℕ} {ε π : Bool} {b : Fin 3 → Fin (k + 1) → ZMod 5}
    (hgram : ∀ i j, fiveForm k ε (b i) (b j) = fiveSignRep π * e11G3 i j) :
    IsFiveTree k ε π (Submodule.span (ZMod 5) (Set.range b)) b ![0, 0, 1] := by
  have hq : fiveSignRep π ≠ 0 := fiveSignRep_ne_zero π
  refine ⟨?_, linearIndependent_e11G3 hgram hq, ?_, ?_⟩
  · intro i
    refine ⟨Submodule.subset_span ⟨i, rfl⟩, ?_, ?_⟩
    · rw [hgram i i, e11G3_self, mul_one]
      exact hq
    · rw [hgram i i, e11G3_self, mul_one]
      exact isSquare_fiveSignRep_iff π
  · intro i hi
    obtain ⟨hlt, hne⟩ := e11G3_parent i hi
    exact ⟨hlt, by rw [hgram i (![0, 0, 1] i)]; exact mul_ne_zero hq hne⟩
  · intro i j hij
    apply e11G3_offdiag i j
    intro h0
    exact hij (by rw [hgram i j, h0, mul_zero])

theorem isFiveAnchor_e11G3 {k : ℕ} {ε : Bool} {q : ZMod 5} (hq : q ≠ 0)
    {b : Fin 3 → Fin (k + 1) → ZMod 5}
    (hgram : ∀ i j, fiveForm k ε (b i) (b j) = q * e11G3 i j) :
    IsFiveAnchor k ε (Submodule.span (ZMod 5) (Set.range b)) b 0 := by
  have hcW : q⁻¹ • (∑ i, e11G3inv 0 i • b i) ∈
      Submodule.span (ZMod 5) (Set.range b) := by
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => ?_)
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hdual : ∀ j, fiveForm k ε (q⁻¹ • (∑ i, e11G3inv 0 i • b i)) (b j) =
      if j = 0 then 1 else 0 := by
    intro j
    have hmv : e11G3.mulVec (e11G3inv 0) = Pi.single (0 : Fin 3) 1 := by decide
    rw [fiveForm_smul_left, fiveForm_e11G3_mulVec hgram (e11G3inv 0) j, hmv]
    by_cases hj : j = 0
    · subst hj
      simp [Pi.single_eq_same, inv_mul_cancel₀ hq]
    · simp [hj]
  have hQc : fiveForm k ε (q⁻¹ • (∑ i, e11G3inv 0 i • b i))
      (q⁻¹ • (∑ i, e11G3inv 0 i • b i)) = q⁻¹ * 2 := by
    rw [fiveForm_smul_right, fiveForm_sum_smul_right]
    simp only [hdual]
    have hs : (∑ i : Fin 3, e11G3inv 0 i * (if i = 0 then 1 else 0)) = (2 : ZMod 5) := by
      decide
    rw [hs]
  refine ⟨q⁻¹ • (∑ i, e11G3inv 0 i • b i), hcW, hdual, ?_⟩
  rw [hQc, hgram 0 0, e11G3_self, mul_one]
  have h2 : q⁻¹ * 2 * q = (2 : ZMod 5) := by
    rw [mul_assoc, mul_comm (2 : ZMod 5) q, ← mul_assoc, inv_mul_cancel₀ hq, one_mul]
  rw [h2]
  decide

theorem exists_e11G_snoc {k : ℕ} {ε π : Bool} {b : Fin 3 → Fin (k + 1) → ZMod 5}
    (hgram : ∀ i j, fiveForm k ε (b i) (b j) = fiveSignRep π * e11G3 i j)
    {x : Fin (k + 1) → ZMod 5} (hx : fiveForm k ε x x ≠ 0)
    (hxπ : IsSquare (fiveForm k ε x x) ↔ π = true) (hx0 : fiveForm k ε x (b 0) ≠ 0)
    (hx1 : fiveForm k ε x (b 1) = 0) (hx2 : fiveForm k ε x (b 2) = 0) :
    ∃ s : ZMod 5, s ≠ 0 ∧ ∃ a : ZMod 5, a ≠ 0 ∧ ∀ i j,
      fiveForm k ε ((Fin.snoc b (s • x) : Fin 4 → Fin (k + 1) → ZMod 5) i)
        ((Fin.snoc b (s • x) : Fin 4 → Fin (k + 1) → ZMod 5) j) =
        fiveSignRep π * e11G a i j := by
  have hq : fiveSignRep π ≠ 0 := fiveSignRep_ne_zero π
  have hsq : IsSquare (fiveForm k ε x x) ↔ IsSquare (fiveSignRep π) :=
    hxπ.trans (isSquare_fiveSignRep_iff π).symm
  obtain ⟨l, hl⟩ := exists_sq_mul_eq_of_isSquare_iff hx hq hsq
  have hl0 : l ≠ 0 := by
    intro h0
    rw [h0] at hl
    simp at hl
    exact hq hl.symm
  let a : ZMod 5 := l * fiveForm k ε x (b 0) * (fiveSignRep π)⁻¹
  have ha : a ≠ 0 := by
    simp only [a]
    exact mul_ne_zero (mul_ne_zero hl0 hx0) (inv_ne_zero hq)
  have hsx0 : fiveForm k ε (l • x) (b 0) = fiveSignRep π * a := by
    rw [fiveForm_smul_left]
    simp only [a]
    field_simp
  refine ⟨l, hl0, a, ha, ?_⟩
  intro i j
  cases i using Fin.lastCases with
  | last =>
    cases j using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last]
      rw [fiveForm_smul_left, fiveForm_smul_right, ← mul_assoc, ← pow_two, hl]
      simp [e11G]
    | cast j =>
      simp only [Fin.snoc_last, Fin.snoc_castSucc]
      fin_cases j
      · simpa [e11G] using hsx0
      · simp [e11G, fiveForm_smul_left, hx1]
      · simp [e11G, fiveForm_smul_left, hx2]
  | cast i =>
    cases j using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      rw [fiveForm_comm]
      fin_cases i
      · simpa [e11G] using hsx0
      · simp [e11G, fiveForm_smul_left, hx1]
      · simp [e11G, fiveForm_smul_left, hx2]
    | cast j =>
      simp only [Fin.snoc_castSucc]
      rw [hgram i j]
      congr 1
      fin_cases i <;> fin_cases j <;> rfl

theorem exists_fiveTree_four {k : ℕ} {ε π : Bool} {W : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)}
    (hW : IsFiveNondeg k ε W) (h4 : Module.finrank (ZMod 5) W = 4) :
    ∃ (b : Fin 4 → Fin (k + 1) → ZMod 5) (p : Fin 4 → Fin 4) (j : Fin 4),
      IsFiveTree k ε π W b p ∧ IsFiveAnchor k ε W b j ∧
      Subgroup.closure (Set.range fun i => fiveReflOf k ε (b i)) =
        fiveReflectionGroupIn k ε π W := by
  have hq : fiveSignRep π ≠ 0 := fiveSignRep_ne_zero π
  obtain ⟨b, hbW, hgram⟩ := exists_e11G3_path hW h4.ge hq
  have hPW : Submodule.span (ZMod 5) (Set.range b) ≤ W :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr hbW)
  have hP3 := finrank_span_e11G3 hgram hq
  obtain ⟨x, hxW, -, hx0, htree, j', hanchor⟩ :=
    exists_fiveTree_leaf hW (isFiveNondeg_span_e11G3 hgram hq) hPW (by rw [hP3, h4])
      (isFiveTree_e11G3 hgram) (isFiveAnchor_e11G3 hq hgram)
  refine ⟨_, _, j', htree, hanchor, ?_⟩
  have h3 := htree.1 (Fin.last 3)
  simp only [Fin.snoc_last] at h3
  obtain ⟨-, hxQ, hxπ⟩ := h3
  have hx1 : fiveForm k ε x (b 1) = 0 := by
    by_contra h
    have hB : fiveForm k ε ((Fin.snoc b x : Fin 4 → Fin (k + 1) → ZMod 5) (Fin.last 3))
        ((Fin.snoc b x : Fin 4 → Fin (k + 1) → ZMod 5) (Fin.castSucc 1)) ≠ 0 := by
      rw [Fin.snoc_last, Fin.snoc_castSucc]
      exact h
    have h4 := htree.2.2.2 (Fin.last 3) (Fin.castSucc 1) hB
    exact absurd h4 (by decide)
  have hx2 : fiveForm k ε x (b 2) = 0 := by
    by_contra h
    have hB : fiveForm k ε ((Fin.snoc b x : Fin 4 → Fin (k + 1) → ZMod 5) (Fin.last 3))
        ((Fin.snoc b x : Fin 4 → Fin (k + 1) → ZMod 5) (Fin.castSucc 2)) ≠ 0 := by
      rw [Fin.snoc_last, Fin.snoc_castSucc]
      exact h
    have h4 := htree.2.2.2 (Fin.last 3) (Fin.castSucc 2) hB
    exact absurd h4 (by decide)
  obtain ⟨s, hs, a, ha, hgram4⟩ := exists_e11G_snoc hgram hxQ hxπ hx0 hx1 hx2
  have hb'W : ∀ i, (Fin.snoc b (s • x) : Fin 4 → Fin (k + 1) → ZMod 5) i ∈ W := by
    intro i
    cases i using Fin.lastCases with
    | last =>
      rw [Fin.snoc_last]
      exact Submodule.smul_mem W s hxW
    | cast i =>
      rw [Fin.snoc_castSucc]
      exact hbW i
  have hspanx : Submodule.span (ZMod 5)
      (Set.range (Fin.snoc b x : Fin 4 → Fin (k + 1) → ZMod 5)) = W := by
    have hle : Submodule.span (ZMod 5)
        (Set.range (Fin.snoc b x : Fin 4 → Fin (k + 1) → ZMod 5)) ≤ W :=
      Submodule.span_le.mpr (Set.range_subset_iff.mpr fun i => (htree.1 i).1)
    apply Submodule.eq_of_le_of_finrank_eq hle
    rw [finrank_span_eq_card htree.2.1, Fintype.card_fin, h4]
  have hspan : Submodule.span (ZMod 5)
      (Set.range (Fin.snoc b (s • x) : Fin 4 → Fin (k + 1) → ZMod 5)) = W := by
    have hsame : Submodule.span (ZMod 5)
        (Set.range (Fin.snoc b (s • x) : Fin 4 → Fin (k + 1) → ZMod 5)) =
        Submodule.span (ZMod 5) (Set.range (Fin.snoc b x : Fin 4 → Fin (k + 1) → ZMod 5)) := by
      apply le_antisymm
      · apply Submodule.span_le.mpr
        rintro _ ⟨i, rfl⟩
        cases i using Fin.lastCases with
        | last =>
          rw [Fin.snoc_last]
          exact Submodule.smul_mem _ s (Submodule.subset_span ⟨Fin.last 3, by rw [Fin.snoc_last]⟩)
        | cast i =>
          rw [Fin.snoc_castSucc]
          exact Submodule.subset_span ⟨Fin.castSucc i, by rw [Fin.snoc_castSucc]⟩
      · apply Submodule.span_le.mpr
        rintro _ ⟨i, rfl⟩
        cases i using Fin.lastCases with
        | last =>
          rw [Fin.snoc_last]
          have hmem : (Fin.snoc b (s • x) : Fin 4 → Fin (k + 1) → ZMod 5) (Fin.last 3) ∈
              Submodule.span (ZMod 5)
                (Set.range (Fin.snoc b (s • x) : Fin 4 → Fin (k + 1) → ZMod 5)) :=
            Submodule.subset_span ⟨Fin.last 3, rfl⟩
          rw [Fin.snoc_last] at hmem
          have := Submodule.smul_mem _ s⁻¹ hmem
          simpa [smul_smul, inv_mul_cancel₀ hs] using this
        | cast i =>
          rw [Fin.snoc_castSucc]
          exact Submodule.subset_span ⟨Fin.castSucc i, by rw [Fin.snoc_castSucc]⟩
    rw [hsame, hspanx]
  have hrefl : (fun i => fiveReflOf k ε ((Fin.snoc b (s • x) : Fin 4 → Fin (k + 1) → ZMod 5) i)) =
      fun i => fiveReflOf k ε ((Fin.snoc b x : Fin 4 → Fin (k + 1) → ZMod 5) i) := by
    funext i
    cases i using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last]
      exact fiveReflOf_smul k ε x hs
    | cast i =>
      simp only [Fin.snoc_castSucc]
  have hfin := e11ReflectionGroup_eq a ha hb'W hspan hgram4
  rw [hrefl] at hfin
  exact hfin

end CFSG.OddTranspositions.PartThree

end
