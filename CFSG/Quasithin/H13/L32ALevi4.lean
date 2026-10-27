module

public import CFSG.Quasithin.H13.L32ALevi3

public section

namespace CFSG.Quasithin.H13.L32A.C.Levi

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace PP

theorem eqB_iff (x y : ℕ) : eqB x y = true ↔ toM x = toM y := by
  constructor
  · intro h
    have hk : ∀ k < 16, x.testBit k = y.testBit k := by
      intro k hk
      have := List.all_eq_true.mp h k (List.mem_range.mpr hk)
      simpa using this
    ext i j
    simp only [toM, Matrix.of_apply]
    rw [hk _ (by omega)]
  · intro h
    refine List.all_eq_true.mpr fun k hk => ?_
    have hk' : k < 16 := List.mem_range.mp hk
    have e := congrFun (congrFun h ⟨k / 4, by omega⟩) ⟨k % 4, by omega⟩
    simp only [toM, Matrix.of_apply] at e
    have hk4 : 4 * (k / 4) + k % 4 = k := Nat.div_add_mod k 4
    simp only [hk4] at e
    cases hx : x.testBit k <;> cases hy : y.testBit k <;> simp_all

theorem valid_of_validB {p : PP} (h : validB p = true) : p.Valid := by
  rw [Valid, ← toM_bmul, (eqB_iff _ _).mp h, toM_idN]

theorem validB_R2P : validB R2P = true := by decide +kernel

theorem validB_M2P : validB M2P = true := by decide +kernel

theorem valid_R2P : R2P.Valid := valid_of_validB validB_R2P

theorem valid_M2P : M2P.Valid := valid_of_validB validB_M2P

theorem chkA_spec {n : ℕ} (hn : n < 64) : validB (uP n) = true ∧ ∀ e : Bool,
    R1B (uP n) e = true → involB (uP n) e = true → (n = 0 ∧ e = false) ∨ (n, e) ∈ invList := by
  have h := List.all_eq_true.mp chkA_eq n (List.mem_range.mpr hn)
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_imp, beq_iff_eq, List.contains_iff_mem] at h
  obtain ⟨hv, hf, ht⟩ := h
  refine ⟨hv, fun e hr hi => ?_⟩
  cases e
  · rcases hf with (h | h) | h
    · exact absurd (hr ▸ hi ▸ h) (by simp)
    · exact Or.inl ⟨h.1, rfl⟩
    · exact Or.inr h
  · rcases ht with (h | h) | h
    · exact absurd (hr ▸ hi ▸ h) (by simp)
    · simp at h
    · exact Or.inr h

theorem valid_uP {n : ℕ} (hn : n < 64) : (uP n).Valid := valid_of_validB (chkA_spec hn).1

theorem fixB_iff {u g : PP} (hu : u.Valid) (hg : g.Valid) (e : Bool) :
    fixB u e g = true ↔ (toSL g)⁻¹ * mact (toSL u) e (toSL g) ∈ unitriangular 4 (ZMod 2) := by
  rw [fixB, sameB_iff hg (hu.act e hg), toSL_act hu e hg]

theorem swapB_iff {u g : PP} (hu : u.Valid) (hg : g.Valid) (e : Bool) :
    swapB u e g = true ↔ (toSL g * toSL M2P)⁻¹ * mact (toSL u) e (toSL g * toSL R2P) ∈
      unitriangular 4 (ZMod 2) := by
  rw [swapB, sameB_iff (hg.mul valid_M2P) (hu.act e (hg.mul valid_R2P)),
    toSL_act hu e (hg.mul valid_R2P), toSL_mul hg valid_M2P, toSL_mul hg valid_R2P]

theorem toM_eq_iff {p q : PP} (hp : p.Valid) (hq : q.Valid) :
    toM p.m = toM q.m ↔ toSL p = toSL q := by
  constructor
  · intro h
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    rw [coe_toSL hp, coe_toSL hq, h]
  · intro h
    rw [← coe_toSL hp, ← coe_toSL hq, h]

end PP

open PP

noncomputable abbrev R2 : Lin.SLn 4 := toSL R2P

noncomputable abbrev M2 : Lin.SLn 4 := toSL M2P

@[expose] def R1 (u : Lin.SLn 4) (e : Bool) : Prop :=
  R2⁻¹ * mact u e R2 ∈ unitriangular 4 (ZMod 2) ∧ M2⁻¹ * mact u e M2 ∈ unitriangular 4 (ZMod 2)

@[expose] noncomputable def gamE (e : Bool) (g : Lin.SLn 4) : Lin.SLn 4 :=
  if e then BinaryParabolic.graphFun g else g

@[expose] def Invol (u : Lin.SLn 4) (e : Bool) : Prop := u * gamE e u = 1

@[expose] def Sw (u : Lin.SLn 4) (e : Bool) (g : Lin.SLn 4) : Prop :=
  (g * M2)⁻¹ * mact u e (g * R2) ∈ unitriangular 4 (ZMod 2)

@[expose] def Ne' (g h : Lin.SLn 4) : Prop := g⁻¹ * h ∉ unitriangular 4 (ZMod 2)

@[expose] def Four (u : Lin.SLn 4) (e : Bool) : Prop :=
  ∃ g₁ g₂ g₃ g₄ : Lin.SLn 4, Sw u e g₁ ∧ Sw u e g₂ ∧ Sw u e g₃ ∧ Sw u e g₄ ∧ Ne' g₁ g₂ ∧
    Ne' g₁ g₃ ∧ Ne' g₁ g₄ ∧ Ne' g₂ g₃ ∧ Ne' g₂ g₄ ∧ Ne' g₃ g₄

@[expose] def Tr (u : Lin.SLn 4) (e : Bool) : Prop :=
  ∃ g y : Lin.SLn 4, mact u e y = y * u ∧ g⁻¹ * mact u e g ∉ unitriangular 4 (ZMod 2) ∧
    (g * R2)⁻¹ * mact u e (g * R2) ∉ unitriangular 4 (ZMod 2) ∧
    (g * M2)⁻¹ * mact u e (g * M2) ∉ unitriangular 4 (ZMod 2) ∧
    g⁻¹ * (y * y * g) ∈ unitriangular 4 (ZMod 2) ∧
    (g * M2)⁻¹ * (y * y * (g * R2)) ∈ unitriangular 4 (ZMod 2) ∧
    (g * R2)⁻¹ * (y * y * (g * M2)) ∈ unitriangular 4 (ZMod 2)

theorem mact_eq (u : Lin.SLn 4) (e : Bool) (g : Lin.SLn 4) : mact u e g = u * gamE e g := rfl

theorem toSL_gamE' {p : PP} (hp : p.Valid) (e : Bool) : toSL (PP.gamE e p) = gamE e (toSL p) :=
  toSL_gamE hp e

theorem toM_uOf_bits : ∀ b₀ b₁ b₂ b₃ b₄ b₅ : Bool,
    toM (uOf (Nat.bit b₀ (Nat.bit b₁ (Nat.bit b₂ (Nat.bit b₃ (Nat.bit b₄ (Nat.bit b₅ 0))))))) =
      Matrix.of ![![1, cond b₀ 1 0, cond b₁ 1 0, cond b₂ 1 0], ![0, 1, cond b₃ 1 0, cond b₄ 1 0],
        ![0, 0, 1, cond b₅ 1 0], ![0, 0, 0, 1]] := by
  decide +kernel

theorem exists_uP {u : Lin.SLn 4} (hu : u ∈ unitriangular 4 (ZMod 2)) :
    ∃ n < 64, u = toSL (uP n) := by
  obtain ⟨hl, hd⟩ := hu
  set b : Fin 4 → Fin 4 → Bool :=
    fun i j => decide ((u : Matrix (Fin 4) (Fin 4) (ZMod 2)) i j = 1) with hbdef
  set n := Nat.bit (b 0 1) <| Nat.bit (b 0 2) <| Nat.bit (b 0 3) <| Nat.bit (b 1 2) <|
    Nat.bit (b 1 3) <| Nat.bit (b 2 3) 0 with hn
  have hn64 : n < 64 := by
    rw [hn, show (64 : ℕ) = 2 ^ (5 + 1) from rfl, Nat.bit_lt_two_pow_succ_iff,
      Nat.bit_lt_two_pow_succ_iff, Nat.bit_lt_two_pow_succ_iff, Nat.bit_lt_two_pow_succ_iff,
      Nat.bit_lt_two_pow_succ_iff, show (2 : ℕ) ^ 1 = 2 ^ (0 + 1) from rfl,
      Nat.bit_lt_two_pow_succ_iff]
    norm_num
  refine ⟨n, hn64, Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_⟩
  rw [coe_toSL (valid_uP hn64), show (uP n).m = uOf n from rfl, hn, toM_uOf_bits]
  have two : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have hb : ∀ i j, cond (b i j) (1 : ZMod 2) 0 = (u : Matrix (Fin 4) (Fin 4) (ZMod 2)) i j := by
    intro i j
    rcases two ((u : Matrix (Fin 4) (Fin 4) (ZMod 2)) i j) with h | h <;> simp [hbdef, h]
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three] <;>
    first
    | exact (hb _ _).symm
    | exact hl _ _ (by decide)
    | exact hd _

theorem uP_zero : toSL (uP 0) = 1 := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [coe_toSL (valid_uP (by norm_num)), show (uP 0).m = idN by decide +kernel, toM_idN,
    Matrix.SpecialLinearGroup.coe_one]

theorem R1_iff {n : ℕ} (hn : n < 64) (e : Bool) : R1 (toSL (uP n)) e ↔ R1B (uP n) e = true := by
  rw [R1B, Bool.and_eq_true, fixB_iff (valid_uP hn) valid_R2P, fixB_iff (valid_uP hn) valid_M2P]
  rfl

theorem Invol_iff {n : ℕ} (hn : n < 64) (e : Bool) :
    Invol (toSL (uP n)) e ↔ involB (uP n) e = true := by
  have hv := valid_uP hn
  rw [involB, eqB_iff, show toM idN = toM (uP 0).m by decide +kernel,
    toM_eq_iff (hv.mul (hv.gamE e)) (valid_uP (by norm_num)), uP_zero, toSL_mul hv (hv.gamE e),
    toSL_gamE' hv]
  rfl

theorem not_mem_of_sameB {p q : PP} (hp : p.Valid) (hq : q.Valid) (h : sameB p q = false) :
    (toSL p)⁻¹ * toSL q ∉ unitriangular 4 (ZMod 2) := by
  rw [← sameB_iff hp hq, h]
  decide

theorem not_mem_symm {g h : Lin.SLn 4} (hgh : g⁻¹ * h ∉ unitriangular 4 (ZMod 2)) :
    h⁻¹ * g ∉ unitriangular 4 (ZMod 2) := fun hm => hgh (by
  have := inv_mem hm
  rwa [_root_.mul_inv_rev, inv_inv] at this)

theorem four_of_w4 {u : PP} (hu : u.Valid) {e : Bool} {g₁ g₂ g₃ g₄ : PP}
    (h : w4 u e g₁ g₂ g₃ g₄ = true) : Four (toSL u) e := by
  simp only [w4, fsB, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨v₁, -⟩, s₁⟩, ⟨⟨v₂, -⟩, s₂⟩⟩, ⟨⟨v₃, -⟩, s₃⟩⟩, ⟨⟨v₄, -⟩, s₄⟩⟩, d₁₂⟩, d₁₃⟩,
    d₁₄⟩, d₂₃⟩, d₂₄⟩, d₃₄⟩ := h
  have w₁ := valid_of_validB v₁
  have w₂ := valid_of_validB v₂
  have w₃ := valid_of_validB v₃
  have w₄ := valid_of_validB v₄
  have n₁₂ := not_mem_of_sameB w₁ w₂ d₁₂
  have n₁₃ := not_mem_of_sameB w₁ w₃ d₁₃
  have n₁₄ := not_mem_of_sameB w₁ w₄ d₁₄
  have n₂₃ := not_mem_of_sameB w₂ w₃ d₂₃
  have n₂₄ := not_mem_of_sameB w₂ w₄ d₂₄
  have n₃₄ := not_mem_of_sameB w₃ w₄ d₃₄
  exact ⟨toSL g₁, toSL g₂, toSL g₃, toSL g₄, (swapB_iff hu w₁ e).mp s₁,
    (swapB_iff hu w₂ e).mp s₂, (swapB_iff hu w₃ e).mp s₃, (swapB_iff hu w₄ e).mp s₄,
    n₁₂, n₁₃, n₁₄, n₂₃, n₂₄, n₃₄⟩

theorem tr_of_wTr {u : PP} (hu : u.Valid) {e : Bool} {g y : PP} (h : wTr u e g y = true) :
    Tr (toSL u) e := by
  simp only [wTr, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨vg, vy⟩, f₀⟩, f₁⟩, f₂⟩, hc⟩, y₀⟩, y₁⟩, y₂⟩ := h
  have wg := valid_of_validB vg
  have wy := valid_of_validB vy
  have wg₁ := wg.mul valid_R2P
  have wg₂ := wg.mul valid_M2P
  have wz := wy.mul wy
  refine ⟨toSL g, toSL y, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← toSL_act hu e wy, ← toSL_mul wy hu]
    exact (toM_eq_iff (hu.act e wy) (wy.mul hu)).mp ((eqB_iff _ _).mp hc)
  · rw [← fixB_iff hu wg e, f₀]
    decide
  · rw [← toSL_mul wg valid_R2P, ← fixB_iff hu wg₁ e, f₁]
    decide
  · rw [← toSL_mul wg valid_M2P, ← fixB_iff hu wg₂ e, f₂]
    decide
  · rw [← toSL_mul wy wy, ← toSL_mul wz wg, ← sameB_iff wg (wz.mul wg)]
    exact y₀
  · rw [← toSL_mul wy wy, ← toSL_mul wg valid_R2P, ← toSL_mul wz wg₁, ← toSL_mul wg valid_M2P,
      ← sameB_iff wg₂ (wz.mul wg₁)]
    exact y₁
  · rw [← toSL_mul wy wy, ← toSL_mul wg valid_R2P, ← toSL_mul wg valid_M2P,
      ← toSL_mul wz wg₂, ← sameB_iff wg₁ (wz.mul wg₂)]
    exact y₂

theorem one_cases {u : Lin.SLn 4} (hu : u ∈ unitriangular 4 (ZMod 2)) {e : Bool} (hr : R1 u e)
    (hi : Invol u e) (hne : ¬ (u = 1 ∧ e = false)) : Four u e ∨ Tr u e := by
  obtain ⟨n, hn, rfl⟩ := exists_uP hu
  have hv := valid_uP hn
  rcases (chkA_spec hn).2 e ((R1_iff hn e).mp hr) ((Invol_iff hn e).mp hi) with h | hmem
  · exact absurd ⟨h.1 ▸ uP_zero, h.2⟩ hne
  have hB := List.all_eq_true.mp chkB_eq _ hmem
  rw [oneB] at hB
  split at hB
  · split at hB
    · exact Or.inl (four_of_w4 hv hB)
    · exact Or.inr (tr_of_wTr hv hB)
  · exact absurd hB (by simp)

theorem mem_invList {n : ℕ} (hn : n < 64) {e : Bool} (hr : R1 (toSL (uP n)) e)
    (hi : Invol (toSL (uP n)) e) (hne : ¬ (toSL (uP n) = 1 ∧ e = false)) : (n, e) ∈ invList := by
  rcases (chkA_spec hn).2 e ((R1_iff hn e).mp hr) ((Invol_iff hn e).mp hi) with h | hmem
  · exact absurd ⟨h.1 ▸ uP_zero, h.2⟩ hne
  · exact hmem

theorem toSL_mulU {p q : PP} (hp : p.Valid) (hq : q.Valid) (e : Bool) :
    toSL (mulU p e q) = toSL p * gamE e (toSL q) := by
  rw [mulU, toSL_mul hp (hq.gamE e), toSL_gamE' hq]

theorem sel_spec {n₁ n₂ : ℕ} (hn₁ : n₁ < 64) (hn₂ : n₂ < 64) (e₁ e₂ : Bool) {i : ℕ} (hi : i < 3) :
    (sel (n₁, e₁) (n₂, e₂) i).1.Valid ∧
      (toSL (sel (n₁, e₁) (n₂, e₂) i).1, (sel (n₁, e₁) (n₂, e₂) i).2) ∈
        [(toSL (uP n₁), e₁), (toSL (uP n₂), e₂),
          (toSL (uP n₁) * gamE e₁ (toSL (uP n₂)), xor e₁ e₂)] := by
  have v₁ := valid_uP hn₁
  have v₂ := valid_uP hn₂
  interval_cases i
  · exact ⟨v₁, by simp [sel]⟩
  · exact ⟨v₂, by simp [sel]⟩
  · refine ⟨v₁.mul (v₂.gamE e₁), ?_⟩
    simp only [sel]
    rw [toSL_mulU v₁ v₂]
    simp

theorem two_cases {u₁ u₂ : Lin.SLn 4} (hu₁ : u₁ ∈ unitriangular 4 (ZMod 2))
    (hu₂ : u₂ ∈ unitriangular 4 (ZMod 2)) {e₁ e₂ : Bool} (hr₁ : R1 u₁ e₁) (hr₂ : R1 u₂ e₂)
    (hi₁ : Invol u₁ e₁) (hi₂ : Invol u₂ e₂) (hne₁ : ¬ (u₁ = 1 ∧ e₁ = false))
    (hne₂ : ¬ (u₂ = 1 ∧ e₂ = false)) (hne : ¬ (u₁ = u₂ ∧ e₁ = e₂))
    (hc : u₁ * gamE e₁ u₂ = u₂ * gamE e₂ u₁) :
    ∃ c ∈ [(u₁, e₁), (u₂, e₂), (u₁ * gamE e₁ u₂, xor e₁ e₂)],
      ∃ c' ∈ [(u₁, e₁), (u₂, e₂), (u₁ * gamE e₁ u₂, xor e₁ e₂)],
        ∃ g : Lin.SLn 4, Sw c.1 c.2 g ∧ Ne' g (mact c'.1 c'.2 g) := by
  obtain ⟨n₁, hn₁, rfl⟩ := exists_uP hu₁
  obtain ⟨n₂, hn₂, rfl⟩ := exists_uP hu₂
  have v₁ := valid_uP hn₁
  have v₂ := valid_uP hn₂
  have m₁ := mem_invList hn₁ hr₁ hi₁ hne₁
  have m₂ := mem_invList hn₂ hr₂ hi₂ hne₂
  have hne' : (n₁, e₁) ≠ (n₂, e₂) := by
    intro h
    simp only [Prod.mk.injEq] at h
    exact hne ⟨by rw [h.1], h.2⟩
  have hcB : commB (uP n₁) e₁ (uP n₂) e₂ = true := by
    have w₁₂ : (mulU (uP n₁) e₁ (uP n₂)).Valid := v₁.mul (v₂.gamE e₁)
    have w₂₁ : (mulU (uP n₂) e₂ (uP n₁)).Valid := v₂.mul (v₁.gamE e₂)
    rw [commB, eqB_iff, toM_eq_iff w₁₂ w₂₁, toSL_mulU v₁ v₂, toSL_mulU v₂ v₁]
    exact hc
  have hpair : ((n₁, e₁), (n₂, e₂)) ∈ pairs := by
    rw [pairs, List.mem_flatMap]
    refine ⟨(n₁, e₁), m₁, List.mem_filterMap.mpr ⟨(n₂, e₂), m₂, ?_⟩⟩
    have hb : ((n₁, e₁) != (n₂, e₂) && commB (uP (n₁, e₁).1) (n₁, e₁).2 (uP (n₂, e₂).1)
        (n₂, e₂).2) = true := by
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
      exact ⟨hne', hcB⟩
    simp only [hb, ite_true]
  have hC := List.all_eq_true.mp chkC_eq _ hpair
  rw [twoB] at hC
  split at hC
  · rename_i w hw
    simp only [wPair, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hC
    obtain ⟨⟨⟨⟨⟨h₁, h₂⟩, hg⟩, -⟩, hs⟩, hf⟩ := hC
    obtain ⟨vc, mc⟩ := sel_spec hn₁ hn₂ e₁ e₂ h₁
    obtain ⟨vc', mc'⟩ := sel_spec hn₁ hn₂ e₁ e₂ h₂
    have wg := valid_of_validB hg
    refine ⟨_, mc, _, mc', toSL ⟨w.2.2.1, w.2.2.2⟩, (swapB_iff vc wg _).mp hs, ?_⟩
    show (toSL _)⁻¹ * mact _ _ (toSL _) ∉ unitriangular 4 (ZMod 2)
    rw [← fixB_iff vc' wg, hf]
    decide
  · exact absurd hC (by simp)

end CFSG.Quasithin.H13.L32A.C.Levi
