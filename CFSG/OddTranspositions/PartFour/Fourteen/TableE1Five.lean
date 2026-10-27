module

public import CFSG.RankThree.GF2n.Tim79aSec23NoSq
import CFSG.OddTranspositions.SymNoSqE1

public section

namespace CFSG.OddTranspositions.PartFour

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Open Matrix

namespace TableE1Five

variable {n : ℕ}

private theorem fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

attribute [local instance] fact_prime_five

private theorem five_eq_zero : (5 : ZMod 5) = 0 := by decide

private theorem eq_zero_of_two_smul_eq_zero {x : Fin n → ZMod 5} (h : (2 : ZMod 5) • x = 0) :
    x = 0 :=
  (smul_eq_zero.1 h).resolve_left (by decide)

@[expose] def act (g : GL (Fin n) (ZMod 5)) (x : Fin n → ZMod 5) : Fin n → ZMod 5 :=
  (g : Matrix (Fin n) (Fin n) (ZMod 5)) *ᵥ x

@[simp]
theorem act_mul (g h : GL (Fin n) (ZMod 5)) (x : Fin n → ZMod 5) :
    act (g * h) x = act g (act h x) := by
  rw [act, act, act, Units.val_mul, Matrix.mulVec_mulVec]

@[simp]
theorem act_one (x : Fin n → ZMod 5) : act 1 x = x := by
  rw [act, Units.val_one, Matrix.one_mulVec]

@[simp]
theorem act_inv_act (g : GL (Fin n) (ZMod 5)) (x : Fin n → ZMod 5) : act g⁻¹ (act g x) = x := by
  rw [← act_mul, inv_mul_cancel, act_one]

@[simp]
theorem act_act_inv (g : GL (Fin n) (ZMod 5)) (x : Fin n → ZMod 5) : act g (act g⁻¹ x) = x := by
  rw [← act_mul, mul_inv_cancel, act_one]

@[simp]
theorem act_add (g : GL (Fin n) (ZMod 5)) (x y : Fin n → ZMod 5) :
    act g (x + y) = act g x + act g y :=
  Matrix.mulVec_add _ _ _

@[simp]
theorem act_smul (g : GL (Fin n) (ZMod 5)) (c : ZMod 5) (x : Fin n → ZMod 5) :
    act g (c • x) = c • act g x :=
  Matrix.mulVec_smul _ _ _

@[simp]
theorem act_neg (g : GL (Fin n) (ZMod 5)) (x : Fin n → ZMod 5) : act g (-x) = -act g x :=
  Matrix.mulVec_neg _ _

@[simp]
theorem neg_act (g : GL (Fin n) (ZMod 5)) (x : Fin n → ZMod 5) : act (-g) x = -act g x := by
  rw [act, act, Units.val_neg, Matrix.neg_mulVec]

theorem gl_ext {g h : GL (Fin n) (ZMod 5)} (H : ∀ x, act g x = act h x) : g = h :=
  Units.ext (Matrix.ext_of_mulVec_single fun _ => H _)

variable {b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5)}

variable (b) in
@[expose] def reflLin (v : Fin n → ZMod 5) : (Fin n → ZMod 5) →ₗ[ZMod 5] Fin n → ZMod 5 where
  toFun x := x + (-2 * b x v) • v
  map_add' x y := by
    rw [LinearMap.BilinForm.add_left]
    module
  map_smul' c x := by
    rw [LinearMap.BilinForm.smul_left, RingHom.id_apply]
    module

theorem reflLin_apply (v x : Fin n → ZMod 5) : reflLin b v x = x + (-2 * b x v) • v :=
  rfl

variable (b) in
@[expose] noncomputable def reflMat (v : Fin n → ZMod 5) : Matrix (Fin n) (Fin n) (ZMod 5) :=
  LinearMap.toMatrix' (reflLin b v)

theorem reflMat_mulVec (v x : Fin n → ZMod 5) : reflMat b v *ᵥ x = x + (-2 * b x v) • v := by
  rw [reflMat, LinearMap.toMatrix'_mulVec, reflLin_apply]

theorem reflMat_mul_self {v : Fin n → ZMod 5} (hv : b v v = 1) :
    reflMat b v * reflMat b v = 1 := by
  refine Matrix.ext_of_mulVec_single fun i => ?_
  rw [← Matrix.mulVec_mulVec, reflMat_mulVec, reflMat_mulVec, Matrix.one_mulVec,
    LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hv]
  module

variable (b) in
@[expose] noncomputable def refl (v : Fin n → ZMod 5) : GL (Fin n) (ZMod 5) :=
  if h : b v v = 1 then ⟨reflMat b v, reflMat b v, reflMat_mul_self h, reflMat_mul_self h⟩
  else 1

theorem act_refl {v : Fin n → ZMod 5} (hv : b v v = 1) (x : Fin n → ZMod 5) :
    act (refl b v) x = x + (-2 * b x v) • v := by
  rw [act, refl, dif_pos hv]
  exact reflMat_mulVec v x

theorem refl_of_ne {v : Fin n → ZMod 5} (hv : b v v ≠ 1) : refl b v = 1 :=
  dif_neg hv

theorem act_refl_self {v : Fin n → ZMod 5} (hv : b v v = 1) : act (refl b v) v = -v := by
  rw [act_refl hv, hv]
  module

theorem act_refl_of_perp {v x : Fin n → ZMod 5} (hv : b v v = 1) (hx : b x v = 0) :
    act (refl b v) x = x := by
  rw [act_refl hv, hx, mul_zero, zero_smul, add_zero]

theorem ne_zero_of_norm_ne_zero {v : Fin n → ZMod 5} (hv : b v v ≠ 0) : v ≠ 0 := by
  rintro rfl
  exact hv (by simp)

@[simp]
theorem refl_mul_self (v : Fin n → ZMod 5) : refl b v * refl b v = 1 := by
  by_cases hv : b v v = 1
  · exact Units.ext (by
      rw [Units.val_mul, refl, dif_pos hv]
      exact reflMat_mul_self hv)
  · rw [refl_of_ne hv, one_mul]

@[simp]
theorem refl_inv (v : Fin n → ZMod 5) : (refl b v)⁻¹ = refl b v :=
  inv_eq_of_mul_eq_one_right (refl_mul_self v)

theorem refl_neg (v : Fin n → ZMod 5) : refl b (-v) = refl b v := by
  have hn : b (-v) (-v) = b v v := by simp
  by_cases hv : b v v = 1
  · refine gl_ext fun x => ?_
    rw [act_refl (hn.trans hv), act_refl hv, LinearMap.BilinForm.neg_right]
    module
  · rw [refl_of_ne hv, refl_of_ne (hn ▸ hv)]

theorem refl_eq_refl_iff {v w : Fin n → ZMod 5} (hv : b v v = 1) (hw : b w w = 1) :
    refl b v = refl b w ↔ w = v ∨ w = -v := by
  constructor
  · intro h
    have h1 : act (refl b v) v = act (refl b w) v := by rw [h]
    rw [act_refl_self hv, act_refl hw] at h1
    have h2 : v = b v w • w := by
      have : (2 : ZMod 5) • (v - b v w • w) = 0 := by linear_combination (norm := module) -h1
      exact sub_eq_zero.1 (eq_zero_of_two_smul_eq_zero this)
    have hc : b v w * b v w = 1 := by
      have := hv
      rw [h2, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hw] at this
      rw [← this]
      ring
    have hc' : b v w = 1 ∨ b v w = -1 := by
      revert hc; generalize b v w = c; revert c; decide
    rcases hc' with hc' | hc'
    · left; rw [h2, hc', one_smul]
    · right; rw [h2, hc', neg_one_smul, neg_neg]
  · rintro (rfl | rfl)
    · rfl
    · exact (refl_neg v).symm

theorem refl_comm_of_perp (hsym : ∀ x y, b x y = b y x) {v w : Fin n → ZMod 5}
    (hvw : b v w = 0) : refl b v * refl b w = refl b w * refl b v := by
  have hwv : b w v = 0 := by rw [hsym]; exact hvw
  by_cases hv : b v v = 1
  · by_cases hw : b w w = 1
    · refine gl_ext fun x => ?_
      simp only [act_mul, act_refl hv, act_refl hw, LinearMap.BilinForm.add_left,
        LinearMap.BilinForm.smul_left, hvw, hwv, mul_zero, add_zero]
      abel
    · rw [refl_of_ne hw, mul_one, one_mul]
  · rw [refl_of_ne hv, mul_one, one_mul]

variable (b) in
@[expose] def isomGroup : Subgroup (GL (Fin n) (ZMod 5)) where
  carrier := {g | ∀ x y, b (act g x) (act g y) = b x y}
  mul_mem' {g h} hg hh x y := by
    rw [act_mul, act_mul, hg (act h x) (act h y), hh x y]
  one_mem' x y := by rw [act_one, act_one]
  inv_mem' {g} hg x y := by
    rw [← hg (act g⁻¹ x) (act g⁻¹ y), act_act_inv, act_act_inv]

theorem mem_isomGroup {g : GL (Fin n) (ZMod 5)} :
    g ∈ isomGroup b ↔ ∀ x y, b (act g x) (act g y) = b x y :=
  Iff.rfl

theorem isom_norm {g : GL (Fin n) (ZMod 5)} (hg : g ∈ isomGroup b) (x : Fin n → ZMod 5) :
    b (act g x) (act g x) = b x x :=
  hg x x

theorem isom_inv_left {g : GL (Fin n) (ZMod 5)} (hg : g ∈ isomGroup b) (x y : Fin n → ZMod 5) :
    b (act g⁻¹ x) y = b x (act g y) := by
  rw [← hg (act g⁻¹ x) y, act_act_inv]

theorem refl_mem_isomGroup (hsym : ∀ x y, b x y = b y x) (v : Fin n → ZMod 5) :
    refl b v ∈ isomGroup b := by
  by_cases hv : b v v = 1
  · intro x y
    rw [act_refl hv, act_refl hv]
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hv, hsym v y]
    ring
  · rw [refl_of_ne hv]
    exact (isomGroup b).one_mem

theorem conj_refl {g : GL (Fin n) (ZMod 5)} (hg : g ∈ isomGroup b) (v : Fin n → ZMod 5) :
    g * refl b v * g⁻¹ = refl b (act g v) := by
  by_cases hv : b v v = 1
  · refine gl_ext fun x => ?_
    rw [act_mul, act_mul, act_refl hv, act_refl (by rw [isom_norm hg, hv]), act_add, act_act_inv,
      act_smul, isom_inv_left hg]
  · rw [refl_of_ne hv, refl_of_ne (by rwa [isom_norm hg]), mul_one, mul_inv_cancel]

theorem act_eq_or_of_commute {g : GL (Fin n) (ZMod 5)} (hg : g ∈ isomGroup b)
    {v : Fin n → ZMod 5} (hv : b v v = 1) (hc : refl b v * g = g * refl b v) :
    act g v = v ∨ act g v = -v := by
  have h1 : g * refl b v * g⁻¹ = refl b v := by rw [← hc, mul_assoc, mul_inv_cancel, mul_one]
  rw [conj_refl hg, refl_eq_refl_iff (by rw [isom_norm hg, hv]) hv] at h1
  rcases h1 with h1 | h1
  · exact Or.inl h1.symm
  · exact Or.inr (neg_eq_iff_eq_neg.mp h1.symm)

private theorem pow_three_of_braid {H : Type*} [Group H] {a c : H} (ha : a * a = 1) (hc : c * c = 1)
    (h : a * c * a = c * a * c) : (a * c) ^ 3 = 1 := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hc' : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  calc (a * c) ^ 3 = (a * c * a) * (c * a * c) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = (c * a * c) * (c⁻¹ * a⁻¹ * c⁻¹) := by rw [h, ha', hc']
    _ = 1 := by group

private theorem pow_five_of_braid {H : Type*} [Group H] {a c : H} (ha : a * a = 1) (hc : c * c = 1)
    (h : a * c * a * c * a = c * a * c * a * c) : (a * c) ^ 5 = 1 := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hc' : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  calc (a * c) ^ 5 = (a * c * a * c * a) * (c * a * c * a * c) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = (c * a * c * a * c) * (c⁻¹ * a⁻¹ * c⁻¹ * a⁻¹ * c⁻¹) := by rw [h, ha', hc']
    _ = 1 := by group

theorem refl_mul_refl_pow_fifteen (hsym : ∀ x y, b x y = b y x) {v w : Fin n → ZMod 5}
    (hv : b v v = 1) (hw : b w w = 1) (hvw : b v w ≠ 0) : (refl b v * refl b w) ^ 15 = 1 := by
  have hwv : b w v = b v w := hsym w v
  have hiv := refl_mem_isomGroup hsym v
  have hiw := refl_mem_isomGroup hsym w
  have e3 : ∀ {x y : Fin n → ZMod 5}, refl b x ∈ isomGroup b →
      refl b x * refl b y * refl b x = refl b (act (refl b x) y) := fun hx => by
    rw [← conj_refl hx, refl_inv]
  have e5 : ∀ {x y : Fin n → ZMod 5}, refl b x * refl b y ∈ isomGroup b →
      refl b x * refl b y * refl b x * refl b y * refl b x =
        refl b (act (refl b x * refl b y) x) := fun hxy => by
    rw [← conj_refl hxy, _root_.mul_inv_rev, refl_inv, refl_inv]
    group
  have h5 : refl b v * refl b w * refl b v * refl b w * refl b v =
      refl b w * refl b v * refl b w * refl b v * refl b w → (refl b v * refl b w) ^ 15 = 1 :=
    fun hb => by
      rw [show (15 : ℕ) = 5 * 3 by norm_num, pow_mul,
        pow_five_of_braid (refl_mul_self v) (refl_mul_self w) hb, one_pow]
  have h3 : refl b v * refl b w * refl b v = refl b w * refl b v * refl b w →
      (refl b v * refl b w) ^ 15 = 1 := fun hb => by
    rw [show (15 : ℕ) = 3 * 5 by norm_num, pow_mul,
      pow_three_of_braid (refl_mul_self v) (refl_mul_self w) hb, one_pow]
  have hc : b v w = 1 ∨ b v w = 4 ∨ b v w = 2 ∨ b v w = 3 := by
    revert hvw; generalize b v w = c; revert c; decide
  rcases hc with hc | hc | hc | hc
  ·
    refine h5 ?_
    rw [e5 ((isomGroup b).mul_mem hiv hiw), e5 ((isomGroup b).mul_mem hiw hiv)]
    congr 1
    simp only [act_mul, act_refl hv, act_refl hw, LinearMap.BilinForm.add_left,
      LinearMap.BilinForm.smul_left, hv, hw, hwv, hc]
    linear_combination (norm := module) five_eq_zero • (v - w)
  ·
    refine h5 ?_
    rw [e5 ((isomGroup b).mul_mem hiv hiw), e5 ((isomGroup b).mul_mem hiw hiv),
      ← refl_neg (act (refl b w * refl b v) w)]
    congr 1
    simp only [act_mul, act_refl hv, act_refl hw, LinearMap.BilinForm.add_left,
      LinearMap.BilinForm.smul_left, hv, hw, hwv, hc]
    linear_combination (norm := module) five_eq_zero • ((11 : ZMod 5) • (v + w))
  ·
    refine h3 ?_
    rw [e3 hiv, e3 hiw]
    congr 1
    rw [act_refl hv, act_refl hw, hwv, hc]
    linear_combination (norm := module) five_eq_zero • (w - v)
  ·
    refine h3 ?_
    rw [e3 hiv, e3 hiw, ← refl_neg (act (refl b w) v)]
    congr 1
    rw [act_refl hv, act_refl hw, hwv, hc]
    linear_combination (norm := module) five_eq_zero • (-v - w)

variable (b) in
abbrev reflSet : Set (GL (Fin n) (ZMod 5)) :=
  fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1

variable (b) in
abbrev reflGroup : Subgroup (GL (Fin n) (ZMod 5)) :=
  Subgroup.closure (reflSet b)

theorem refl_mem_reflSet {v : Fin n → ZMod 5} (hv : b v v = 1) : refl b v ∈ reflSet b :=
  ⟨v, hv, act_refl hv⟩

theorem mem_reflSet_iff {g : GL (Fin n) (ZMod 5)} :
    g ∈ reflSet b ↔ ∃ v, b v v = 1 ∧ refl b v = g := by
  constructor
  · rintro ⟨v, hv, hg⟩
    exact ⟨v, hv, gl_ext fun x => by rw [act_refl hv]; exact (hg x).symm⟩
  · rintro ⟨v, hv, rfl⟩
    exact refl_mem_reflSet hv

theorem refl_mem_reflGroup (v : Fin n → ZMod 5) : refl b v ∈ reflGroup b := by
  by_cases hv : b v v = 1
  · exact Subgroup.subset_closure (refl_mem_reflSet hv)
  · rw [refl_of_ne hv]
    exact Subgroup.one_mem _

theorem reflGroup_le_isomGroup (hsym : ∀ x y, b x y = b y x) : reflGroup b ≤ isomGroup b := by
  rw [Subgroup.closure_le]
  intro g hg
  obtain ⟨v, -, rfl⟩ := mem_reflSet_iff.1 hg
  exact refl_mem_isomGroup hsym v

theorem exists_ne_zero_perp {k : ℕ} (hk : k < n) (u : Fin k → Fin n → ZMod 5) :
    ∃ y, y ≠ 0 ∧ ∀ i, b y (u i) = 0 := by
  let L : (Fin n → ZMod 5) →ₗ[ZMod 5] Fin k → ZMod 5 := LinearMap.pi fun i => b.flip (u i)
  have h := LinearMap.ker_ne_bot_of_finrank_lt (f := L) (by simpa using hk)
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 h
  exact ⟨y, hy0, fun i => congrFun (LinearMap.mem_ker.1 hy) i⟩

theorem exists_aniso_perp (hsym : ∀ x y, b x y = b y x) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    {k : ℕ} (hk : k < n) (u : Fin k → Fin n → ZMod 5)
    (horth : ∀ i j, i ≠ j → b (u i) (u j) = 0) (hanis : ∀ i, b (u i) (u i) ≠ 0) :
    ∃ z, (∀ i, b z (u i) = 0) ∧ b z z ≠ 0 := by
  obtain ⟨z₀, hz₀, hz₀u⟩ := exists_ne_zero_perp (b := b) hk u
  by_cases h0 : b z₀ z₀ = 0
  swap
  · exact ⟨z₀, hz₀u, h0⟩
  obtain ⟨y, hy⟩ : ∃ y, b z₀ y ≠ 0 := by
    by_contra! h
    exact hz₀ (hnd z₀ h)
  obtain ⟨y', hy'⟩ : ∃ y', y' = y - ∑ i, (b y (u i) * (b (u i) (u i))⁻¹) • u i := ⟨_, rfl⟩
  have hy'u : ∀ j, b y' (u j) = 0 := by
    intro j
    rw [hy', LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sum_left,
      Finset.sum_eq_single j (fun i _ hij => by
        rw [LinearMap.BilinForm.smul_left, horth i j hij, mul_zero])
        (fun h => absurd (Finset.mem_univ j) h),
      LinearMap.BilinForm.smul_left, mul_assoc, inv_mul_cancel₀ (hanis j), mul_one, sub_self]
  have hz₀y' : b z₀ y' = b z₀ y := by
    rw [hy', LinearMap.BilinForm.sub_right, LinearMap.BilinForm.sum_right,
      Finset.sum_eq_zero (fun i _ => by rw [LinearMap.BilinForm.smul_right, hz₀u i, mul_zero]),
      sub_zero]
  by_cases h1 : b y' y' = 0
  · refine ⟨z₀ + y', fun i => by rw [LinearMap.BilinForm.add_left, hz₀u i, hy'u i, add_zero], ?_⟩
    rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.add_right, h0, h1, hsym y' z₀, hz₀y']
    rw [show (0 : ZMod 5) + b z₀ y + (b z₀ y + 0) = 2 * b z₀ y by ring]
    exact mul_ne_zero (by decide) hy
  · exact ⟨y', hy'u, h1⟩

theorem exists_aniso_perp₂ (hsym : ∀ x y, b x y = b y x) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hn : 3 ≤ n) {u₁ u₂ : Fin n → ZMod 5} (h₁ : b u₁ u₁ ≠ 0) (h₂ : b u₂ u₂ ≠ 0)
    (h₁₂ : b u₁ u₂ = 0) : ∃ z, b z u₁ = 0 ∧ b z u₂ = 0 ∧ b z z ≠ 0 := by
  have h₂₁ : b u₂ u₁ = 0 := by rw [hsym]; exact h₁₂
  obtain ⟨z, hz, hzz⟩ := exists_aniso_perp hsym hnd (k := 2) (by omega) ![u₁, u₂]
    (fun i j hij => by
      fin_cases i <;> fin_cases j
      all_goals first | exact absurd rfl hij | simp [h₁₂, h₂₁])
    (fun i => by fin_cases i <;> simp [h₁, h₂])
  exact ⟨z, by simpa using hz 0, by simpa using hz 1, hzz⟩

theorem exists_aniso_perp₃ (hsym : ∀ x y, b x y = b y x) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hn : 4 ≤ n) {u₁ u₂ u₃ : Fin n → ZMod 5} (h₁ : b u₁ u₁ ≠ 0) (h₂ : b u₂ u₂ ≠ 0)
    (h₃ : b u₃ u₃ ≠ 0) (h₁₂ : b u₁ u₂ = 0) (h₁₃ : b u₁ u₃ = 0) (h₂₃ : b u₂ u₃ = 0) :
    ∃ z, b z u₁ = 0 ∧ b z u₂ = 0 ∧ b z u₃ = 0 ∧ b z z ≠ 0 := by
  have h₂₁ : b u₂ u₁ = 0 := by rw [hsym]; exact h₁₂
  have h₃₁ : b u₃ u₁ = 0 := by rw [hsym]; exact h₁₃
  have h₃₂ : b u₃ u₂ = 0 := by rw [hsym]; exact h₂₃
  obtain ⟨z, hz, hzz⟩ := exists_aniso_perp hsym hnd (k := 3) (by omega) ![u₁, u₂, u₃]
    (fun i j hij => by
      fin_cases i <;> fin_cases j
      all_goals first | exact absurd rfl hij | simp [h₁₂, h₂₁, h₁₃, h₃₁, h₂₃, h₃₂])
    (fun i => by fin_cases i <;> simp [h₁, h₂, h₃])
  exact ⟨z, by simpa using hz 0, by simpa using hz 1, by simpa using hz 2, hzz⟩

theorem exists_norm_eq_perp (hsym : ∀ x y, b x y = b y x) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hn : 3 ≤ n) {v : Fin n → ZMod 5} (hv : b v v ≠ 0) {c : ZMod 5} (hc : c ≠ 0) :
    ∃ x, b x v = 0 ∧ b x x = c := by
  obtain ⟨z₁, hz₁, hz₁z₁⟩ := exists_aniso_perp hsym hnd (k := 1) (by omega) ![v]
    (fun i j hij => absurd (Subsingleton.elim i j) hij) (fun i => by fin_cases i; simpa using hv)
  have hz₁v : b z₁ v = 0 := by simpa using hz₁ 0
  obtain ⟨z₂, hz₂v, hz₂z₁, hz₂z₂⟩ := exists_aniso_perp₂ hsym hnd hn hv hz₁z₁
    (by rw [hsym]; exact hz₁v)
  have key : ∀ a d t : ZMod 5, a ≠ 0 → d ≠ 0 → t ≠ 0 →
      ∃ l m : ZMod 5, l * l * a + m * m * d = t := by decide
  obtain ⟨l, m, hlm⟩ := key _ _ _ hz₁z₁ hz₂z₂ hc
  refine ⟨l • z₁ + m • z₂, ?_, ?_⟩
  · rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.smul_left, hz₁v, hz₂v, mul_zero, mul_zero, add_zero]
  · simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hz₂z₁, hsym z₁ z₂]
    rw [← hlm]
    ring

private theorem exists_norm_one_not_fixed (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 3 ≤ n) {v : Fin n → ZMod 5} (hv : b v v = 1) :
    ∃ w, b w w = 1 ∧ act (refl b v) w ≠ w ∧ act (refl b v) w ≠ -w := by
  obtain ⟨s, hsv, hss⟩ := exists_norm_eq_perp hsym hnd hn (v := v) (by rw [hv]; decide)
    (c := 2) (by decide)
  have hvs : b v s = 0 := by rw [hsym]; exact hsv
  have hwv : b ((2 : ZMod 5) • v + s) v = 2 := by
    rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hv, hsv]
    decide
  have hws : b ((2 : ZMod 5) • v + s) s = 2 := by
    rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hvs, hss]
    decide
  refine ⟨(2 : ZMod 5) • v + s, ?_, ?_, ?_⟩
  · rw [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, hwv, hws]
    decide
  · intro h
    have h1 := congrArg (fun x => b x v) h
    simp only [act_refl hv, LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left,
      hwv, hv] at h1
    revert h1
    decide
  · intro h
    have h1 := congrArg (fun x => b x s) h
    simp only [act_refl hv, LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.neg_left, hwv, hws, hvs] at h1
    revert h1
    decide

private theorem exists_norm_one_perp_ne_ne (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 4 ≤ n) {v w₁ w₂ : Fin n → ZMod 5}
    (hv : b v v = 1) (hw₁ : b w₁ w₁ = 1) (hw₂ : b w₂ w₂ = 1) (hw₁v : b w₁ v = 0)
    (hw₂v : b w₂ v = 0) (hw₁w₂ : b w₁ w₂ = 0) :
    ∃ x, b x x = 1 ∧ b x v = 0 ∧ b x w₁ ≠ 0 ∧ b x w₂ ≠ 0 := by
  obtain ⟨z, hzv, hzw₁, hzw₂, hzz⟩ := exists_aniso_perp₃ hsym hnd hn
    (by rw [hv]; decide) (by rw [hw₁]; decide) (by rw [hw₂]; decide)
    (by rw [hsym]; exact hw₁v) (by rw [hsym]; exact hw₂v) hw₁w₂
  have key : ∀ β : ZMod 5, β ≠ 0 → ∃ α γ δ : ZMod 5, α ≠ 0 ∧ γ ≠ 0 ∧
      α * α + γ * γ + δ * δ * β = 1 := by decide
  obtain ⟨α, γ, δ, hα, hγ, hsum⟩ := key _ hzz
  refine ⟨α • w₁ + γ • w₂ + δ • z, ?_, ?_, ?_, ?_⟩
  · simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hw₁, hw₂, hw₁w₂,
      hsym w₂ w₁, hzw₁, hzw₂, hsym w₁ z, hsym w₂ z]
    linear_combination hsum
  · simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hw₁v, hw₂v, hzv]
    ring
  · simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hw₁, hsym w₂ w₁,
      hw₁w₂, hzw₁]
    rw [show α * 1 + γ * 0 + δ * 0 = α by ring]
    exact hα
  · simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hw₂, hw₁w₂, hzw₂]
    rw [show α * 0 + γ * 1 + δ * 0 = γ by ring]
    exact hγ

theorem eq_zero_of_forall_norm_one_perp (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 3 ≤ n) {v u : Fin n → ZMod 5} (hv : b v v = 1)
    (huv : b u v = 0) (hu : ∀ w, b w w = 1 → b w v = 0 → b u w = 0) : u = 0 := by
  obtain ⟨w₁, hw₁v, hw₁⟩ := exists_norm_eq_perp hsym hnd hn (v := v) (by rw [hv]; decide)
    (c := 1) one_ne_zero
  have huw₁ : b u w₁ = 0 := hu w₁ hw₁ hw₁v
  have hvw₁ : b v w₁ = 0 := by rw [hsym]; exact hw₁v
  have key : ∀ a : ZMod 5, ∃ l m : ZMod 5, m ≠ 0 ∧ l * l + m * m * a = 1 := by decide
  apply hnd
  intro x
  obtain ⟨x', hx'⟩ : ∃ x', x' = x - b x v • v - b x w₁ • w₁ := ⟨_, rfl⟩
  have hx'v : b x' v = 0 := by
    simp only [hx', LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hv, hw₁v]
    ring
  have hx'w₁ : b x' w₁ = 0 := by
    simp only [hx', LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hw₁, hvw₁]
    ring
  have hux' : b u x' = 0 := by
    obtain ⟨l, m, hm, hlm⟩ := key (b x' x')
    have h := hu (l • w₁ + m • x') (by
      simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
        LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hw₁, hx'w₁,
        hsym w₁ x']
      linear_combination hlm) (by
      simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hw₁v, hx'v]
      ring)
    rw [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right,
      LinearMap.BilinForm.smul_right, huw₁, mul_zero, zero_add] at h
    exact (mul_eq_zero.1 h).resolve_left hm
  have hx : x = x' + b x v • v + b x w₁ • w₁ := by rw [hx']; abel
  rw [hx, LinearMap.BilinForm.add_right, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.smul_right, LinearMap.BilinForm.smul_right, hux', huv, huw₁]
  ring

theorem refl_ne_neg_refl (hn : 3 ≤ n) (v w : Fin n → ZMod 5) : refl b w ≠ -refl b v := by
  intro h
  obtain ⟨y, hy0, hy⟩ := exists_ne_zero_perp (b := b) (k := 2) (by omega) ![v, w]
  have hyv : b y v = 0 := by simpa using hy 0
  have hyw : b y w = 0 := by simpa using hy 1
  have h1 : act (refl b w) y = y := by
    by_cases hw : b w w = 1
    · exact act_refl_of_perp hw hyw
    · rw [refl_of_ne hw, act_one]
  have h2 : act (refl b v) y = y := by
    by_cases hv : b v v = 1
    · exact act_refl_of_perp hv hyv
    · rw [refl_of_ne hv, act_one]
  rw [h, neg_act, h2] at h1
  exact hy0 (eq_zero_of_two_smul_eq_zero (by linear_combination (norm := module) -h1))

theorem act_perp {g : GL (Fin n) (ZMod 5)} (hg : g ∈ isomGroup b) {v x : Fin n → ZMod 5}
    (hgv : act g v = v ∨ act g v = -v) (hx : b x v = 0) : b (act g x) v = 0 := by
  rcases hgv with h | h
  · rw [← hx, ← hg x v, h]
  · rw [← neg_eq_zero, ← LinearMap.BilinForm.neg_right, ← h, hg x v, hx]

theorem exists_smul_on_perp (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 4 ≤ n) {v : Fin n → ZMod 5} (hv : b v v = 1)
    {g : GL (Fin n) (ZMod 5)} (hg : g ∈ isomGroup b) (hgv : act g v = v ∨ act g v = -v)
    (h : ∀ w, b w w = 1 → b w v = 0 → act g w = w ∨ act g w = -w) :
    ∃ ε : ZMod 5, ε * ε = 1 ∧ ∀ x, b x v = 0 → act g x = ε • x := by
  have mixed : ∀ w₁ w₂, b w₁ w₁ = 1 → b w₂ w₂ = 1 → b w₁ v = 0 → b w₂ v = 0 →
      b w₁ w₂ ≠ 0 → act g w₁ = w₁ → act g w₂ = -w₂ → False := by
    intro w₁ w₂ hw₁ hw₂ hw₁v hw₂v hw₁w₂ h1 h2
    have hu : b (act (refl b w₁) w₂) (act (refl b w₁) w₂) = 1 := by
      rw [isom_norm (refl_mem_isomGroup hsym w₁), hw₂]
    have huv : b (act (refl b w₁) w₂) v = 0 := by
      rw [act_refl hw₁, LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hw₂v, hw₁v,
        mul_zero, add_zero]
    have hgu : act g (act (refl b w₁) w₂) = -w₂ + (-2 * b w₂ w₁) • w₁ := by
      rw [act_refl hw₁, act_add, act_smul, h1, h2]
    rcases h _ hu huv with h3 | h3 <;> rw [hgu, act_refl hw₁] at h3
    · have h4 : (2 : ZMod 5) • w₂ = 0 := by linear_combination (norm := module) -h3
      exact ne_zero_of_norm_ne_zero (b := b) (by rw [hw₂]; decide)
        (eq_zero_of_two_smul_eq_zero h4)
    · have h4 : (2 : ZMod 5) • ((-2 * b w₂ w₁) • w₁) = 0 := by
        linear_combination (norm := module) h3
      rcases smul_eq_zero.1 (eq_zero_of_two_smul_eq_zero h4) with h5 | h5
      · exact hw₁w₂ (by rw [hsym]; exact (mul_eq_zero.1 h5).resolve_left (by decide))
      · exact ne_zero_of_norm_ne_zero (b := b) (by rw [hw₁]; decide) h5
  have agree₁ : ∀ w₁ w₂, b w₁ w₁ = 1 → b w₂ w₂ = 1 → b w₁ v = 0 → b w₂ v = 0 →
      b w₁ w₂ ≠ 0 → (act g w₁ = w₁ ↔ act g w₂ = w₂) := by
    intro w₁ w₂ hw₁ hw₂ hw₁v hw₂v hw₁w₂
    constructor
    · intro h1
      rcases h w₂ hw₂ hw₂v with h2 | h2
      · exact h2
      · exact (mixed w₁ w₂ hw₁ hw₂ hw₁v hw₂v hw₁w₂ h1 h2).elim
    · intro h2
      rcases h w₁ hw₁ hw₁v with h1 | h1
      · exact h1
      · exact (mixed w₂ w₁ hw₂ hw₁ hw₂v hw₁v (by rwa [hsym]) h2 h1).elim
  have agree : ∀ w₁ w₂, b w₁ w₁ = 1 → b w₂ w₂ = 1 → b w₁ v = 0 → b w₂ v = 0 →
      (act g w₁ = w₁ ↔ act g w₂ = w₂) := by
    intro w₁ w₂ hw₁ hw₂ hw₁v hw₂v
    by_cases hw₁w₂ : b w₁ w₂ = 0
    · obtain ⟨x, hx, hxv, hxw₁, hxw₂⟩ :=
        exists_norm_one_perp_ne_ne hsym hnd hn hv hw₁ hw₂ hw₁v hw₂v hw₁w₂
      exact (agree₁ w₁ x hw₁ hx hw₁v hxv (by rwa [hsym])).trans
        (agree₁ x w₂ hx hw₂ hxv hw₂v hxw₂)
    · exact agree₁ w₁ w₂ hw₁ hw₂ hw₁v hw₂v hw₁w₂
  have key : ∀ ε : ZMod 5, ε * ε = 1 → (∀ w, b w w = 1 → b w v = 0 → act g w = ε • w) →
      ∀ x, b x v = 0 → act g x = ε • x := by
    intro ε hε hall x hxv
    refine sub_eq_zero.1 (eq_zero_of_forall_norm_one_perp hsym hnd (by omega) hv ?_ ?_)
    · rw [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, act_perp hg hgv hxv, hxv,
        mul_zero, sub_zero]
    · intro w hw hwv
      have hw' : w = ε • act g w := by rw [hall w hw hwv, smul_smul, hε, one_smul]
      have h1 : b (act g x) w = ε * b x w := by
        calc b (act g x) w = b (act g x) (ε • act g w) := by rw [← hw']
          _ = ε * b x w := by rw [LinearMap.BilinForm.smul_right, hg x w]
      rw [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, h1, sub_self]
  obtain ⟨w₀, hw₀v, hw₀⟩ := exists_norm_eq_perp hsym hnd (by omega) (v := v)
    (by rw [hv]; decide) (c := 1) one_ne_zero
  by_cases h0 : act g w₀ = w₀
  · refine ⟨1, by decide, key 1 (by decide) fun w hw hwv => ?_⟩
    rw [one_smul]
    exact (agree w₀ w hw₀ hw hw₀v hwv).1 h0
  · refine ⟨-1, by decide, key (-1) (by decide) fun w hw hwv => ?_⟩
    rw [neg_one_smul]
    rcases h w hw hwv with h1 | h1
    · exact absurd ((agree w₀ w hw₀ hw hw₀v hwv).2 h1) h0
    · exact h1

theorem eq_four_of_forall_perp (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 4 ≤ n) {v : Fin n → ZMod 5} (hv : b v v = 1)
    {g : GL (Fin n) (ZMod 5)} (hg : g ∈ isomGroup b) (hgv : act g v = v ∨ act g v = -v)
    (h : ∀ w, b w w = 1 → b w v = 0 → act g w = w ∨ act g w = -w) :
    g = 1 ∨ g = -1 ∨ g = refl b v ∨ g = -refl b v := by
  obtain ⟨ε, hε, hε'⟩ := exists_smul_on_perp hsym hnd hn hv hg hgv h
  have hε1 : ε = 1 ∨ ε = -1 := by
    revert hε; generalize ε = c; revert c; decide
  have hgx : ∀ x, act g x = ε • (x - b x v • v) + b x v • act g v := fun x => by
    have hx : b (x - b x v • v) v = 0 := by
      rw [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hv, mul_one, sub_self]
    rw [← hε' _ hx, ← act_smul, ← act_add, sub_add_cancel]
  rcases hε1 with rfl | rfl <;> rcases hgv with h1 | h1
  · left
    exact gl_ext fun x => by rw [hgx, h1, act_one]; module
  · right; right; left
    exact gl_ext fun x => by rw [hgx, h1, act_refl hv]; module
  · right; right; right
    exact gl_ext fun x => by rw [hgx, h1, neg_act, act_refl hv]; module
  · right; left
    exact gl_ext fun x => by rw [hgx, h1, neg_act, act_one]; module

theorem coe_eq_of_mem_center (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 4 ≤ n) {v : Fin n → ZMod 5} (hv : b v v = 1)
    {g : reflGroup b} (hg : g ∈ Subgroup.center (reflGroup b)) :
    (g : GL (Fin n) (ZMod 5)) = 1 ∨ (g : GL (Fin n) (ZMod 5)) = -1 := by
  have hiso : (g : GL (Fin n) (ZMod 5)) ∈ isomGroup b := reflGroup_le_isomGroup hsym g.2
  have hcomm : ∀ w, b w w = 1 → act g w = w ∨ act g w = -w := fun w hw =>
    act_eq_or_of_commute hiso hw (congrArg Subtype.val
      (Subgroup.mem_center_iff.1 hg ⟨refl b w, refl_mem_reflGroup w⟩))
  obtain ⟨w, hw, hw1, hw2⟩ := exists_norm_one_not_fixed hsym hnd (by omega) hv
  rcases eq_four_of_forall_perp hsym hnd hn hv hiso (hcomm v hv) (fun w hw _ => hcomm w hw)
    with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · rcases hcomm w hw with h3 | h3 <;> rw [h] at h3
    · exact absurd h3 hw1
    · exact absurd h3 hw2
  · rcases hcomm w hw with h3 | h3 <;> rw [h, neg_act] at h3
    · exact absurd (neg_eq_iff_eq_neg.mp h3) hw2
    · exact absurd (neg_inj.mp h3) hw1

private theorem eq_one_of_pow_two_pow_of_pow_fifteen {H : Type*} [Monoid H] {x : H} {k : ℕ}
    (hk : x ^ 2 ^ k = 1) (h15 : x ^ 15 = 1) : x = 1 := by
  have hc : Nat.Coprime 15 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h15) (orderOf_dvd_of_pow_eq_one hk)
  rwa [hc.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at hd

theorem eq_four_of_mem (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 4 ≤ n) {v : Fin n → ZMod 5} (hv : b v v = 1)
    (S : Set (GL (Fin n) (ZMod 5))) (hS1 : ∀ g ∈ S, g ∈ isomGroup b)
    (hS2 : ∀ g ∈ S, ∃ k : ℕ, g ^ 2 ^ k = 1)
    (hS3 : ∀ g ∈ S, ∀ w, b w w = 1 → b w v = 0 → refl b w * g * refl b w ∈ S)
    (hS4 : ∀ g ∈ S, ∀ h ∈ S, g * h⁻¹ ∈ S) (hS5 : ∀ g ∈ S, act g v = v ∨ act g v = -v) :
    ∀ g ∈ S, g = 1 ∨ g = -1 ∨ g = refl b v ∨ g = -refl b v := by
  have hcomm : ∀ g ∈ S, ∀ w, b w w = 1 → b w v = 0 → refl b w * refl b (act g w) ∈ S := by
    intro g hg w hw hwv
    have := hS4 _ (hS3 g hg w hw hwv) g hg
    rwa [mul_assoc (refl b w) g (refl b w), mul_assoc (refl b w) (g * refl b w) g⁻¹,
      conj_refl (hS1 g hg)] at this
  have step1 : ∀ g ∈ S, ∀ w, b w w = 1 → b w v = 0 → b w (act g w) ≠ 0 →
      act g w = w ∨ act g w = -w := by
    intro g hg w hw hwv hne
    have hw' : b (act g w) (act g w) = 1 := by rw [isom_norm (hS1 g hg), hw]
    obtain ⟨k, hk⟩ := hS2 _ (hcomm g hg w hw hwv)
    have h1 := eq_one_of_pow_two_pow_of_pow_fifteen hk (refl_mul_refl_pow_fifteen hsym hw hw' hne)
    have h2 : refl b w = refl b (act g w) := by
      calc refl b w = refl b w * (refl b (act g w) * refl b (act g w)) := by
            rw [refl_mul_self, mul_one]
        _ = refl b (act g w) := by rw [← mul_assoc, h1, one_mul]
    exact (refl_eq_refl_iff hw hw').1 h2
  have step2 : ∀ g ∈ S, ∀ w, b w w = 1 → b w v = 0 → b w (act g w) ≠ 0 := by
    intro g hg w hw hwv h0
    obtain ⟨w', hw'def⟩ : ∃ w', w' = act g w := ⟨_, rfl⟩
    rw [← hw'def] at h0
    have hw' : b w' w' = 1 := by rw [hw'def, isom_norm (hS1 g hg), hw]
    have hw'v : b w' v = 0 := by rw [hw'def]; exact act_perp (hS1 g hg) (hS5 g hg) hwv
    have hw'w : b w' w = 0 := by rw [hsym]; exact h0
    have hc : refl b w * refl b w' ∈ S := by rw [hw'def]; exact hcomm g hg w hw hwv
    obtain ⟨z, hzv, hzw, hzw', hzz⟩ := exists_aniso_perp₃ hsym hnd hn
      (by rw [hv]; decide) (by rw [hw]; decide) (by rw [hw']; decide)
      (by rw [hsym]; exact hwv) (by rw [hsym]; exact hw'v) h0
    have key : ∀ β : ZMod 5, β ≠ 0 → ∃ α γ δ : ZMod 5, α ≠ 0 ∧ δ ≠ 0 ∧
        α * α + γ * γ + δ * δ * β = 1 ∧ -(α * α) - γ * γ + δ * δ * β ≠ 0 := by decide
    obtain ⟨α, γ, δ, hα, hδ, hnorm, hne⟩ := key _ hzz
    obtain ⟨t, ht⟩ : ∃ t, t = α • w + γ • w' + δ • z := ⟨_, rfl⟩
    have htw : b t w = α := by
      simp only [ht, LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hw, hw'w, hzw]
      ring
    have htw' : b t w' = γ := by
      simp only [ht, LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hw', h0, hzw']
      ring
    have htz : b t z = δ * b z z := by
      simp only [ht, LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hsym w z,
        hsym w' z, hzw, hzw']
      ring
    have htt : b t t = 1 := by
      simp only [ht, LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
        LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hw, hw', h0, hw'w, hzw,
        hzw', hsym w z, hsym w' z]
      linear_combination hnorm
    have htv : b t v = 0 := by
      simp only [ht, LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hwv, hw'v, hzv]
      ring
    have hct : act (refl b w * refl b w') t = -(α • w) - γ • w' + δ • z := by
      rw [act_mul, act_refl hw', htw', act_refl hw, LinearMap.BilinForm.add_left,
        LinearMap.BilinForm.smul_left, htw, hw'w, ht]
      module
    have htct : b t (act (refl b w * refl b w') t) ≠ 0 := by
      rw [hct]
      simp only [LinearMap.BilinForm.add_right, LinearMap.BilinForm.sub_right,
        LinearMap.BilinForm.neg_right, LinearMap.BilinForm.smul_right, htw, htw', htz]
      convert hne using 1
      ring
    rcases step1 _ hc t htt htv htct with h1 | h1
    · have h2 := congrArg (fun x => b x w) h1
      simp only [hct, htw, LinearMap.BilinForm.add_left, LinearMap.BilinForm.sub_left,
        LinearMap.BilinForm.neg_left, LinearMap.BilinForm.smul_left, hw, hw'w, hzw] at h2
      apply hα
      have h3 : (2 : ZMod 5) * α = 0 := by linear_combination -h2
      exact (mul_eq_zero.1 h3).resolve_left (by decide)
    · have h2 := congrArg (fun x => b x z) h1
      simp only [hct, htz, LinearMap.BilinForm.add_left, LinearMap.BilinForm.sub_left,
        LinearMap.BilinForm.neg_left, LinearMap.BilinForm.smul_left, hsym w z, hsym w' z, hzw,
        hzw'] at h2
      have h3 : (2 : ZMod 5) * (δ * b z z) = 0 := by linear_combination h2
      rcases mul_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left (by decide)) with h4 | h4
      · exact hδ h4
      · exact hzz h4
  intro g hg
  exact eq_four_of_forall_perp hsym hnd hn hv (hS1 g hg) (hS5 g hg)
    fun w hw hwv => step1 g hg w hw hwv (step2 g hg w hw hwv)

theorem noSqE1_reflQuotient (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 4 ≤ n) :
    CFSG.RankThree.GF2n.Tim79a.NoSqE1 {q : reflGroup b ⧸ Subgroup.center (reflGroup b) |
      ∃ h : reflGroup b, (h : GL (Fin n) (ZMod 5)) ∈ reflSet b ∧
        q = (QuotientGroup.mk h : reflGroup b ⧸ Subgroup.center (reflGroup b))} := by
  intro d hd
  obtain ⟨h₀, hh₀, rfl⟩ := hd
  obtain ⟨v, hv, hh₀v⟩ := mem_reflSet_iff.1 hh₀
  set Z := Subgroup.center (reflGroup b) with hZdef
  set C := CFSG.RankThree.GF2n.Tim79a.cenGen {q : reflGroup b ⧸ Z |
      ∃ h : reflGroup b, (h : GL (Fin n) (ZMod 5)) ∈ reflSet b ∧ q = QuotientGroup.mk h}
    (QuotientGroup.mk h₀ : reflGroup b ⧸ Z) with hCdef
  set P := CFSG.inSubgroup (CFSG.pCore 2) C
  obtain ⟨hP2, hPC, hCP⟩ := CFSG.RankThree.GF2n.inSubgroup_pCore_two C
  have hCcent : C ≤ Subgroup.centralizer {(QuotientGroup.mk h₀ : reflGroup b ⧸ Z)} := by
    rw [hCdef, CFSG.RankThree.GF2n.Tim79a.cenGen, Subgroup.closure_le]
    exact Set.inter_subset_right
  have hZc : ∀ z : reflGroup b, z ∈ Z →
      (z : GL (Fin n) (ZMod 5)) = 1 ∨ (z : GL (Fin n) (ZMod 5)) = -1 :=
    fun z hz => coe_eq_of_mem_center hsym hnd hn hv hz
  have hneg : ∀ z : reflGroup b, (z : GL (Fin n) (ZMod 5)) = -1 → z ∈ Z := by
    intro z hz
    rw [hZdef, Subgroup.mem_center_iff]
    intro r
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hz, mul_neg_one, neg_one_mul]
  let S : Set (GL (Fin n) (ZMod 5)) :=
    {g | ∃ y : reflGroup b, (y : GL (Fin n) (ZMod 5)) = g ∧
      (QuotientGroup.mk y : reflGroup b ⧸ Z) ∈ P}
  have hS1 : ∀ g ∈ S, g ∈ isomGroup b := by
    rintro _ ⟨y, rfl, -⟩
    exact reflGroup_le_isomGroup hsym y.2
  have hS2 : ∀ g ∈ S, ∃ k : ℕ, g ^ 2 ^ k = 1 := by
    rintro _ ⟨y, rfl, hy⟩
    obtain ⟨k, hk⟩ := hP2 ⟨_, hy⟩
    have hk' : y ^ 2 ^ k ∈ Z := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      simpa using congrArg Subtype.val hk
    refine ⟨k + 1, ?_⟩
    rw [pow_succ, pow_mul, ← Subgroup.coe_pow]
    rcases hZc _ hk' with h | h
    · rw [h, one_pow]
    · rw [h, neg_one_sq]
  have hS3 : ∀ g ∈ S, ∀ w, b w w = 1 → b w v = 0 → refl b w * g * refl b w ∈ S := by
    rintro _ ⟨y, rfl, hy⟩ w hw hwv
    let ρ : reflGroup b := ⟨refl b w, refl_mem_reflGroup w⟩
    have hρ2 : ρ⁻¹ = ρ := Subtype.ext (refl_inv w)
    have hρC : (QuotientGroup.mk ρ : reflGroup b ⧸ Z) ∈ C := by
      apply Subgroup.subset_closure
      refine ⟨⟨ρ, refl_mem_reflSet hw, rfl⟩, ?_⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hh₀v]
      exact refl_comm_of_perp hsym hwv
    have hconj := (Subgroup.mem_normalizer_iff.1 (hCP hρC) _).1 hy
    refine ⟨ρ * y * ρ, rfl, ?_⟩
    have he : (QuotientGroup.mk (ρ * y * ρ) : reflGroup b ⧸ Z) =
        QuotientGroup.mk ρ * QuotientGroup.mk y * (QuotientGroup.mk ρ)⁻¹ := by
      rw [← QuotientGroup.mk_inv, hρ2, QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    rw [he]
    exact hconj
  have hS4 : ∀ g ∈ S, ∀ h ∈ S, g * h⁻¹ ∈ S := by
    rintro _ ⟨y₁, rfl, hy₁⟩ _ ⟨y₂, rfl, hy₂⟩
    refine ⟨y₁ * y₂⁻¹, rfl, ?_⟩
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact P.mul_mem hy₁ (P.inv_mem hy₂)
  have hS5 : ∀ g ∈ S, act g v = v ∨ act g v = -v := by
    rintro _ ⟨y, rfl, hy⟩
    have hiso := reflGroup_le_isomGroup hsym y.2
    have hcomm : (QuotientGroup.mk y : reflGroup b ⧸ Z) * QuotientGroup.mk h₀ =
        QuotientGroup.mk h₀ * QuotientGroup.mk y :=
      Subgroup.mem_centralizer_singleton_iff.1 (hCcent (hPC hy))
    have hz : y * h₀ * y⁻¹ * h₀⁻¹ ∈ Z := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, hcomm]
      group
    have hcoe : ((y * h₀ * y⁻¹ * h₀⁻¹ : reflGroup b) : GL (Fin n) (ZMod 5)) =
        refl b (act y v) * refl b v := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
        Subgroup.coe_inv, ← hh₀v, conj_refl hiso, refl_inv]
    have hyv : b (act y v) (act y v) = 1 := by rw [isom_norm hiso, hv]
    rcases hZc _ hz with h | h <;> rw [hcoe] at h
    · have h2 : refl b v = refl b (act y v) := by
        calc refl b v = refl b (act y v) * refl b v * refl b v := by
              rw [h, one_mul]
          _ = refl b (act y v) := by rw [mul_assoc, refl_mul_self, mul_one]
      exact (refl_eq_refl_iff hv hyv).1 h2
    · have h2 : refl b (act y v) = -refl b v := by
        calc refl b (act y v) = refl b (act y v) * refl b v * refl b v := by
              rw [mul_assoc, refl_mul_self, mul_one]
          _ = -refl b v := by rw [h, neg_one_mul]
      exact absurd h2 (refl_ne_neg_refl (by omega) v _)
  have key := eq_four_of_mem hsym hnd hn hv S hS1 hS2 hS3 hS4 hS5
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  apply Subgroup.mem_sup_left
  rcases key _ ⟨y, rfl, hx⟩ with h | h | h | h
  · rw [show y = 1 from Subtype.ext h, QuotientGroup.mk_one]
    exact Subgroup.one_mem _
  · rw [(QuotientGroup.eq_one_iff y).2 (hneg y h)]
    exact Subgroup.one_mem _
  · rw [show y = h₀ from Subtype.ext (h.trans hh₀v)]
    exact Subgroup.mem_zpowers _
  · have hz : y * h₀⁻¹ ∈ Z := hneg _ (by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, h, ← hh₀v, refl_inv, neg_mul, refl_mul_self])
    have he : (QuotientGroup.mk y : reflGroup b ⧸ Z) = QuotientGroup.mk h₀ := by
      calc (QuotientGroup.mk y : reflGroup b ⧸ Z) = QuotientGroup.mk (y * h₀⁻¹ * h₀) := by
            rw [inv_mul_cancel_right]
        _ = QuotientGroup.mk h₀ := by
            rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 hz, one_mul]
    rw [he]
    exact Subgroup.mem_zpowers _

end TableE1Five

open TableE1Five in
theorem noSqE1_of_fischerCentralQuotientModel_five {G : Type} [Group G] [Finite G] {D : Set G}
    {n : ℕ} (hn : 4 ≤ n) {b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5)}
    (hsym : ∀ x y, b x y = b y x) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hM : CFSG.Open.fischerCentralQuotientModel D
      (Subgroup.closure (CFSG.Open.fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1))
      (CFSG.Open.fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1)) :
    CFSG.RankThree.GF2n.Tim79a.NoSqE1 D := by
  obtain ⟨φ, hφ⟩ := hM
  refine noSqE1_of_map_mulEquiv φ ?_ (noSqE1_reflQuotient hsym hnd hn)
  ext q
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨φ.symm (QuotientGroup.mk h), (hφ _).2 ⟨h, hh, φ.apply_symm_apply _⟩,
      φ.apply_symm_apply _⟩
  · rintro ⟨g, hg, rfl⟩
    exact (hφ g).1 hg

end CFSG.OddTranspositions.PartFour
