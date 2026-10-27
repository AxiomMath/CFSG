module

public import CFSG.LocalAnalysis.StandardType.GGE6DepZLFinite

public section

namespace CFSG.StandardType

namespace E6Dep

namespace ZL

private lemma zlc_cartanM_symm : cartanM.transpose = cartanM := by decide +kernel

private lemma zlc_vecMul_cartanM (w : Vec6) :
    Matrix.vecMul w cartanM = cartanM.mulVec w := by
  rw [← zlc_cartanM_symm, Matrix.vecMul_transpose, zlc_cartanM_symm]

private lemma zlc_dot_C (u v : Vec6) :
    cartanM.mulVec u ⬝ᵥ v = u ⬝ᵥ cartanM.mulVec v := by
  calc cartanM.mulVec u ⬝ᵥ v = v ⬝ᵥ cartanM.mulVec u := dotProduct_comm _ _
    _ = Matrix.vecMul v cartanM ⬝ᵥ u := by rw [Matrix.dotProduct_mulVec]
    _ = cartanM.mulVec v ⬝ᵥ u := by rw [zlc_vecMul_cartanM]
    _ = u ⬝ᵥ cartanM.mulVec v := dotProduct_comm _ _

private lemma zlc_reflMat_mulVec (α h u : Vec6) :
    (reflMat α h).mulVec u = u - (α ⬝ᵥ u) • h := by
  simp only [reflMat, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec,
    op_smul_eq_smul]

private lemma zlc_scalar_reflsq : ∀ c xi hi : ZMod 3,
    xi - c * hi - (c - c * 2) * hi = xi := by decide +kernel

private lemma zlc_scalar_key_h : ∀ a b hi ki : ZMod 3,
    b * (a * hi + ki) = (-hi - b * (ki - a * hi)) - (-hi + b * ki) := by decide +kernel

private lemma zlc_scalar_key_k : ∀ a b hi ki : ZMod 3,
    a * (hi + b * ki) = (-ki - a * hi + (a * b) * ki) - (-ki + a * hi) := by decide +kernel

private lemma zlc_scalar_lhs_braid : ∀ a b hi ki : ZMod 3,
    -(hi - b * ki) - b * (-ki - a * (hi - b * ki)) =
      (b * a - 1) * hi + ((2 - b * a) * b) * ki := by decide +kernel

private lemma zlc_scalar_rhs_braid : ∀ a b hi ki : ZMod 3,
    -(-hi - b * (ki - a * hi)) = (1 - b * a) * hi + b * ki := by decide +kernel

private lemma zlc_scalar_braid_key : ∀ a b hi ki : ZMod 3,
    (a * b - 1) * (hi + b * ki) =
      ((1 - b * a) * hi + b * ki) - ((b * a - 1) * hi + ((2 - b * a) * b) * ki) := by
  decide +kernel

private lemma zlc_scalar_smul_eq_zero' : ∀ a x : ZMod 3, x ≠ 0 → a * x = 0 → a = 0 := by
  decide +kernel

private lemma zlc_scalar_sub_eq_self : ∀ c wi vi : ZMod 3,
    vi - c * wi = vi → c * wi = 0 := by decide +kernel

private lemma zlc_scalar_sub_sub_eq : ∀ u a k c y : ZMod 3,
    u - c * y - a * k = 0 → u = a * k + c * y := by decide +kernel

private lemma zlc_scalar_smul_eq_zero : ∀ a x : ZMod 3, a ≠ 0 → a * x = 0 → x = 0 := by
  decide +kernel

private lemma zlc_scalar_bb : ∀ b : ZMod 3, b ≠ 0 → b * b = 1 := by decide +kernel

private lemma zlc_scalar_neg2 : ∀ b : ZMod 3, (-b) * 2 = b := by decide +kernel

private lemma zlc_scalar_abm1 : ∀ a b : ZMod 3, a * b - 1 = 0 → a = b := by decide +kernel

private lemma zlc_scalar_neg_mul : ∀ a b : ZMod 3, (-a) * b = 2 → a = b := by decide +kernel

private lemma zlc_smul_eq_zero {a : ZMod 3} {v : Vec6} (ha : a ≠ 0) (h : a • v = 0) :
    v = 0 := by
  funext i
  have hi := congrFun h i
  simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hi
  exact zlc_scalar_smul_eq_zero a (v i) ha hi

private lemma zlc_eq_zero_of_smul_eq_zero {a : ZMod 3} {v : Vec6} (hv : v ≠ 0)
    (h : a • v = 0) : a = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hv (funext fun i => h' i)
  have hc := congrFun h i
  simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hc
  exact zlc_scalar_smul_eq_zero' a (v i) hi hc

private lemma zlc_sub_eq_self_smul {c : ZMod 3} {v w : Vec6} (h : v - c • w = v) :
    c • w = 0 := by
  funext i
  have hi := congrFun h i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
  exact zlc_scalar_sub_eq_self c (w i) (v i) hi

private lemma zlc_reflMat_sq {α h : Vec6} (hαh : α ⬝ᵥ h = 2) :
    reflMat α h * reflMat α h = 1 := by
  rw [Matrix.ext_iff_mulVec]
  intro u
  rw [← Matrix.mulVec_mulVec, zlc_reflMat_mulVec, zlc_reflMat_mulVec, Matrix.one_mulVec]
  simp only [dotProduct_sub, dotProduct_smul, hαh]
  funext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  exact zlc_scalar_reflsq (α ⬝ᵥ u) (u i) (h i)

private lemma zlc_comm_of_sq {s r : Mat6} (hss : s * s = 1) (hrr : r * r = 1)
    (h : (s * r) ^ 2 = 1) : s * r = r * s := by
  have h1 : s * r * s * r = 1 := by simpa only [pow_two, mul_assoc] using h
  have h2 : r * s * r = s := by
    have hh := congrArg (fun x => s * x) h1
    rw [mul_one] at hh
    have e : s * (s * r * s * r) = (s * s) * (r * s * r) := by simp only [mul_assoc]
    rw [e, hss, one_mul] at hh
    exact hh
  have h3 : r * s * (r * r) = s * r := by
    calc r * s * (r * r) = (r * s * r) * r := by simp only [mul_assoc]
      _ = s * r := congrArg (fun x => x * r) h2
  rw [hrr, mul_one] at h3
  exact h3.symm

private lemma zlc_braid_of_cube {s r : Mat6} (hss : s * s = 1) (hrr : r * r = 1)
    (h : (s * r) ^ 3 = 1) : r * s * r = s * r * s := by
  have hXY : (s * r * s) * (r * s * r) = 1 := by
    have h' : s * r * s * r * s * r = 1 := by
      simpa only [pow_three, pow_two, mul_assoc] using h
    simpa only [mul_assoc] using h'
  have hX : (s * r * s) * (s * r * s) = 1 := by
    calc (s * r * s) * (s * r * s) = s * r * (s * s) * r * s := by simp only [mul_assoc]
      _ = s * r * 1 * r * s := by rw [hss]
      _ = s * (r * r) * s := by simp only [mul_assoc, mul_one]
      _ = s * 1 * s := by rw [hrr]
      _ = 1 := by rw [mul_one, hss]
  calc r * s * r = 1 * (r * s * r) := by rw [one_mul]
    _ = ((s * r * s) * (s * r * s)) * (r * s * r) := by rw [hX]
    _ = (s * r * s) * ((s * r * s) * (r * s * r)) := by simp only [mul_assoc]
    _ = (s * r * s) * 1 := by rw [hXY]
    _ = s * r * s := by rw [mul_one]

private lemma zlc_centre_ne_zero {Λ : Type} (h : Λ → Vec6) (l : Λ)
    (hn : bilU (h l) (h l) = 2) : h l ≠ 0 := by
  intro h0
  have h2 : h l ⬝ᵥ cartanM.mulVec (h l) = 2 := by simpa only [bilU] using hn
  rw [h0, Matrix.mulVec_zero, zero_dotProduct] at h2
  exact (by decide : (2 : ZMod 3) ≠ 0) h2.symm

private lemma zlc_fixed_perp {Λ : Type} (g : Λ → Mat6) (h : Λ → Vec6) (l : Λ)
    (hg : g l = reflMat (cartanM.mulVec (h l)) (h l))
    (hn : bilU (h l) (h l) = 2) {v : Vec6} (hv : (g l).mulVec v = v) :
    (cartanM.mulVec v) ⬝ᵥ h l = 0 := by
  have hhl : h l ≠ 0 := zlc_centre_ne_zero h l hn
  have hc : (cartanM.mulVec (h l)) ⬝ᵥ v = 0 := by
    have hsub : v - ((cartanM.mulVec (h l)) ⬝ᵥ v) • h l = v := by
      calc v - ((cartanM.mulVec (h l)) ⬝ᵥ v) • h l = (g l).mulVec v := by
            rw [hg, zlc_reflMat_mulVec]
        _ = v := hv
    have hzero : ((cartanM.mulVec (h l)) ⬝ᵥ v) • h l = 0 :=
      zlc_sub_eq_self_smul hsub
    exact zlc_eq_zero_of_smul_eq_zero hhl hzero
  calc (cartanM.mulVec v) ⬝ᵥ h l = (cartanM.mulVec (h l)) ⬝ᵥ v := by
        rw [zlc_dot_C, dotProduct_comm]
    _ = 0 := hc

private lemma zlc_nondeg {Λ : Type} (b : Λ) (g : Λ → Mat6) (h : Λ → Vec6)
    (hn : ∀ l, bilU (h l) (h l) = 2)
    (hg : ∀ l, g l = reflMat (cartanM.mulVec (h l)) (h l))
    (hgen : ∀ m ∈ closureU, m ∈ Submonoid.closure (Set.range g)) :
    ∀ f : Vec6, (∀ l, f ⬝ᵥ h l = 0) → f = 0 := by
  intro f hf
  set M : Submodule (ZMod 3) Vec6 := Submodule.span (ZMod 3) (Set.range h) with hM
  have hspan : ∀ l, h l ∈ M := fun l => Submodule.subset_span ⟨l, rfl⟩
  have hCl : ∀ m ∈ Submonoid.closure (Set.range g), ∀ v ∈ M, m.mulVec v ∈ M := by
    intro m hm
    induction hm using Submonoid.closure_induction with
    | mem m hm =>
      obtain ⟨l, rfl⟩ := hm
      intro v hv
      rw [hg l, zlc_reflMat_mulVec]
      exact Submodule.sub_mem M hv (Submodule.smul_mem M _ (hspan l))
    | one =>
      intro v hv
      simpa using hv
    | mul a' b' _ _ iha ihb =>
      intro v hv
      rw [← Matrix.mulVec_mulVec]
      exact iha _ (ihb v hv)
  have hinv : ∀ m ∈ closureU, ∀ v ∈ M, m.mulVec v ∈ M :=
    fun m hm v hv => hCl m (hgen m hm) v hv
  have hCb : cartanM.mulVec (h b) ≠ 0 := by
    intro h0
    have h2 : h b ⬝ᵥ cartanM.mulVec (h b) = 2 := by simpa only [bilU] using hn b
    rw [h0, dotProduct_zero] at h2
    exact (by decide : (2 : ZMod 3) ≠ 0) h2.symm
  have htop : M = ⊤ := zl_span_top M hinv (hspan b) hCb
  have hfM : ∀ v ∈ M, f ⬝ᵥ v = 0 := by
    intro v hv
    rw [hM] at hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨l, rfl⟩ := hv
      exact hf l
    | zero => simp
    | add x y _ _ ihx ihy => rw [dotProduct_add, ihx, ihy, add_zero]
    | smul a' x _ ihx => rw [dotProduct_smul, ihx, smul_zero]
  funext j
  have hj : f ⬝ᵥ (Pi.single j 1 : Vec6) = 0 :=
    hfM _ (by rw [htop]; exact Submodule.mem_top)
  rwa [dotProduct_single_one] at hj

private lemma zlc_hb {Λ : Type} (b : Λ) (g : Λ → Mat6) (h : Λ → Vec6) (y : Vec6)
    (hn : ∀ l, bilU (h l) (h l) = 2)
    (hg : ∀ l, g l = reflMat (cartanM.mulVec (h l)) (h l))
    (hgen : ∀ m ∈ closureU, m ∈ Submonoid.closure (Set.range g))
    (hy : cartanM.mulVec y ≠ 0)
    (hgy : ∀ l, l ≠ b → (g l).mulVec y = y) :
    (cartanM.mulVec y) ⬝ᵥ h b ≠ 0 := by
  intro h0
  apply hy
  apply zlc_nondeg b g h hn hg hgen
  intro l
  by_cases hl : l = b
  · rw [hl]; exact h0
  · exact zlc_fixed_perp g h l (hg l) (hn l) (hgy l hl)

private lemma zlc_coeff {Λ : Type} (b : Λ) (g : Λ → Mat6) (h : Λ → Vec6) (y w : Vec6)
    (hn : ∀ l, bilU (h l) (h l) = 2)
    (hg : ∀ l, g l = reflMat (cartanM.mulVec (h l)) (h l))
    (hgen : ∀ m ∈ closureU, m ∈ Submonoid.closure (Set.range g))
    (hy : cartanM.mulVec y ≠ 0)
    (hgy : ∀ l, l ≠ b → (g l).mulVec y = y)
    (hw : ∀ l, l ≠ b → w ⬝ᵥ h l = 0) :
    ∃ c : ZMod 3, w = c • cartanM.mulVec y := by
  have hden : (cartanM.mulVec y) ⬝ᵥ h b ≠ 0 := zlc_hb b g h y hn hg hgen hy hgy
  refine ⟨(w ⬝ᵥ h b) * ((cartanM.mulVec y) ⬝ᵥ h b), ?_⟩
  have hf : w - ((w ⬝ᵥ h b) * ((cartanM.mulVec y) ⬝ᵥ h b)) • cartanM.mulVec y = 0 := by
    apply zlc_nondeg b g h hn hg hgen
    intro l
    by_cases hl : l = b
    · rw [hl]
      rw [sub_dotProduct, smul_dotProduct, smul_eq_mul]
      have hbb : ((cartanM.mulVec y) ⬝ᵥ h b) * ((cartanM.mulVec y) ⬝ᵥ h b) = 1 :=
        zlc_scalar_bb _ hden
      rw [mul_assoc, hbb, mul_one, sub_self]
    · have hz : (cartanM.mulVec y) ⬝ᵥ h l = 0 :=
        zlc_fixed_perp g h l (hg l) (hn l) (hgy l hl)
      rw [sub_dotProduct, smul_dotProduct, smul_eq_mul, hw l hl, hz, mul_zero, sub_zero]
  rw [sub_eq_zero] at hf
  exact hf

theorem zl_pair {h k α : Vec6} (hh : bilU h h = 2) (hα : α ⬝ᵥ k = 2)
    (hp : (reflMat (cartanM.mulVec h) h * reflMat α k) ^ 2 = 1 ∨
      (reflMat (cartanM.mulVec h) h * reflMat α k) ^ 3 = 1) :
    α ⬝ᵥ h = cartanM.mulVec h ⬝ᵥ k := by
  set a : ZMod 3 := cartanM.mulVec h ⬝ᵥ k with ha
  set b : ZMod 3 := α ⬝ᵥ h with hb
  have hCh : (cartanM.mulVec h) ⬝ᵥ h = 2 := by
    rw [dotProduct_comm]; simpa only [bilU] using hh
  have hss : reflMat (cartanM.mulVec h) h * reflMat (cartanM.mulVec h) h = 1 :=
    zlc_reflMat_sq hCh
  have hrr : reflMat α k * reflMat α k = 1 := zlc_reflMat_sq hα
  have hh0 : h ≠ 0 := by
    intro h0
    have h2 : (cartanM.mulVec h) ⬝ᵥ h = 2 := hCh
    rw [h0, Matrix.mulVec_zero, zero_dotProduct] at h2
    exact (by decide : (2 : ZMod 3) ≠ 0) h2.symm
  have hk0 : k ≠ 0 := by
    intro h0
    have h2 : α ⬝ᵥ k = 2 := hα
    rw [h0, dotProduct_zero] at h2
    exact (by decide : (2 : ZMod 3) ≠ 0) h2.symm
  have hS_h : (reflMat (cartanM.mulVec h) h).mulVec h = -h := by
    rw [zlc_reflMat_mulVec, hCh]
    funext i
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    ring
  have hS_k : (reflMat (cartanM.mulVec h) h).mulVec k = k - a • h := by
    rw [zlc_reflMat_mulVec, ha]
  have hR_h : (reflMat α k).mulVec h = h - b • k := by
    rw [zlc_reflMat_mulVec, hb]
  have hR_k : (reflMat α k).mulVec k = -k := by
    rw [zlc_reflMat_mulVec, hα]
    funext i
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    ring
  rcases hp with hp2 | hp3
  ·
    have hcomm : reflMat (cartanM.mulVec h) h * reflMat α k =
        reflMat α k * reflMat (cartanM.mulVec h) h := zlc_comm_of_sq hss hrr hp2
    have e_h : (reflMat (cartanM.mulVec h) h).mulVec ((reflMat α k).mulVec h) =
        (reflMat α k).mulVec ((reflMat (cartanM.mulVec h) h).mulVec h) := by
      rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec]
    have lhs_h : (reflMat (cartanM.mulVec h) h).mulVec ((reflMat α k).mulVec h) =
        -h - b • (k - a • h) := by
      rw [hR_h, Matrix.mulVec_sub, Matrix.mulVec_smul, hS_h, hS_k]
    have rhs_h : (reflMat α k).mulVec ((reflMat (cartanM.mulVec h) h).mulVec h) =
        -h + b • k := by
      rw [hS_h, Matrix.mulVec_neg, hR_h]
      funext i
      simp only [Pi.neg_apply, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have key_h : b • (a • h + k) =
        (reflMat (cartanM.mulVec h) h).mulVec ((reflMat α k).mulVec h) -
          (reflMat α k).mulVec ((reflMat (cartanM.mulVec h) h).mulVec h) := by
      rw [lhs_h, rhs_h]
      funext i
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
      exact zlc_scalar_key_h a b (h i) (k i)
    have star : b • (a • h + k) = 0 := by rw [key_h, e_h, sub_self]
    have e_k : (reflMat (cartanM.mulVec h) h).mulVec ((reflMat α k).mulVec k) =
        (reflMat α k).mulVec ((reflMat (cartanM.mulVec h) h).mulVec k) := by
      rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec]
    have lhs_k : (reflMat (cartanM.mulVec h) h).mulVec ((reflMat α k).mulVec k) =
        -k + a • h := by
      rw [hR_k, Matrix.mulVec_neg, hS_k]
      funext i
      simp only [Pi.neg_apply, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have rhs_k : (reflMat α k).mulVec ((reflMat (cartanM.mulVec h) h).mulVec k) =
        -k - a • h + (a * b) • k := by
      rw [hS_k, Matrix.mulVec_sub, Matrix.mulVec_smul, hR_k, hR_h]
      funext i
      simp only [Pi.neg_apply, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have key_k : a • (h + b • k) =
        (reflMat α k).mulVec ((reflMat (cartanM.mulVec h) h).mulVec k) -
          (reflMat (cartanM.mulVec h) h).mulVec ((reflMat α k).mulVec k) := by
      rw [lhs_k, rhs_k]
      funext i
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
      exact zlc_scalar_key_k a b (h i) (k i)
    have star2 : a • (h + b • k) = 0 := by rw [key_k, e_k, sub_self]
    by_cases ha0 : a = 0
    · by_cases hb0 : b = 0
      · rw [ha0, hb0]
      · exfalso
        have hx : a • h + k = 0 := zlc_smul_eq_zero hb0 star
        rw [ha0, zero_smul, zero_add] at hx
        exact hk0 hx
    · have hbk : h + b • k = 0 := zlc_smul_eq_zero ha0 star2
      by_cases hb0 : b = 0
      · exfalso
        rw [hb0, zero_smul, add_zero] at hbk
        exact hh0 hbk
      · have hk : k = (-a) • h := by
          have hx : a • h + k = 0 := zlc_smul_eq_zero hb0 star
          have hneg : k = -(a • h) := by
            rw [eq_neg_iff_add_eq_zero]
            rwa [add_comm]
          rw [hneg, neg_smul]
        have hscal : (-a) * b = 2 := by
          have hh' : α ⬝ᵥ k = 2 := hα
          rw [hk, dotProduct_smul, smul_eq_mul] at hh'
          rwa [← hb] at hh'
        exact (zlc_scalar_neg_mul a b hscal).symm
  ·
    have hbraid : reflMat α k * reflMat (cartanM.mulVec h) h * reflMat α k =
        reflMat (cartanM.mulVec h) h * reflMat α k * reflMat (cartanM.mulVec h) h :=
      zlc_braid_of_cube hss hrr hp3
    have lhs_braid : (reflMat α k * reflMat (cartanM.mulVec h) h * reflMat α k).mulVec h =
        (b * a - 1) • h + ((2 - b * a) * b) • k := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      rw [hR_h, Matrix.mulVec_sub, Matrix.mulVec_smul, hS_h, hS_k,
        Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_neg, hR_h,
        Matrix.mulVec_sub, Matrix.mulVec_smul, hR_k, hR_h]
      funext i
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
      exact zlc_scalar_lhs_braid a b (h i) (k i)
    have rhs_braid :
        (reflMat (cartanM.mulVec h) h * reflMat α k * reflMat (cartanM.mulVec h) h).mulVec h =
        (1 - b * a) • h + b • k := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      rw [hS_h, Matrix.mulVec_neg, hR_h, Matrix.mulVec_neg, Matrix.mulVec_sub,
        Matrix.mulVec_smul, hS_h, hS_k]
      funext i
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
      exact zlc_scalar_rhs_braid a b (h i) (k i)
    have key_braid : (a * b - 1) • (h + b • k) =
        (reflMat (cartanM.mulVec h) h * reflMat α k *
            reflMat (cartanM.mulVec h) h).mulVec h -
          (reflMat α k * reflMat (cartanM.mulVec h) h * reflMat α k).mulVec h := by
      rw [lhs_braid, rhs_braid]
      funext i
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact zlc_scalar_braid_key a b (h i) (k i)
    have e_braid :
        (reflMat α k * reflMat (cartanM.mulVec h) h * reflMat α k).mulVec h =
          (reflMat (cartanM.mulVec h) h * reflMat α k *
            reflMat (cartanM.mulVec h) h).mulVec h := by rw [hbraid]
    have hstar : (a * b - 1) • (h + b • k) = 0 := by
      rw [key_braid, ← e_braid, sub_self]
    by_cases hab : a * b - 1 = 0
    · exact (zlc_scalar_abm1 a b hab).symm
    · have hbk : h + b • k = 0 := zlc_smul_eq_zero hab hstar
      have hb0 : b ≠ 0 := by
        intro hb0
        rw [hb0, zero_smul, add_zero] at hbk
        exact hh0 hbk
      have hb2 : b * b = 1 := zlc_scalar_bb b hb0
      have hk : k = (-b) • h := by
        have h1 : b • (h + b • k) = 0 := by rw [hbk, smul_zero]
        have h2 : b • (b • k) = k := by
          have h2' : b • (b • k) = (b * b) • k := smul_smul b b k
          rw [h2', hb2, one_smul]
        rw [smul_add, h2, add_comm] at h1
        have hneg : k = -(b • h) := by
          rw [eq_neg_iff_add_eq_zero]
          exact h1
        rw [hneg, neg_smul]
      have haeq : a = (-b) * 2 := by
        have h1 : a = (cartanM.mulVec h) ⬝ᵥ ((-b) • h) := by rw [ha, hk]
        rw [h1, dotProduct_smul, smul_eq_mul, hCh]
      rw [haeq, zlc_scalar_neg2 b]

theorem zl_core {Λ : Type} (b : Λ) (g : Λ → Mat6) (r : Mat6) (y : Vec6)
    (hgW : ∀ l, g l ∈ closureU) (hgR : ∀ l, IsRefl6 (g l))
    (hgen : ∀ m ∈ closureU, m ∈ Submonoid.closure (Set.range g))
    (hrR : IsRefl6 r) (hy : cartanM.mulVec y ≠ 0)
    (hgy : ∀ l, l ≠ b → (g l).mulVec y = y)
    (hp : ∀ l, l ≠ b → (g l * r) ^ 2 = 1 ∨ (g l * r) ^ 3 = 1) :
    r.mulVec kappa = kappa := by
  have hc0 : ∀ l, ∃ h : Vec6, bilU h h = 2 ∧ g l = reflMat (cartanM.mulVec h) h :=
    fun l => closureU_refl (hgW l) (hgR l)
  choose h hn_hg using hc0
  have hn : ∀ l, bilU (h l) (h l) = 2 := fun l => (hn_hg l).1
  have hg : ∀ l, g l = reflMat (cartanM.mulVec (h l)) (h l) := fun l => (hn_hg l).2
  obtain ⟨α, k, hαk, hr⟩ := isRefl6_form hrR
  have hpair : ∀ l, l ≠ b → α ⬝ᵥ h l = (cartanM.mulVec (h l)) ⬝ᵥ k := by
    intro l hl
    have hp' := hp l hl
    rw [hg l, hr] at hp'
    exact zl_pair (hn l) hαk hp'
  set w : Vec6 := α - cartanM.mulVec k with hwdef
  have hwperp : ∀ l, l ≠ b → w ⬝ᵥ h l = 0 := by
    intro l hl
    have h1 : (cartanM.mulVec k) ⬝ᵥ h l = (cartanM.mulVec (h l)) ⬝ᵥ k := by
      rw [zlc_dot_C, dotProduct_comm]
    rw [hwdef, sub_dotProduct, hpair l hl, h1, sub_self]
  obtain ⟨c, hc⟩ := zlc_coeff b g h y w hn hg hgen hy hgy hwperp
  have hαkappa : α ⬝ᵥ kappa = 0 := by
    have hαeq : α = w + cartanM.mulVec k := by rw [hwdef]; abel
    have h1 : (cartanM.mulVec k) ⬝ᵥ kappa = 0 := by
      rw [zlc_dot_C, cartanM_kappa, dotProduct_zero]
    have h2 : (cartanM.mulVec y) ⬝ᵥ kappa = 0 := by
      rw [zlc_dot_C, cartanM_kappa, dotProduct_zero]
    rw [hαeq, add_dotProduct, hc, smul_dotProduct, smul_eq_mul, h2, mul_zero, h1, add_zero]
  rw [hr, zlc_reflMat_mulVec, hαkappa, zero_smul, sub_zero]

theorem zl_fixS {Λ : Type} (b : Λ) (g : Λ → Mat6) (y : Vec6)
    (hgW : ∀ l, g l ∈ closureU) (hgR : ∀ l, IsRefl6 (g l))
    (hgen : ∀ m ∈ closureU, m ∈ Submonoid.closure (Set.range g))
    (hy : cartanM.mulVec y ≠ 0) (hgy : ∀ l, l ≠ b → (g l).mulVec y = y)
    {u : Vec6} (hu : ∀ l, l ≠ b → (g l).mulVec u = u) :
    ∃ a c : ℕ, u = a • kappa + c • y := by
  have hc0 : ∀ l, ∃ h : Vec6, bilU h h = 2 ∧ g l = reflMat (cartanM.mulVec h) h :=
    fun l => closureU_refl (hgW l) (hgR l)
  choose h hn_hg using hc0
  have hn : ∀ l, bilU (h l) (h l) = 2 := fun l => (hn_hg l).1
  have hg : ∀ l, g l = reflMat (cartanM.mulVec (h l)) (h l) := fun l => (hn_hg l).2
  have hw : ∀ l, l ≠ b → (cartanM.mulVec u) ⬝ᵥ h l = 0 :=
    fun l hl => zlc_fixed_perp g h l (hg l) (hn l) (hu l hl)
  obtain ⟨c, hc⟩ := zlc_coeff b g h y (cartanM.mulVec u) hn hg hgen hy hgy hw
  have hker : cartanM.mulVec (u - c • y) = 0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hc, sub_self]
  obtain ⟨a, ha⟩ := rad_eq (u - c • y) hker
  refine ⟨a.val, c.val, ?_⟩
  have hua : u = a • kappa + c • y := by
    have h' : u - c • y - a • kappa = 0 := by rw [ha, sub_self]
    funext i
    have hi := congrFun h' i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hi ⊢
    exact zlc_scalar_sub_sub_eq (u i) a (kappa i) c (y i) hi
  rw [hua]
  have h1 : a • kappa = a.val • kappa := by
    conv_lhs => rw [← ZMod.natCast_zmod_val a]
    exact Nat.cast_smul_eq_nsmul (ZMod 3) a.val kappa
  have h2 : c • y = c.val • y := by
    conv_lhs => rw [← ZMod.natCast_zmod_val c]
    exact Nat.cast_smul_eq_nsmul (ZMod 3) c.val y
  rw [h1, h2]

end ZL

end E6Dep

end CFSG.StandardType

end
