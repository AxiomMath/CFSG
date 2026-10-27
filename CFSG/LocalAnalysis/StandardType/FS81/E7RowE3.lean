module

public import CFSG.LocalAnalysis.StandardType.FS81.E7RowE2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81.E7Row

open scoped Matrix

local notation:max "↑ₘ" g:max => ((g : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3))

variable {X : Subgroup (GL (Fin 8) (ZMod 3))}

@[expose] def coefMap (ρ β : ZMod 3) (p : ZMod 3 × ZMod 3) : ZMod 3 × ZMod 3 :=
  (-p.1 + β * p.2, -(ρ * p.1) + (β * ρ - 1) * p.2)

theorem coefMap_ord23 : ∀ ρ β : ZMod 3,
    (coefMap ρ β (coefMap ρ β (1, 0)) = (1, 0) ∧ coefMap ρ β (coefMap ρ β (0, 1)) = (0, 1)) ∨
      (coefMap ρ β (coefMap ρ β (coefMap ρ β (1, 0))) = (1, 0) ∧
        coefMap ρ β (coefMap ρ β (coefMap ρ β (0, 1))) = (0, 1)) → ρ = β := by
  decide

theorem ord23_val {u : GL (Fin 8) (ZMod 3)} (hu : Ord23 u) : Ord23 ↑ₘu := by
  rcases hu with e | e
  · left
    rw [← Units.val_mul, e, Units.val_one]
  · right
    rw [← Units.val_mul, ← Units.val_mul, e, Units.val_one]

theorem pair_coef {T : Matrix (Fin 8) (Fin 8) (ZMod 3)} {r v : Coords 8} {φ : Coords 8 → ZMod 3}
    (hT : ∀ w, T *ᵥ w = w + φ w • v) (hTv : T *ᵥ v = -v) (hr : b8 r r = 1)
    {i j : Fin 8} (hri : r i = 0) (hvi : v i ≠ 0) (hrj : r j ≠ 0)
    (hk : Ord23 (T * reflM r)) : φ r = b8 v r := by
  have hP : ∀ p : ZMod 3 × ZMod 3, (T * reflM r) *ᵥ (p.1 • r + p.2 • v) =
      (coefMap (φ r) (b8 v r) p).1 • r + (coefMap (φ r) (b8 v r) p).2 • v := by
    intro p
    simp only [← Matrix.mulVec_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_neg,
      reflM_mulVec_self hr, reflM_mulVec r v, hTv, hT r, coefMap]
    module
  have two : ∀ p : ZMod 3 × ZMod 3, (T * reflM r * (T * reflM r)) *ᵥ (p.1 • r + p.2 • v) =
      (coefMap (φ r) (b8 v r) (coefMap (φ r) (b8 v r) p)).1 • r +
        (coefMap (φ r) (b8 v r) (coefMap (φ r) (b8 v r) p)).2 • v := by
    intro p
    rw [← Matrix.mulVec_mulVec, hP, hP]
  have three : ∀ p : ZMod 3 × ZMod 3,
      (T * reflM r * (T * reflM r) * (T * reflM r)) *ᵥ (p.1 • r + p.2 • v) =
      (coefMap (φ r) (b8 v r) (coefMap (φ r) (b8 v r) (coefMap (φ r) (b8 v r) p))).1 • r +
        (coefMap (φ r) (b8 v r) (coefMap (φ r) (b8 v r) (coefMap (φ r) (b8 v r) p))).2 • v := by
    intro p
    rw [← Matrix.mulVec_mulVec, hP, two]
  have hbasis : ∀ x y x' y' : ZMod 3, x • r + y • v = x' • r + y' • v → x = x' ∧ y = y' := by
    intro x y x' y' e
    have ei := congrFun e i
    have ej := congrFun e j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hri, mul_zero, zero_add] at ei ej
    have hy : y = y' := mul_right_cancel₀ hvi ei
    subst hy
    exact ⟨mul_right_cancel₀ hrj (add_right_cancel ej), rfl⟩
  have fix : ∀ (Q : Matrix (Fin 8) (Fin 8) (ZMod 3)) (f : ZMod 3 × ZMod 3 → ZMod 3 × ZMod 3),
      Q = 1 → (∀ p : ZMod 3 × ZMod 3, Q *ᵥ (p.1 • r + p.2 • v) = (f p).1 • r + (f p).2 • v) →
        f (1, 0) = (1, 0) ∧ f (0, 1) = (0, 1) := by
    intro Q f hQ hf
    constructor
    · have e := hf (1, 0)
      rw [hQ, Matrix.one_mulVec] at e
      obtain ⟨e1, e2⟩ := hbasis _ _ _ _ e
      exact Prod.ext e1.symm e2.symm
    · have e := hf (0, 1)
      rw [hQ, Matrix.one_mulVec] at e
      obtain ⟨e1, e2⟩ := hbasis _ _ _ _ e
      exact Prod.ext e1.symm e2.symm
  apply coefMap_ord23
  rcases hk with hk | hk
  · exact Or.inl (fix _ _ hk two)
  · exact Or.inr (fix _ _ hk three)

theorem matrix_ext_single {A B : Matrix (Fin 8) (Fin 8) (ZMod 3)}
    (h : ∀ j : Fin 8, A *ᵥ Pi.single j 1 = B *ᵥ Pi.single j 1) : A = B := by
  ext i j
  have := congrFun (h j) i
  rwa [Matrix.mulVec_single_one, Matrix.mulVec_single_one, Matrix.col_apply, Matrix.col_apply] at this

theorem two_smul_pm (j l : Fin 8) :
    (2 : ZMod 3) • ((Pi.single j 1 + Pi.single l 1) + (Pi.single j 1 - Pi.single l 1) : Coords 8) =
      Pi.single j 1 := by
  rw [show ((Pi.single j 1 + Pi.single l 1) + (Pi.single j 1 - Pi.single l 1) : Coords 8) =
    (2 : ZMod 3) • Pi.single j 1 by module, smul_smul]
  rw [show (2 * 2 : ZMod 3) = 1 by decide, one_smul]

section T0

variable {t : GL (Fin 8) (ZMod 3)}

theorem exists_conj_t0_reflM (h : CoreHyp X) {δ : ZMod 3} (hδ : δ = 1 ∨ δ = -1)
    (horb : ∀ v, v ∈ orb1 X ↔ IsRoot7 δ v) (ht : t ∈ X) (htM : ↑ₘt = t0M)
    {g : GL (Fin 8) (ZMod 3)} (hg : g ∈ X) (hgr : IsRoot7 δ (↑ₘg *ᵥ Pi.single 0 1))
    {r : Coords 8} (hr : IsRoot7 δ r) : ∃ z ∈ X, ↑ₘz *ᵥ Pi.single 0 1 = r ∧ ↑ₘ(z * t * z⁻¹) = reflM r := by
  obtain ⟨z, hz, hze⟩ := root_orbit horb hg hgr hr
  have := (conj_t0_of_zero h hδ horb ht htM hz (by rw [hze]; exact hr.1)).2
  rw [hze] at this
  exact ⟨z, hz, hze, this⟩

theorem conj_t0_mixed (h : CoreHyp X) {δ : ZMod 3} (hδ : δ = 1 ∨ δ = -1)
    (horb : ∀ v, v ∈ orb1 X ↔ IsRoot7 δ v) (ht : t ∈ X) (htM : ↑ₘt = t0M)
    {g : GL (Fin 8) (ZMod 3)} (hg : g ∈ X) (hgr : IsRoot7 δ (↑ₘg *ᵥ Pi.single 0 1))
    {y : GL (Fin 8) (ZMod 3)} (hy : y ∈ X) (hy0 : (↑ₘy *ᵥ Pi.single 0 1) 0 = 1) {i : Fin 8}
    (hi : i ≠ 0) (hyi : (↑ₘy *ᵥ Pi.single 0 1) i ≠ 0) :
    ↑ₘ(y * t * y⁻¹) = reflM (↑ₘy *ᵥ Pi.single 0 1) ∧
      b8 (↑ₘy *ᵥ Pi.single 0 1) (↑ₘy *ᵥ Pi.single 0 1) = 1 := by
  have hax := axis_conj_t0 htM y
  have hTv := hax.2.1
  have hT : ∀ w, ↑ₘ(y * t * y⁻¹) *ᵥ w =
      w + (↑ₘ(y * t * y⁻¹) *ᵥ w - w) 0 • (↑ₘy *ᵥ Pi.single 0 1) := by
    intro w
    obtain ⟨c, hc⟩ := hax.2.2 w
    have e := congrFun hc 0
    rw [Pi.smul_apply, smul_eq_mul, hy0, mul_one] at e
    rw [e, ← hc]
    abel
  have hordr : ∀ r, IsRoot7 δ r → Ord23 (↑ₘ(y * t * y⁻¹) * reflM r) := by
    intro r hr
    obtain ⟨z, hz, -, hzr⟩ := exists_conj_t0_reflM h hδ horb ht htM hg hgr hr
    have := ord23_val (conj_t0_pair h hδ horb ht htM hg hgr hy hz)
    rwa [Units.val_mul, hzr] at this
  have hord0 : Ord23 (↑ₘ(y * t * y⁻¹) * reflM (Pi.single 0 1)) := by
    have := ord23_val (conj_t0_pair h hδ horb ht htM hg hgr hy X.one_mem)
    rwa [Units.val_mul, show (1 : GL (Fin 8) (ZMod 3)) * t * 1⁻¹ = t by group, htM,
      t0M_eq_reflM] at this
  generalize ↑ₘy *ᵥ (Pi.single 0 1 : Coords 8) = v at hT hTv hy0 hyi ⊢
  generalize ↑ₘ(y * t * y⁻¹) = T at hT hTv hordr hord0 ⊢
  have hφr : ∀ r, IsRoot7 δ r → (T *ᵥ r - r) 0 = b8 v r := by
    intro r hr
    obtain ⟨j, hj⟩ := Function.ne_iff.mp (root7_ne_zero hδ hr)
    exact pair_coef (φ := fun w => (T *ᵥ w - w) 0) hT hTv (root7_b8 hδ hr) hr.1
      (by rw [hy0]; exact one_ne_zero) hj (hordr r hr)
  have hφ0 : (T *ᵥ Pi.single 0 1 - Pi.single 0 1 : Coords 8) 0 = b8 v (Pi.single 0 1) :=
    pair_coef (φ := fun w => (T *ᵥ w - w) 0) (i := i) (j := 0) hT hTv
      (by rw [b8_e0_left, Pi.single_eq_same]) (Pi.single_eq_of_ne hi 1) hyi (by simp) hord0
  have hadd : ∀ a b : Coords 8, (T *ᵥ (a + b) - (a + b)) 0 = (T *ᵥ a - a) 0 + (T *ᵥ b - b) 0 := by
    intro a b
    simp only [Matrix.mulVec_add, Pi.sub_apply, Pi.add_apply]
    ring
  have hsmul : ∀ (c : ZMod 3) (a : Coords 8), (T *ᵥ (c • a) - c • a) 0 = c * (T *ᵥ a - a) 0 := by
    intro c a
    simp only [Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  obtain ⟨-, rpm, -⟩ := root7_facts hδ
  have hφe : ∀ k : Fin 8, (T *ᵥ Pi.single k 1 - Pi.single k 1 : Coords 8) 0 =
      b8 v (Pi.single k 1) := by
    intro k
    by_cases hk0 : k = 0
    · subst hk0
      exact hφ0
    by_cases hk1 : k = 1
    · subst hk1
      exact hφr _ (root7_facts hδ).1
    have hk : 2 ≤ k.val := by
      have h0' : k.val ≠ 0 := fun e => hk0 (Fin.ext e)
      have h1' : k.val ≠ 1 := fun e => hk1 (Fin.ext e)
      omega
    obtain ⟨l, hl, hkl⟩ : ∃ l : Fin 8, 2 ≤ l.val ∧ k ≠ l := by
      by_cases hk2 : k = 2
      · exact ⟨3, by decide, by rw [hk2]; decide⟩
      · exact ⟨2, by decide, hk2⟩
    have e := hφr _ (rpm k l hk hl hkl).1
    have e' := hφr _ (rpm k l hk hl hkl).2
    have := congrArg (fun w => (T *ᵥ w - w) 0) (two_smul_pm k l)
    simp only at this
    rw [← this, hsmul, hadd, e, e', ← b8_add_right, ← b8_smul_right, two_smul_pm]
  have hTr : T = reflM v := by
    apply matrix_ext_single
    intro k
    rw [hT, hφe, reflM_mulVec, b8_comm]
  refine ⟨hTr, ?_⟩
  have e := congrFun hTv 0
  rw [hTr, reflM_mulVec, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, hy0, smul_eq_mul, mul_one] at e
  have k : ∀ x : ZMod 3, 1 + x = -1 → x = 1 := by decide
  exact k _ e

theorem conj_t0_eq_reflM (h : CoreHyp X) {δ : ZMod 3} (hδ : δ = 1 ∨ δ = -1)
    (horb : ∀ v, v ∈ orb1 X ↔ IsRoot7 δ v) (ht : t ∈ X) (htM : ↑ₘt = t0M)
    {g : GL (Fin 8) (ZMod 3)} (hg : g ∈ X) (hgr : IsRoot7 δ (↑ₘg *ᵥ Pi.single 0 1))
    {y : GL (Fin 8) (ZMod 3)} (hy : y ∈ X) :
    ↑ₘ(y * t * y⁻¹) = reflM (↑ₘy *ᵥ Pi.single 0 1) ∧
      b8 (↑ₘy *ᵥ Pi.single 0 1) (↑ₘy *ᵥ Pi.single 0 1) = 1 := by
  by_cases h0 : (↑ₘy *ᵥ Pi.single 0 1) 0 = 0
  · obtain ⟨hr, he⟩ := conj_t0_of_zero h hδ horb ht htM hy h0
    exact ⟨he, root7_b8 hδ hr⟩
  have k1 : ∀ c : ZMod 3, c ≠ 0 → c * c = 1 := by decide
  by_cases hline : ∀ i : Fin 8, i ≠ 0 → (↑ₘy *ᵥ Pi.single 0 1) i = 0
  · obtain ⟨c, hc⟩ : ∃ c, (↑ₘy *ᵥ Pi.single 0 1) 0 = c := ⟨_, rfl⟩
    have hv : ↑ₘy *ᵥ Pi.single 0 1 = c • Pi.single 0 1 := by
      funext i
      by_cases hi : i = 0
      · subst hi
        simp [hc]
      · simp [hi, hline i hi]
    have hcc : c * c = 1 := k1 c (hc ▸ h0)
    have hyt : y * t * y⁻¹ = t := by
      rw [commute_t0_of_line h ht htM hy hv, mul_assoc, mul_inv_cancel, mul_one]
    rw [hyt, htM, hv, reflM_smul hcc, t0M_eq_reflM, b8_smul_left, b8_smul_right, b8_e0_left,
      Pi.single_eq_same, mul_one, hcc]
    exact ⟨rfl, rfl⟩
  obtain ⟨i, hi, hyi⟩ : ∃ i : Fin 8, i ≠ 0 ∧ (↑ₘy *ᵥ Pi.single 0 1) i ≠ 0 := by
    by_contra hc
    exact hline fun i hi => by
      by_contra hne
      exact hc ⟨i, hi, hne⟩
  have k2 : ∀ c : ZMod 3, c ≠ 0 → c = 1 ∨ c = -1 := by decide
  rcases k2 _ h0 with h1 | h1
  · exact conj_t0_mixed h hδ horb ht htM hg hgr hy h1 hi hyi
  · have hyt : (y * t) * t * (y * t)⁻¹ = y * t * y⁻¹ := by group
    have hv' : ↑ₘ(y * t) *ᵥ Pi.single 0 1 = -(↑ₘy *ᵥ Pi.single 0 1) := by
      rw [mulVec_gmul, htM, t0M_e0, Matrix.mulVec_neg]
    obtain ⟨e1, e2⟩ := conj_t0_mixed h hδ horb ht htM hg hgr (X.mul_mem hy ht)
      (by rw [hv', Pi.neg_apply, h1, neg_neg]) hi (by rw [hv', Pi.neg_apply, neg_ne_zero]; exact hyi)
    rw [hyt, hv'] at e1
    rw [hv', b8_neg_left, b8_neg_right, neg_neg] at e2
    refine ⟨?_, e2⟩
    rw [e1, ← neg_one_smul (ZMod 3), reflM_smul (by decide)]

theorem X_b8 (h : CoreHyp X) {δ : ZMod 3} (hδ : δ = 1 ∨ δ = -1)
    (horb : ∀ v, v ∈ orb1 X ↔ IsRoot7 δ v) (ht : t ∈ X) (htM : ↑ₘt = t0M)
    {g : GL (Fin 8) (ZMod 3)} (hg : g ∈ X) (hgr : IsRoot7 δ (↑ₘg *ᵥ Pi.single 0 1))
    {x : GL (Fin 8) (ZMod 3)} (hx : x ∈ X) (u w : Coords 8) :
    b8 (↑ₘx *ᵥ u) (↑ₘx *ᵥ w) = b8 u w := by
  have key : ∀ y ∈ X, ∀ u : Coords 8, b8 (↑ₘx *ᵥ u) (↑ₘx *ᵥ (↑ₘy *ᵥ Pi.single 0 1)) =
      b8 u (↑ₘy *ᵥ Pi.single 0 1) := by
    intro y hy u
    have h1 := (conj_t0_eq_reflM h hδ horb ht htM hg hgr hy).1
    have h2 := (conj_t0_eq_reflM h hδ horb ht htM hg hgr (X.mul_mem hx hy)).1
    have e : x * y * t * (x * y)⁻¹ = x * (y * t * y⁻¹) * x⁻¹ := by group
    rw [e, Units.val_mul, Units.val_mul, h1, mulVec_gmul] at h2
    have e2 := congrArg (fun A => A *ᵥ (↑ₘx *ᵥ u)) h2
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mulVec_inv_mulVec, reflM_mulVec,
      reflM_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul] at e2
    have hne : ↑ₘx *ᵥ (↑ₘy *ᵥ Pi.single 0 1) ≠ 0 := by
      rw [← mulVec_gmul]
      exact ne_zero_mulVec_e0 (x * y)
    exact (smul_left_injective (ZMod 3) hne (add_left_cancel e2)).symm
  let W : Set (Coords 8) := {w | ∀ u, b8 (↑ₘx *ᵥ u) (↑ₘx *ᵥ w) = b8 u w}
  have hWadd : ∀ a ∈ W, ∀ b ∈ W, a + b ∈ W := by
    intro a ha b hb u
    rw [Matrix.mulVec_add, b8_add_right, b8_add_right, ha u, hb u]
  have hWsmul : ∀ (c : ZMod 3), ∀ a ∈ W, c • a ∈ W := by
    intro c a ha u
    rw [Matrix.mulVec_smul, b8_smul_right, b8_smul_right, ha u]
  have hWroot : ∀ r, IsRoot7 δ r → r ∈ W := by
    intro r hr
    obtain ⟨z, hz, hze⟩ := root_orbit horb hg hgr hr
    rw [← hze]
    exact key z hz
  obtain ⟨r1, rpm, -⟩ := root7_facts hδ
  have hWe : ∀ j : Fin 8, Pi.single j 1 ∈ W := by
    intro j
    by_cases hj0 : j = 0
    · subst hj0
      have := key 1 X.one_mem
      rwa [Units.val_one, Matrix.one_mulVec] at this
    by_cases hj1 : j = 1
    · subst hj1
      exact hWroot _ r1
    have hj : 2 ≤ j.val := by
      have h0' : j.val ≠ 0 := fun e => hj0 (Fin.ext e)
      have h1' : j.val ≠ 1 := fun e => hj1 (Fin.ext e)
      omega
    obtain ⟨l, hl, hjl⟩ : ∃ l : Fin 8, 2 ≤ l.val ∧ j ≠ l := by
      by_cases hj2 : j = 2
      · exact ⟨3, by decide, by rw [hj2]; decide⟩
      · exact ⟨2, by decide, hj2⟩
    rw [← two_smul_pm j l]
    exact hWsmul _ _ (hWadd _ (hWroot _ (rpm j l hj hl hjl).1) _ (hWroot _ (rpm j l hj hl hjl).2))
  exact b8_mulVec_of_gram (fun i j => hWe j (Pi.single i 1)) u w

end T0

end CFSG.StandardType.FrameRoute.FS81.E7Row

end
