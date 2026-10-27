module

public import CFSG.LocalAnalysis.StandardType.FS81.E7RowE1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81.E7Row

open scoped Matrix

local notation:max "↑ₘ" g:max => ((g : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3))

variable {X : Subgroup (GL (Fin 8) (ZMod 3))}

@[expose] def Ord23 {G : Type*} [Monoid G] (p : G) : Prop := p * p = 1 ∨ p * p * p = 1

theorem ord23_conj {G : Type*} [Group G] (x p : G) : Ord23 (x * p * x⁻¹) ↔ Ord23 p := by
  have e2 : x * p * x⁻¹ * (x * p * x⁻¹) = x * (p * p) * x⁻¹ := by group
  have e3 : x * p * x⁻¹ * (x * p * x⁻¹) * (x * p * x⁻¹) = x * (p * p * p) * x⁻¹ := by group
  unfold Ord23
  rw [e3, e2, conj_eq_one_iff, conj_eq_one_iff]

theorem reflM_iso {p : Coords 8} (hp : b8 p p = 1) (u w : Coords 8) :
    b8 (reflM p *ᵥ u) (reflM p *ᵥ w) = b8 u w := by
  simp only [reflM_mulVec, b8_add_left, b8_add_right, b8_smul_left, b8_smul_right, hp]
  rw [b8_comm p w]
  generalize b8 u p = x
  generalize b8 w p = y
  generalize b8 u w = a
  revert a x y
  decide

theorem reflM_smul {c : ZMod 3} (hc : c * c = 1) (v : Coords 8) : reflM (c • v) = reflM v := by
  apply matrix_ext_mulVec
  intro w
  rw [reflM_mulVec, reflM_mulVec, b8_smul_right, smul_smul, mul_comm, ← mul_assoc, hc, one_mul]

theorem reflM_conj {p : Coords 8} (hp : b8 p p = 1) (q : Coords 8) :
    reflM p * reflM q * reflM p = reflM (reflM p *ᵥ q) := by
  have hpp : ∀ x : Coords 8, reflM p *ᵥ (reflM p *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, reflM_mul_self hp, Matrix.one_mulVec]
  apply matrix_ext_mulVec
  intro w
  have hb : b8 (reflM p *ᵥ w) q = b8 w (reflM p *ᵥ q) := by
    conv_lhs => rw [← hpp q]
    rw [reflM_iso hp]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, reflM_mulVec q, Matrix.mulVec_add,
    Matrix.mulVec_smul, hpp, hb, reflM_mulVec (reflM p *ᵥ q)]

theorem reflM_pair {p q : Coords 8} (hp : b8 p p = 1) (hq : b8 q q = 1) :
    Ord23 (reflM p * reflM q) := by
  have hp2 := reflM_mul_self hp
  have hq2 := reflM_mul_self hq
  have hpq : reflM p *ᵥ q = q + b8 q p • p := reflM_mulVec p q
  have hqp : reflM q *ᵥ p = p + b8 q p • q := by rw [reflM_mulVec, b8_comm]
  by_cases hc : b8 q p = 0
  · left
    have hcomm : reflM p * reflM q * reflM p = reflM q := by
      rw [reflM_conj hp, hpq, hc, zero_smul, add_zero]
    calc reflM p * reflM q * (reflM p * reflM q) = (reflM p * reflM q * reflM p) * reflM q := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hcomm, hq2]
  · right
    have hc2 : b8 q p * b8 q p = 1 := by
      have k : ∀ c : ZMod 3, c ≠ 0 → c * c = 1 := by decide
      exact k _ hc
    have hbr : reflM p * reflM q * reflM p = reflM q * reflM p * reflM q := by
      rw [reflM_conj hp, reflM_conj hq, hqp, hpq]
      rw [show q + b8 q p • p = b8 q p • (p + b8 q p • q) by
        rw [smul_add, smul_smul, hc2, one_smul, add_comm]]
      exact reflM_smul hc2 _
    calc reflM p * reflM q * (reflM p * reflM q) * (reflM p * reflM q)
        = (reflM p * reflM q * reflM p) * (reflM q * reflM p * reflM q) := by
          simp only [Matrix.mul_assoc]
      _ = (reflM q * reflM p * reflM q) * (reflM q * reflM p * reflM q) := by rw [hbr]
      _ = 1 := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (reflM q) (reflM q), hq2, Matrix.one_mul,
            ← Matrix.mul_assoc (reflM p) (reflM p), hp2, Matrix.one_mul, hq2]

theorem exists_fixed_d60 {A : Matrix (Fin 8) (Fin 8) (ZMod 3)} {b : Coords 8}
    (hrank : ∀ w : Coords 8, ∃ c : ZMod 3, A *ᵥ w - w = c • b) :
    ∃ i j : Fin 8, 2 ≤ i.val ∧ 2 ≤ j.val ∧ i ≠ j ∧ ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧
      A *ᵥ (Pi.single i 1 + ε • Pi.single j 1) = Pi.single i 1 + ε • Pi.single j 1 := by
  obtain ⟨c2, h2⟩ := hrank (Pi.single 2 1)
  obtain ⟨c3, h3⟩ := hrank (Pi.single 3 1)
  obtain ⟨c4, h4⟩ := hrank (Pi.single 4 1)
  have key : ∀ (i j : Fin 8) (ci cj ε : ZMod 3), A *ᵥ Pi.single i 1 - Pi.single i 1 = ci • b →
      A *ᵥ Pi.single j 1 - Pi.single j 1 = cj • b → ci + ε * cj = 0 →
      A *ᵥ (Pi.single i 1 + ε • Pi.single j 1) = Pi.single i 1 + ε • Pi.single j 1 := by
    intro i j ci cj ε hi hj hc
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, ← sub_eq_zero]
    have : A *ᵥ Pi.single i 1 + ε • A *ᵥ Pi.single j 1 - (Pi.single i 1 + ε • Pi.single j 1) =
        (A *ᵥ Pi.single i 1 - Pi.single i 1) + ε • (A *ᵥ Pi.single j 1 - Pi.single j 1) := by
      rw [smul_sub]
      abel
    rw [this, hi, hj, smul_smul, ← add_smul, hc, zero_smul]
  have pig : ∀ x y z : ZMod 3, (∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧ x + ε * y = 0) ∨
      (∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧ x + ε * z = 0) ∨
      (∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧ y + ε * z = 0) := by decide
  rcases pig c2 c3 c4 with ⟨ε, hε, he⟩ | ⟨ε, hε, he⟩ | ⟨ε, hε, he⟩
  · exact ⟨2, 3, by decide, by decide, by decide, ε, hε, key 2 3 c2 c3 ε h2 h3 he⟩
  · exact ⟨2, 4, by decide, by decide, by decide, ε, hε, key 2 4 c2 c4 ε h2 h4 he⟩
  · exact ⟨3, 4, by decide, by decide, by decide, ε, hε, key 3 4 c3 c4 ε h3 h4 he⟩

theorem root7_pm {δ : ZMod 3} (hδ : δ = 1 ∨ δ = -1) {i j : Fin 8} (hi : 2 ≤ i.val) (hj : 2 ≤ j.val)
    (hij : i ≠ j) {ε : ZMod 3} (hε : ε = 1 ∨ ε = -1) :
    IsRoot7 δ (Pi.single i 1 + ε • Pi.single j 1) := by
  obtain ⟨-, rpm, -⟩ := root7_facts hδ
  rcases hε with rfl | rfl
  · rw [one_smul]
    exact (rpm i j hi hj hij).1
  · rw [neg_one_smul, ← sub_eq_add_neg]
    exact (rpm i j hi hj hij).2

section T0

variable {t : GL (Fin 8) (ZMod 3)}

theorem t_mul_self (htM : ↑ₘt = t0M) : t * t = 1 :=
  Units.ext (by rw [Units.val_mul, htM, t0M_mul_self, Units.val_one])

theorem ne_zero_mulVec_e0 (y : GL (Fin 8) (ZMod 3)) : ↑ₘy *ᵥ (Pi.single 0 1 : Coords 8) ≠ 0 := by
  intro e
  have := mulVec_inv_mulVec y (Pi.single 0 1)
  rw [e, Matrix.mulVec_zero] at this
  have := congrFun this 0
  simp at this

theorem line_of_t0M_neg {v : Coords 8} (hv : t0M *ᵥ v = -v) : v = v 0 • Pi.single 0 1 := by
  funext i
  by_cases hi : i = 0
  · subst hi
    simp
  · have e := congrFun hv i
    rw [t0M_mulVec] at e
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hi, smul_zero, add_zero,
      Pi.neg_apply] at e
    have k : ∀ x : ZMod 3, x = -x → x = 0 := by decide
    rw [Pi.smul_apply, Pi.single_eq_of_ne hi, smul_zero]
    exact k _ e

theorem commute_t0_of_X1 (h : CoreHyp X) (htM : ↑ₘt = t0M) {x : GL (Fin 8) (ZMod 3)}
    (hx : x ∈ X ⊓ fixE0 7) : x * t = t * x := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, htM]
  apply ext_e0
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, t0M_e0, Matrix.mulVec_neg,
      mem_fixE0.mp hx.2, t0M_e0]
  · intro w hw
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, t0M_fix hw,
      t0M_fix (h.hA x hx.1 (mem_fixE0.mp hx.2) w hw)]

theorem commute_t0_of_line (h : CoreHyp X) (ht : t ∈ X) (htM : ↑ₘt = t0M)
    {y : GL (Fin 8) (ZMod 3)} (hy : y ∈ X) {c : ZMod 3}
    (hyc : ↑ₘy *ᵥ Pi.single 0 1 = c • Pi.single 0 1) : y * t = t * y := by
  have k : ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = -1 := by decide
  rcases k c with rfl | rfl | rfl
  · rw [zero_smul] at hyc
    exact absurd hyc (ne_zero_mulVec_e0 y)
  · rw [one_smul] at hyc
    exact commute_t0_of_X1 h htM ⟨hy, mem_fixE0.mpr hyc⟩
  · have hty : t * y ∈ X ⊓ fixE0 7 := by
      refine ⟨X.mul_mem ht hy, mem_fixE0.mpr ?_⟩
      rw [mulVec_gmul, hyc, Matrix.mulVec_smul, htM, t0M_e0, smul_neg, neg_one_smul, neg_neg]
    have hc := commute_t0_of_X1 h htM hty
    apply mul_left_cancel (a := t)
    rw [← mul_assoc, hc]

theorem conj_t0_eq (h : CoreHyp X) (ht : t ∈ X) (htM : ↑ₘt = t0M) {y z : GL (Fin 8) (ZMod 3)}
    (hy : y ∈ X) (hz : z ∈ X) {c : ZMod 3}
    (hyz : ↑ₘy *ᵥ Pi.single 0 1 = c • (↑ₘz *ᵥ Pi.single 0 1)) : y * t * y⁻¹ = z * t * z⁻¹ := by
  have hw : z⁻¹ * y ∈ X := X.mul_mem (X.inv_mem hz) hy
  have hwc : ↑ₘ(z⁻¹ * y) *ᵥ Pi.single 0 1 = c • Pi.single 0 1 := by
    rw [mulVec_gmul, hyz, Matrix.mulVec_smul, mulVec_inv_mulVec]
  have hcomm := commute_t0_of_line h ht htM hw hwc
  calc y * t * y⁻¹ = z * ((z⁻¹ * y) * t) * (z⁻¹ * y)⁻¹ * z⁻¹ := by group
    _ = z * (t * (z⁻¹ * y)) * (z⁻¹ * y)⁻¹ * z⁻¹ := by rw [hcomm]
    _ = z * t * z⁻¹ := by group

theorem conj_t0_mulVec (htM : ↑ₘt = t0M) (y : GL (Fin 8) (ZMod 3)) (w : Coords 8) :
    ↑ₘ(y * t * y⁻¹) *ᵥ w = w + (↑ₘ(y⁻¹) *ᵥ w) 0 • (↑ₘy *ᵥ Pi.single 0 1) := by
  rw [mulVec_gmul, mulVec_gmul, htM, t0M_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul,
    mulVec_mulVec_inv]

theorem axis_conj_t0 (htM : ↑ₘt = t0M) (y : GL (Fin 8) (ZMod 3)) :
    IsAxis ↑ₘ(y * t * y⁻¹) (↑ₘy *ᵥ Pi.single 0 1) := by
  refine ⟨ne_zero_mulVec_e0 y, ?_, fun w => ⟨(↑ₘ(y⁻¹) *ᵥ w) 0, ?_⟩⟩
  · rw [conj_t0_mulVec htM, mulVec_inv_mulVec, Pi.single_eq_same, one_smul, vec_neg_eq]
  · rw [conj_t0_mulVec htM]
    abel

theorem conj_t0_mul_self (htM : ↑ₘt = t0M) (y : GL (Fin 8) (ZMod 3)) :
    y * t * y⁻¹ * (y * t * y⁻¹) = 1 := by
  rw [show y * t * y⁻¹ * (y * t * y⁻¹) = y * (t * t) * y⁻¹ by group, t_mul_self htM, mul_one,
    mul_inv_cancel]

theorem exists_root_orbit (h : CoreHyp X) {δ : ZMod 3} (hδ : δ = 1 ∨ δ = -1)
    (horb : ∀ v, v ∈ orb1 X ↔ IsRoot7 δ v)
    (hodd : ∀ N : Subgroup ↥X, N.Normal → Odd (Nat.card N) → N = ⊥)
    (hmove : ∃ x ∈ X, ∃ i : Fin 8, i ≠ 0 ∧ (↑ₘx *ᵥ Pi.single 0 1) i ≠ 0)
    (ht : t ∈ X) (htM : ↑ₘt = t0M) : ∃ g ∈ X, IsRoot7 δ (↑ₘg *ᵥ Pi.single 0 1) := by
  classical
  have hnot : ∃ g ∈ X, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) ∧ g * t * g⁻¹ ≠ t := by
    by_contra hiso'
    have hiso : ∀ g ∈ X, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t := by
      intro g hg hc
      by_contra hne
      exact hiso' ⟨g, hg, hc, hne⟩
    let tt : ↥X := ⟨t, ht⟩
    have : Fintype ↥X := Fintype.ofFinite _
    have ht1 : tt ≠ 1 := by
      intro e
      have e' : ↑ₘt = 1 := by
        have := congrArg (fun y : ↥X => ((y : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3))) e
        simpa [tt] using this
      have := congrFun (congrFun e' 0) 0
      rw [htM, t0M, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at this
      exact absurd this (by decide)
    have ht2 : tt * tt = 1 := Subtype.ext (t_mul_self htM)
    obtain ⟨N, hN, hNo, hNt⟩ := CFSG.ZStar.glauberman_zStar ↥X tt ht1 ht2 (fun g hg => by
      apply Subtype.ext
      exact hiso g g.2 (congrArg Subtype.val hg))
    have hN1 := hodd N hN hNo
    obtain ⟨x, hxX, i, hi, hxi⟩ := hmove
    have hc := hNt ⟨x, hxX⟩
    rw [hN1, Subgroup.mem_bot, mul_inv_eq_one] at hc
    have hc' : x * t * x⁻¹ = t := congrArg Subtype.val hc
    have hxc : x * t = t * x :=
      calc x * t = (x * t * x⁻¹) * x := by group
        _ = t * x := by rw [hc']
    have hneg : t0M *ᵥ (↑ₘx *ᵥ Pi.single 0 1) = -(↑ₘx *ᵥ Pi.single 0 1) := by
      rw [← htM, ← mulVec_gmul, ← hxc, mulVec_gmul, htM, t0M_e0, Matrix.mulVec_neg]
    apply hxi
    have := congrFun (line_of_t0M_neg hneg) i
    rw [Pi.smul_apply, Pi.single_eq_of_ne hi, smul_zero] at this
    exact this
  obtain ⟨g, hg, hcomm, hne⟩ := hnot
  have hTc : ↑ₘ(g * t * g⁻¹) * t0M = t0M * ↑ₘ(g * t * g⁻¹) := by
    rw [← htM, ← Units.val_mul, ← Units.val_mul, hcomm]
  have hfix : ↑ₘ(g * t * g⁻¹) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
    have hneg : t0M *ᵥ (↑ₘ(g * t * g⁻¹) *ᵥ Pi.single 0 1) =
        -(↑ₘ(g * t * g⁻¹) *ᵥ Pi.single 0 1) := by
      rw [Matrix.mulVec_mulVec, ← hTc, ← Matrix.mulVec_mulVec, t0M_e0, Matrix.mulVec_neg]
    have hline := line_of_t0M_neg hneg
    obtain ⟨d, hd⟩ := (axis_conj_t0 htM g).2.2 (Pi.single 0 1)
    generalize (↑ₘ(g * t * g⁻¹) *ᵥ Pi.single 0 1) 0 = c at hline
    rw [hline] at hd ⊢
    by_cases hc1 : c = 1
    · rw [hc1, one_smul]
    exfalso
    apply hne
    have hd0 : d ≠ 0 := by
      rintro rfl
      have e := congrFun hd 0
      simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
        zero_mul] at e
      exact hc1 (sub_eq_zero.mp e)
    have hdd : d * d = 1 := by
      have k : ∀ c : ZMod 3, c ≠ 0 → c * c = 1 := by decide
      exact k _ hd0
    have hge : ↑ₘg *ᵥ Pi.single 0 1 =
        (d * (c - 1)) • (↑ₘ(1 : GL (Fin 8) (ZMod 3)) *ᵥ Pi.single 0 1) := by
      rw [Units.val_one, Matrix.one_mulVec, mul_smul, sub_smul, one_smul, hd, smul_smul, hdd,
        one_smul]
    exact (conj_t0_eq h ht htM hg X.one_mem hge).trans (by group)
  exact ⟨g, hg, axis_root_of_X1 h hδ horb ⟨X.mul_mem (X.mul_mem hg ht) (X.inv_mem hg),
    mem_fixE0.mpr hfix⟩ (conj_t0_mul_self htM g) (axis_conj_t0 htM g)⟩

theorem root_orbit {δ : ZMod 3} (horb : ∀ v, v ∈ orb1 X ↔ IsRoot7 δ v) {g : GL (Fin 8) (ZMod 3)}
    (hg : g ∈ X) (hgr : IsRoot7 δ (↑ₘg *ᵥ Pi.single 0 1)) {r : Coords 8} (hr : IsRoot7 δ r) :
    ∃ y ∈ X, ↑ₘy *ᵥ Pi.single 0 1 = r := by
  obtain ⟨x₀, hx₀, hx₀e⟩ := (horb _).mpr hgr
  obtain ⟨x₁, hx₁, hx₁e⟩ := (horb _).mpr hr
  refine ⟨x₁ * x₀⁻¹ * g, X.mul_mem (X.mul_mem hx₁.1 (X.inv_mem hx₀.1)) hg, ?_⟩
  rw [mulVec_gmul, mulVec_gmul, ← hx₀e, mulVec_inv_mulVec, hx₁e]

theorem conj_t0_of_zero (h : CoreHyp X) {δ : ZMod 3} (hδ : δ = 1 ∨ δ = -1)
    (horb : ∀ v, v ∈ orb1 X ↔ IsRoot7 δ v) (ht : t ∈ X) (htM : ↑ₘt = t0M)
    {y : GL (Fin 8) (ZMod 3)} (hy : y ∈ X) (hy0 : (↑ₘy *ᵥ Pi.single 0 1) 0 = 0) :
    IsRoot7 δ (↑ₘy *ᵥ Pi.single 0 1) ∧ ↑ₘ(y * t * y⁻¹) = reflM (↑ₘy *ᵥ Pi.single 0 1) := by
  have hc : (t * y) * t * (t * y)⁻¹ = y * t * y⁻¹ :=
    conj_t0_eq h ht htM (X.mul_mem ht hy) hy (c := 1)
      (by rw [one_smul, mulVec_gmul, htM, t0M_fix hy0])
  have hcomm : t * (y * t * y⁻¹) = (y * t * y⁻¹) * t :=
    calc t * (y * t * y⁻¹) = ((t * y) * t * (t * y)⁻¹) * t := by group
      _ = (y * t * y⁻¹) * t := by rw [hc]
  have hTc : t0M * ↑ₘ(y * t * y⁻¹) = ↑ₘ(y * t * y⁻¹) * t0M := by
    rw [← htM, ← Units.val_mul, ← Units.val_mul, hcomm]
  have hfix : ↑ₘ(y * t * y⁻¹) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
    have hneg : t0M *ᵥ (↑ₘ(y * t * y⁻¹) *ᵥ Pi.single 0 1) =
        -(↑ₘ(y * t * y⁻¹) *ᵥ Pi.single 0 1) := by
      rw [Matrix.mulVec_mulVec, hTc, ← Matrix.mulVec_mulVec, t0M_e0, Matrix.mulVec_neg]
    have hline := line_of_t0M_neg hneg
    obtain ⟨d, hd⟩ := (axis_conj_t0 htM y).2.2 (Pi.single 0 1)
    have e := congrFun hd 0
    rw [hline] at e
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, hy0,
      mul_zero] at e
    rw [hline, sub_eq_zero.mp e, one_smul]
  exact reflM_of_X1 h hδ horb ⟨X.mul_mem (X.mul_mem hy ht) (X.inv_mem hy), mem_fixE0.mpr hfix⟩
    (conj_t0_mul_self htM y) (axis_conj_t0 htM y)

theorem conj_t0_pair (h : CoreHyp X) {δ : ZMod 3} (hδ : δ = 1 ∨ δ = -1)
    (horb : ∀ v, v ∈ orb1 X ↔ IsRoot7 δ v) (ht : t ∈ X) (htM : ↑ₘt = t0M)
    {g : GL (Fin 8) (ZMod 3)} (hg : g ∈ X) (hgr : IsRoot7 δ (↑ₘg *ᵥ Pi.single 0 1))
    {y z : GL (Fin 8) (ZMod 3)} (hy : y ∈ X) (hz : z ∈ X) :
    Ord23 (y * t * y⁻¹ * (z * t * z⁻¹)) := by
  have hw : z⁻¹ * y ∈ X := X.mul_mem (X.inv_mem hz) hy
  rw [show y * t * y⁻¹ * (z * t * z⁻¹) = z * ((z⁻¹ * y) * t * (z⁻¹ * y)⁻¹ * t) * z⁻¹ by group,
    ord23_conj]
  obtain ⟨i, j, hi, hj, hij, ε, hε, hd⟩ := exists_fixed_d60 (axis_conj_t0 htM (z⁻¹ * y)).2.2
  have hdr := root7_pm hδ hi hj hij hε
  obtain ⟨k, hk, hke⟩ := root_orbit horb hg hgr hdr
  have hd0 : (Pi.single i 1 + ε • Pi.single j 1 : Coords 8) 0 = 0 := hdr.1
  have ha : k⁻¹ * ((z⁻¹ * y) * t * (z⁻¹ * y)⁻¹) * k = (k⁻¹ * (z⁻¹ * y)) * t * (k⁻¹ * (z⁻¹ * y))⁻¹ := by
    group
  have hb : k⁻¹ * t * k = k⁻¹ * t * (k⁻¹)⁻¹ := by group
  have haX : (k⁻¹ * (z⁻¹ * y)) * t * (k⁻¹ * (z⁻¹ * y))⁻¹ ∈ X ⊓ fixE0 7 := by
    refine ⟨X.mul_mem (X.mul_mem (X.mul_mem (X.inv_mem hk) hw) ht)
      (X.inv_mem (X.mul_mem (X.inv_mem hk) hw)), mem_fixE0.mpr ?_⟩
    rw [← ha, mulVec_gmul, mulVec_gmul, hke, hd, ← hke, mulVec_inv_mulVec]
  have hbX : k⁻¹ * t * (k⁻¹)⁻¹ ∈ X ⊓ fixE0 7 := by
    refine ⟨X.mul_mem (X.mul_mem (X.inv_mem hk) ht) (X.inv_mem (X.inv_mem hk)), mem_fixE0.mpr ?_⟩
    rw [← hb, mulVec_gmul, mulVec_gmul, hke, htM, t0M_fix hd0, ← hke, mulVec_inv_mulVec]
  obtain ⟨hpr, hpa⟩ := reflM_of_X1 h hδ horb haX (conj_t0_mul_self htM _) (axis_conj_t0 htM _)
  obtain ⟨hqr, hqb⟩ := reflM_of_X1 h hδ horb hbX (conj_t0_mul_self htM _) (axis_conj_t0 htM _)
  have hpair := reflM_pair (root7_b8 hδ hpr) (root7_b8 hδ hqr)
  rw [← hpa, ← hqb, ← ha, ← hb, ← Units.val_mul] at hpair
  have hpair' : Ord23 (k⁻¹ * ((z⁻¹ * y) * t * (z⁻¹ * y)⁻¹) * k * (k⁻¹ * t * k)) := by
    rcases hpair with e | e
    · left
      exact Units.ext (by rw [Units.val_mul, e, Units.val_one])
    · right
      exact Units.ext (by rw [Units.val_mul, Units.val_mul, e, Units.val_one])
  rw [show k⁻¹ * ((z⁻¹ * y) * t * (z⁻¹ * y)⁻¹) * k * (k⁻¹ * t * k) =
    k⁻¹ * ((z⁻¹ * y) * t * (z⁻¹ * y)⁻¹ * t) * k⁻¹⁻¹ by group, ord23_conj] at hpair'
  exact hpair'

end T0

end CFSG.StandardType.FrameRoute.FS81.E7Row

end
