module

public import CFSG.LocalAnalysis.StandardType.FS81.E7RowA5
public import CFSG.LocalAnalysis.ZStar
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81.E7Row

open scoped Matrix

local notation:max "↑ₘ" g:max => ((g : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3))

variable {X : Subgroup (GL (Fin 8) (ZMod 3))}

@[expose] def sref (a w : Coords 8) : Coords 8 := w + (b8 w a * b8 a a) • a

theorem vec_neg_eq (v : Coords 8) : -v = v + v := by
  funext i
  exact zmod3_neg_eq (v i)

theorem eq_zero_of_b8 {a : Coords 8} (h : ∀ w : Coords 8, b8 w a = 0) : a = 0 := by
  funext j
  have e := h (Pi.single j 1)
  rw [b8_comm, b8_single] at e
  have k1 : ∀ x : ZMod 3, x * 1 = 0 → x = 0 := by decide
  have k2 : ∀ x : ZMod 3, x * 2 = 0 → x = 0 := by decide
  split_ifs at e
  · exact k1 _ e
  · exact k2 _ e

theorem sref_of_axis {A : Matrix (Fin 8) (Fin 8) (ZMod 3)}
    (hiso : ∀ u w : Coords 8, b8 (A *ᵥ u) (A *ᵥ w) = b8 u w) {a : Coords 8} (ha : IsAxis A a) :
    b8 a a ≠ 0 ∧ ∀ w, A *ᵥ w = sref a w := by
  obtain ⟨ha0, hneg, hrank⟩ := ha
  have key : ∀ w : Coords 8, ∀ c : ZMod 3, A *ᵥ w - w = c • a → c * b8 a a = b8 w a := by
    intro w c hc
    have hw : A *ᵥ w = w + c • a := by rw [← hc]; abel
    have e := hiso w a
    rw [hneg, hw, b8_neg_right, b8_add_left, b8_smul_left] at e
    have k : ∀ x y : ZMod 3, -(x + y) = x → y = x := by decide
    exact k _ _ e
  have hq : b8 a a ≠ 0 := by
    intro h0
    apply ha0
    apply eq_zero_of_b8
    intro w
    obtain ⟨c, hc⟩ := hrank w
    rw [← key w c hc, h0, mul_zero]
  refine ⟨hq, fun w => ?_⟩
  obtain ⟨c, hc⟩ := hrank w
  have k : ∀ c q b : ZMod 3, q ≠ 0 → c * q = b → c = b * q := by decide
  rw [sref, ← k c _ _ hq (key w c hc), ← hc]
  abel

theorem reflM_mul_self {r : Coords 8} (hr : b8 r r = 1) : reflM r * reflM r = 1 := by
  apply matrix_ext_mulVec
  intro w
  rw [← Matrix.mulVec_mulVec, reflM_mulVec, reflM_mulVec, Matrix.one_mulVec, b8_add_left,
    b8_smul_left, hr]
  have k : ∀ x : ZMod 3, x + (x + x * 1) = 0 := by decide
  rw [add_assoc, ← add_smul, k, zero_smul, add_zero]

theorem reflM_mulVec_self {r : Coords 8} (hr : b8 r r = 1) : reflM r *ᵥ r = -r := by
  rw [reflM_mulVec, hr, one_smul, vec_neg_eq]

theorem sref_eq_reflM {a : Coords 8} (ha : b8 a a = 1) (w : Coords 8) : sref a w = reflM a *ᵥ w := by
  rw [sref, reflM_mulVec, ha, mul_one]

theorem root7_ne_zero {δ : ZMod 3} (hδ : δ = 1 ∨ δ = -1) {r : Coords 8} (hr : IsRoot7 δ r) : r ≠ 0 := by
  rintro rfl
  have := root7_q hδ 0 hr
  rw [qE8_eq] at this
  exact absurd this (by decide)

theorem root7_b8 {δ : ZMod 3} (hδ : δ = 1 ∨ δ = -1) {r : Coords 8} (hr : IsRoot7 δ r) : b8 r r = 1 := by
  rw [b8_self, root7_q hδ r hr]
  decide

theorem b8_e0_left (w : Coords 8) : b8 (Pi.single 0 1) w = w 0 := by
  rw [b8_comm, b8_single]
  simp

@[expose] def PresRoots (δ : ZMod 3) (a : Coords 8) : Prop :=
  ∀ r, IsRoot7 δ r → IsRoot7 δ (sref a r)

@[expose] def b8e (x y : Coords 8) : ZMod 3 := x 0 * y 0 + x 1 * y 1 +
  2 * (x 2 * y 2 + x 3 * y 3 + x 4 * y 4 + x 5 * y 5 + x 6 * y 6 + x 7 * y 7)

@[expose] def srefe (a w : Coords 8) : Coords 8 := w + (b8e w a * b8e a a) • a

theorem b8_eq_b8e (x y : Coords 8) : b8 x y = b8e x y := by
  rw [b8_eq]
  rfl

theorem sref_eq_srefe (a w : Coords 8) : sref a w = srefe a w := by
  rw [sref, srefe, b8_eq_b8e, b8_eq_b8e]

@[expose] def wlist (δ : ZMod 3) : List (Coords 8) :=
  [fRoot δ, Pi.single 5 1 + Pi.single 7 1, Pi.single 6 1 + Pi.single 7 1,
    Pi.single 3 1 + Pi.single 7 1, Pi.single 4 1 + Pi.single 7 1, Pi.single 6 1 - Pi.single 7 1]

set_option maxRecDepth 100000 in
theorem wlist_roots {δ : ZMod 3} (hδ : δ = 1 ∨ δ = -1) : ∀ r ∈ wlist δ, IsRoot7 δ r := by
  rcases hδ with rfl | rfl <;> decide +kernel

set_option maxRecDepth 100000 in
theorem cand_presRoots {δ : ZMod 3} (hδ : δ = 1 ∨ δ = -1) : ∀ n : Fin 16,
    b8e (cand n) (cand n) ≠ 0 → (∀ r ∈ wlist δ, IsRoot7 δ (srefe (cand n) r)) →
      IsRoot7 δ (cand n) := by
  rcases hδ with rfl | rfl <;> decide +kernel

theorem Gen.act_add (g : Gen) (v w : Coords 8) : g.act (v + w) = g.act v + g.act w := by
  rw [← Gen.mat_mulVec, ← Gen.mat_mulVec, ← Gen.mat_mulVec, Matrix.mulVec_add]

theorem Gen.act_smul (g : Gen) (c : ZMod 3) (v : Coords 8) : g.act (c • v) = c • g.act v := by
  rw [← Gen.mat_mulVec, ← Gen.mat_mulVec, Matrix.mulVec_smul]

theorem Gen.act_zero_coord {g : Gen} (hg : g.Valid) {v : Coords 8} (hv : v 0 = 0) :
    (g.act v) 0 = 0 := by
  rw [← Gen.mat_mulVec]
  exact hSeven_mulVec_zero (Gen.mat_mem hg) hv

theorem Gen.b8_act (h : CoreHyp X) {δ : ZMod 3} (hδ : δ = 1 ∨ δ = -1)
    (horb : ∀ v, v ∈ orb1 X ↔ IsRoot7 δ v) {g : Gen} (hg : g.Valid) (u w : Coords 8) :
    b8 (g.act u) (g.act w) = b8 u w := by
  obtain ⟨x, hx, hxA⟩ := h.exists_fix (Gen.mat_mem hg)
  rw [← Gen.mat_mulVec, ← Gen.mat_mulVec, ← hxA]
  exact X1_b8 h hδ horb hx u w

theorem Gen.isRoot7_act (h : CoreHyp X) {δ : ZMod 3} (horb : ∀ v, v ∈ orb1 X ↔ IsRoot7 δ v)
    {g : Gen} (hg : g.Valid) (v : Coords 8) : IsRoot7 δ (g.act v) ↔ IsRoot7 δ v := by
  constructor
  · intro hv
    have := orb1_gen h hg ((horb _).mpr hv)
    rw [Gen.act_act] at this
    exact (horb v).mp this
  · intro hv
    exact (horb _).mp (orb1_gen h hg ((horb v).mpr hv))

theorem Gen.sref_act (h : CoreHyp X) {δ : ZMod 3} (hδ : δ = 1 ∨ δ = -1)
    (horb : ∀ v, v ∈ orb1 X ↔ IsRoot7 δ v) {g : Gen} (hg : g.Valid) (a w : Coords 8) :
    sref (g.act a) (g.act w) = g.act (sref a w) := by
  rw [sref, sref, Gen.b8_act h hδ horb hg, Gen.b8_act h hδ horb hg, Gen.act_add, Gen.act_smul]

theorem Gen.presRoots_act (h : CoreHyp X) {δ : ZMod 3} (hδ : δ = 1 ∨ δ = -1)
    (horb : ∀ v, v ∈ orb1 X ↔ IsRoot7 δ v) {g : Gen} (hg : g.Valid) {a : Coords 8}
    (ha : PresRoots δ a) : PresRoots δ (g.act a) := by
  intro r hr
  have hr' : IsRoot7 δ (g.act r) := (Gen.isRoot7_act h horb hg r).mpr hr
  have := ha _ hr'
  rw [← Gen.isRoot7_act h horb hg, ← Gen.sref_act h hδ horb hg, Gen.act_act] at this
  exact this

theorem root_of_presRoots (h : CoreHyp X) {δ : ZMod 3} (hδ : δ = 1 ∨ δ = -1)
    (horb : ∀ v, v ∈ orb1 X ↔ IsRoot7 δ v) {a : Coords 8} (ha0 : a 0 = 0) (hq : b8 a a ≠ 0)
    (hP : PresRoots δ a) : IsRoot7 δ a := by
  let Ω : Set (Coords 8) := {a | a 0 = 0 ∧ b8 a a ≠ 0 ∧ PresRoots δ a}
  have hΩ : ∀ g : Gen, g.Valid → ∀ v ∈ Ω, g.act v ∈ Ω := by
    rintro g hg v ⟨hv0, hvq, hvP⟩
    refine ⟨Gen.act_zero_coord hg hv0, ?_, Gen.presRoots_act h hδ horb hg hvP⟩
    rw [Gen.b8_act h hδ horb hg]
    exact hvq
  have hnf : nf a ∈ Ω := (mem_iff_nf_mem hΩ a).mp ⟨ha0, hq, hP⟩
  obtain ⟨n, hn⟩ := nf_mem_cand a ha0
  rw [hn] at hnf
  obtain ⟨-, hq', hP'⟩ := hnf
  have hc := cand_presRoots hδ n (by rw [← b8_eq_b8e]; exact hq')
    (fun r hr => by rw [← sref_eq_srefe]; exact hP' r (wlist_roots hδ r hr))
  obtain ⟨-, hc⟩ := hc
  rw [(nf_cand n).1] at hc
  refine ⟨ha0, ?_⟩
  rw [hn]
  exact hc

theorem reflM_of_X1 (h : CoreHyp X) {δ : ZMod 3} (hδ : δ = 1 ∨ δ = -1)
    (horb : ∀ v, v ∈ orb1 X ↔ IsRoot7 δ v) {g : GL (Fin 8) (ZMod 3)} (hg : g ∈ X ⊓ fixE0 7)
    (hg2 : g * g = 1) {r : Coords 8} (hr : IsAxis ↑ₘg r) : IsRoot7 δ r ∧ ↑ₘg = reflM r := by
  have hroot := axis_root_of_X1 h hδ horb hg hg2 hr
  refine ⟨hroot, matrix_ext_mulVec fun w => ?_⟩
  rw [(sref_of_axis (X1_b8 h hδ horb hg) hr).2 w, sref_eq_reflM (root7_b8 hδ hroot)]

@[expose] def tauM : Matrix (Fin 8) (Fin 8) (ZMod 3) :=
  Matrix.diagonal fun i => if i = 0 then 1 else -1

@[expose] def t0M : Matrix (Fin 8) (Fin 8) (ZMod 3) :=
  Matrix.diagonal fun i => if i = 0 then -1 else 1

theorem tauM_mulVec (v : Coords 8) : tauM *ᵥ v = -v - v 0 • Pi.single 0 1 := by
  funext i
  rw [tauM, Matrix.mulVec_diagonal]
  by_cases hi : i = 0
  · subst hi
    simp only [if_true, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
      mul_one, one_mul]
    rw [zmod3_neg_eq]
    abel_nf
  · simp [hi]

theorem t0M_mulVec (v : Coords 8) : t0M *ᵥ v = v + v 0 • Pi.single 0 1 := by
  funext i
  rw [t0M, Matrix.mulVec_diagonal]
  by_cases hi : i = 0
  · subst hi
    simp only [if_true, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    rw [zmod3_neg_eq]
    ring
  · simp [hi]

theorem t0M_eq_reflM : t0M = reflM (Pi.single 0 1) := by
  apply matrix_ext_mulVec
  intro w
  rw [t0M_mulVec, reflM_mulVec, b8_comm, b8_e0_left]

theorem t0M_fix {v : Coords 8} (hv : v 0 = 0) : t0M *ᵥ v = v := by
  rw [t0M_mulVec, hv, zero_smul, add_zero]

theorem t0M_e0 : t0M *ᵥ Pi.single 0 1 = -Pi.single 0 1 := by
  rw [t0M_mulVec, Pi.single_eq_same, one_smul, vec_neg_eq]

theorem t0M_mul_self : t0M * t0M = 1 := by
  rw [t0M_eq_reflM]
  exact reflM_mul_self (by rw [b8_e0_left, Pi.single_eq_same])

theorem tauM_mem : tauM ∈ hSeven := by
  refine ⟨1, fun i => if i = 0 then 1 else -1, by unfold IsSign; decide, ⟨rfl, rfl, rfl, by decide⟩, ?_⟩
  rw [spMat_one_eq_diagonal]
  rfl

theorem tauM_mul_self : tauM * tauM = 1 := by
  rw [tauM, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs <;> ring

theorem tauM_e0 : tauM *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
  rw [tauM_mulVec, Pi.single_eq_same, one_smul, vec_neg_eq]
  abel

theorem tauM_of_zero {v : Coords 8} (hv : v 0 = 0) : tauM *ᵥ v = -v := by
  rw [tauM_mulVec, hv, zero_smul, sub_zero]

theorem zero_of_tauM {v : Coords 8} (hv : tauM *ᵥ v = -v) : v 0 = 0 := by
  have e := congrFun hv 0
  rw [tauM_mulVec] at e
  simp only [Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
    mul_one] at e
  have k : ∀ x : ZMod 3, -x - x = -x → x = 0 := by decide
  exact k _ e

theorem fix_of_tauM {v : Coords 8} (hv : tauM *ᵥ v = v) : v = v 0 • Pi.single 0 1 := by
  funext i
  by_cases hi : i = 0
  · subst hi
    simp
  · have e := congrFun hv i
    rw [tauM_mulVec] at e
    simp only [Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, Pi.single_eq_of_ne hi, smul_eq_mul,
      mul_zero, sub_zero] at e
    have k : ∀ x : ZMod 3, -x = x → x = 0 := by decide
    rw [Pi.smul_apply, Pi.single_eq_of_ne hi, smul_zero]
    exact k _ e

theorem decomp_e0 (v : Coords 8) : v = v 0 • Pi.single 0 1 + (v - v 0 • Pi.single 0 1) := by
  abel

theorem decomp_e0_zero (v : Coords 8) : ((v - v 0 • Pi.single 0 1 : Coords 8)) 0 = 0 := by
  simp

theorem ext_e0 {A B : Matrix (Fin 8) (Fin 8) (ZMod 3)} (h0 : A *ᵥ Pi.single 0 1 = B *ᵥ Pi.single 0 1)
    (hU : ∀ w : Coords 8, w 0 = 0 → A *ᵥ w = B *ᵥ w) : A = B := by
  apply matrix_ext_mulVec
  intro v
  rw [decomp_e0 v, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, h0,
    hU _ (decomp_e0_zero v)]

theorem conj_tau_mulVec {τx g : GL (Fin 8) (ZMod 3)} (hτ : ↑ₘτx = tauM) (w : Coords 8) :
    ↑ₘ(g * τx * g⁻¹) *ᵥ w = -w - (↑ₘ(g⁻¹) *ᵥ w) 0 • (↑ₘg *ᵥ Pi.single 0 1) := by
  rw [mulVec_gmul, mulVec_gmul, hτ, tauM_mulVec, Matrix.mulVec_sub, Matrix.mulVec_neg,
    Matrix.mulVec_smul, mulVec_mulVec_inv]

theorem exists_conj_tau (h : CoreHyp X)
    (hodd : ∀ N : Subgroup ↥X, N.Normal → Odd (Nat.card N) → N = ⊥)
    (hmove : ∃ x ∈ X, ∃ i : Fin 8, i ≠ 0 ∧ (↑ₘx *ᵥ Pi.single 0 1) i ≠ 0) :
    ∃ τx ∈ X, ↑ₘτx = tauM ∧ ∃ g ∈ X, (g * τx * g⁻¹) * τx = τx * (g * τx * g⁻¹) ∧
      g * τx * g⁻¹ ≠ τx := by
  classical
  obtain ⟨τx, hτX, hτ⟩ := h.hH tauM tauM_mem
  refine ⟨τx, hτX, hτ, ?_⟩
  by_contra hiso'
  have hiso : ∀ g ∈ X, (g * τx * g⁻¹) * τx = τx * (g * τx * g⁻¹) → g * τx * g⁻¹ = τx := by
    intro g hg hc
    by_contra hne
    exact hiso' ⟨g, hg, hc, hne⟩
  let t : ↥X := ⟨τx, hτX⟩
  have : Fintype ↥X := Fintype.ofFinite _
  have ht1 : t ≠ 1 := by
    intro e
    have e' : ↑ₘτx = 1 := by
      have := congrArg (fun y : ↥X => ((y : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3))) e
      simpa [t] using this
    have := congrFun (congrFun e' 1) 1
    rw [hτ, tauM, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at this
    exact absurd this (by decide)
  have ht2 : t * t = 1 := by
    apply Subtype.ext
    apply Units.ext
    show ↑ₘτx * ↑ₘτx = 1
    rw [hτ, tauM_mul_self]
  obtain ⟨N, hN, hNo, hNt⟩ := CFSG.ZStar.glauberman_zStar ↥X t ht1 ht2 (fun g hg => by
    apply Subtype.ext
    exact hiso g g.2 (congrArg Subtype.val hg))
  have hN1 := hodd N hN hNo
  obtain ⟨x, hxX, i, hi, hxi⟩ := hmove
  have hc := hNt ⟨x, hxX⟩
  rw [hN1, Subgroup.mem_bot, mul_inv_eq_one] at hc
  have hc' : x * τx * x⁻¹ = τx := congrArg Subtype.val hc
  have hxc : x * τx = τx * x :=
    calc x * τx = (x * τx * x⁻¹) * x := by group
      _ = τx * x := by rw [hc']
  have hcm : ↑ₘx * tauM = tauM * ↑ₘx := by
    rw [← hτ, ← Units.val_mul, ← Units.val_mul, hxc]
  have hfix : tauM *ᵥ (↑ₘx *ᵥ Pi.single 0 1) = ↑ₘx *ᵥ Pi.single 0 1 := by
    rw [Matrix.mulVec_mulVec, ← hcm, ← Matrix.mulVec_mulVec, tauM_e0]
  have := congrFun (fix_of_tauM hfix) i
  rw [Pi.smul_apply, Pi.single_eq_of_ne hi, smul_zero] at this
  exact hxi this

theorem exists_t0 (h : CoreHyp X) {δ : ZMod 3} (hδ : δ = 1 ∨ δ = -1)
    (horb : ∀ v, v ∈ orb1 X ↔ IsRoot7 δ v)
    (hodd : ∀ N : Subgroup ↥X, N.Normal → Odd (Nat.card N) → N = ⊥)
    (hmove : ∃ x ∈ X, ∃ i : Fin 8, i ≠ 0 ∧ (↑ₘx *ᵥ Pi.single 0 1) i ≠ 0) :
    ∃ t ∈ X, ↑ₘt = t0M := by
  obtain ⟨τx, hτX, hτ, g, hgX, hcomm, hne⟩ := exists_conj_tau h hodd hmove
  have hτ2 : τx * τx = 1 := Units.ext (by rw [Units.val_mul, hτ, tauM_mul_self, Units.val_one])
  have hτ'X : g * τx * g⁻¹ ∈ X := X.mul_mem (X.mul_mem hgX hτX) (X.inv_mem hgX)
  have hT2 : g * τx * g⁻¹ * (g * τx * g⁻¹) = 1 := by
    rw [show g * τx * g⁻¹ * (g * τx * g⁻¹) = g * (τx * τx) * g⁻¹ by group, hτ2, mul_one,
      mul_inv_cancel]
  have hTw := conj_tau_mulVec (g := g) hτ
  have hTa : ↑ₘ(g * τx * g⁻¹) *ᵥ (↑ₘg *ᵥ Pi.single 0 1) = ↑ₘg *ᵥ Pi.single 0 1 := by
    rw [mulVec_gmul, mulVec_gmul, mulVec_inv_mulVec, hτ, tauM_e0]
  have hψa : (↑ₘ(g⁻¹) *ᵥ (↑ₘg *ᵥ Pi.single 0 1)) 0 = 1 := by
    rw [mulVec_inv_mulVec, Pi.single_eq_same]
  have ha0' : ↑ₘg *ᵥ (Pi.single 0 1 : Coords 8) ≠ 0 := by
    intro e
    have := mulVec_inv_mulVec g (Pi.single 0 1)
    rw [e, Matrix.mulVec_zero] at this
    have := congrFun this 0
    simp at this
  generalize ↑ₘg *ᵥ (Pi.single 0 1 : Coords 8) = a at hTw hTa hψa ha0'
  generalize g * τx * g⁻¹ = τ' at hτ'X hT2 hTw hTa hcomm hne
  have hTc : ↑ₘτ' * tauM = tauM * ↑ₘτ' := by
    rw [← hτ, ← Units.val_mul, ← Units.val_mul, hcomm]
  have hTU : ∀ w : Coords 8, w 0 = 0 → (↑ₘτ' *ᵥ w) 0 = 0 := by
    intro w hw
    apply zero_of_tauM
    rw [Matrix.mulVec_mulVec, ← hTc, ← Matrix.mulVec_mulVec, tauM_of_zero hw, Matrix.mulVec_neg]
  have hTe : ↑ₘτ' *ᵥ Pi.single 0 1 = (↑ₘτ' *ᵥ Pi.single 0 1) 0 • Pi.single 0 1 := by
    apply fix_of_tauM
    rw [Matrix.mulVec_mulVec, ← hTc, ← Matrix.mulVec_mulVec, tauM_e0]
  have hcc : (↑ₘτ' *ᵥ Pi.single 0 1) 0 * (↑ₘτ' *ᵥ Pi.single 0 1) 0 = 1 := by
    have e := congrFun (congrArg (fun A : Matrix (Fin 8) (Fin 8) (ZMod 3) => A *ᵥ Pi.single 0 1)
      (congrArg Units.val hT2)) 0
    simp only [Units.val_mul, Units.val_one, Matrix.one_mulVec, ← Matrix.mulVec_mulVec] at e
    rw [hTe, Matrix.mulVec_smul, hTe, smul_smul] at e
    simpa using e
  have e0 := congrFun (hTw (Pi.single 0 1)) 0
  simp only [Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul] at e0
  have hsq : ∀ c : ZMod 3, c * c = 1 → c = 1 ∨ c = -1 := by decide
  rcases hsq _ hcc with hc | hc
  ·
    exfalso
    apply hne
    have k1 : ∀ x y : ZMod 3, 1 = -1 - x * y → y ≠ 0 := by decide
    have ha00 : a 0 ≠ 0 := k1 _ _ (hc ▸ e0)
    apply Units.ext
    rw [hτ]
    apply ext_e0
    · rw [hTe, hc, one_smul, tauM_e0]
    · intro w hw
      have ew := congrFun (hTw w) 0
      simp only [Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, hw, hTU w hw] at ew
      have k2 : ∀ x y : ZMod 3, y ≠ 0 → 0 = -0 - x * y → x = 0 := by decide
      rw [hTw w, k2 _ _ ha00 ew, zero_smul, sub_zero, tauM_of_zero hw]
  have hTe0 : ↑ₘτ' *ᵥ Pi.single 0 1 = -Pi.single 0 1 := by
    rw [hTe, hc, neg_one_smul]
  have ha00 : a 0 = 0 := by
    have e := congrFun hTa 0
    rw [decomp_e0 a, Matrix.mulVec_add, Matrix.mulVec_smul, hTe0] at e
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.single_eq_same, smul_eq_mul,
      hTU _ (decomp_e0_zero a)] at e
    have k : ∀ x : ZMod 3, x * -1 + 0 = x + 0 → x = 0 := by
      decide
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, sub_self,
      add_zero] at e
    exact k _ (by rw [add_zero, add_zero]; exact e)
  have hnX : τ' * τx ∈ X := X.mul_mem hτ'X hτX
  have hNe0 : ↑ₘ(τ' * τx) *ᵥ Pi.single 0 1 = -Pi.single 0 1 := by
    rw [mulVec_gmul, hτ, tauM_e0, hTe0]
  have hNU : ∀ w : Coords 8, w 0 = 0 →
      ↑ₘ(τ' * τx) *ᵥ w = w + (↑ₘ(g⁻¹) *ᵥ w) 0 • a := by
    intro w hw
    rw [mulVec_gmul, hτ, tauM_of_zero hw, Matrix.mulVec_neg, hTw]
    abel
  have hNU0 : ∀ w : Coords 8, w 0 = 0 → (↑ₘ(τ' * τx) *ᵥ w) 0 = 0 := by
    intro w hw
    rw [hNU w hw]
    simp [hw, ha00]
  have hMe0 : (t0M * ↑ₘ(τ' * τx)) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
    rw [← Matrix.mulVec_mulVec, hNe0, Matrix.mulVec_neg, t0M_e0, neg_neg]
  have hMU : ∀ w : Coords 8, w 0 = 0 →
      (t0M * ↑ₘ(τ' * τx)) *ᵥ w = w + (↑ₘ(g⁻¹) *ᵥ w) 0 • a := by
    intro w hw
    rw [← Matrix.mulVec_mulVec, t0M_fix (hNU0 w hw), hNU w hw]
  have hMU0 : ∀ w : Coords 8, w 0 = 0 → ((t0M * ↑ₘ(τ' * τx)) *ᵥ w) 0 = 0 := by
    intro w hw
    rw [← Matrix.mulVec_mulVec, t0M_fix (hNU0 w hw)]
    exact hNU0 w hw
  have hMa : (t0M * ↑ₘ(τ' * τx)) *ᵥ a = -a := by
    rw [hMU a ha00, hψa, one_smul, vec_neg_eq]
  have hMax : IsAxis (t0M * ↑ₘ(τ' * τx)) a := by
    refine ⟨ha0', hMa, fun w => ⟨(↑ₘ(g⁻¹) *ᵥ (w - w 0 • Pi.single 0 1)) 0, ?_⟩⟩
    conv_lhs => rw [decomp_e0 w]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hMe0, hMU _ (decomp_e0_zero w)]
    abel
  have hR : ∀ r, IsRoot7 δ r → IsRoot7 δ ((t0M * ↑ₘ(τ' * τx)) *ᵥ r) := by
    intro r hr
    have hr0 : r 0 = 0 := hr.1
    rw [← Matrix.mulVec_mulVec, t0M_fix (hNU0 r hr0)]
    obtain ⟨m, hm, hmr⟩ := exists_reflM_mem h hδ horb hr
    have hm2 : m * m = 1 :=
      Units.ext (by rw [Units.val_mul, hmr, reflM_mul_self (root7_b8 hδ hr), Units.val_one])
    have hninv : ↑ₘ((τ' * τx)⁻¹) *ᵥ Pi.single 0 1 = -Pi.single 0 1 := by
      have := mulVec_inv_mulVec (τ' * τx) (Pi.single 0 1)
      rw [hNe0, Matrix.mulVec_neg] at this
      exact neg_eq_iff_eq_neg.mp this
    have hkX : τ' * τx * m * (τ' * τx)⁻¹ ∈ X ⊓ fixE0 7 := by
      refine ⟨X.mul_mem (X.mul_mem hnX hm.1) (X.inv_mem hnX), mem_fixE0.mpr ?_⟩
      rw [mulVec_gmul, mulVec_gmul, hninv, Matrix.mulVec_neg, hmr, reflM_mulVec, b8_e0_left, hr0,
        zero_smul, add_zero, Matrix.mulVec_neg, hNe0, neg_neg]
    have hk2 : τ' * τx * m * (τ' * τx)⁻¹ * (τ' * τx * m * (τ' * τx)⁻¹) = 1 := by
      rw [show τ' * τx * m * (τ' * τx)⁻¹ * (τ' * τx * m * (τ' * τx)⁻¹) =
        τ' * τx * (m * m) * (τ' * τx)⁻¹ by group, hm2, mul_one, mul_inv_cancel]
    refine axis_root_of_X1 h hδ horb hkX hk2 ⟨fun e => root7_ne_zero hδ hr ?_, ?_, fun w => ?_⟩
    · have := mulVec_inv_mulVec (τ' * τx) r
      rw [e, Matrix.mulVec_zero] at this
      exact this.symm
    · rw [mulVec_gmul, mulVec_gmul, mulVec_inv_mulVec, hmr, reflM_mulVec_self (root7_b8 hδ hr),
        Matrix.mulVec_neg]
    · refine ⟨b8 (↑ₘ((τ' * τx)⁻¹) *ᵥ w) r, ?_⟩
      rw [mulVec_gmul, mulVec_gmul, hmr, reflM_mulVec, Matrix.mulVec_add, mulVec_mulVec_inv,
        Matrix.mulVec_smul]
      abel
  have hiso := b8_mulVec_of_gram (gram_of_roots7 hδ hMe0 hMU0 hR)
  obtain ⟨hq, hMs⟩ := sref_of_axis hiso hMax
  have ha : IsRoot7 δ a := root_of_presRoots h hδ horb ha00 hq (fun r hr => by
    rw [← hMs]
    exact hR r hr)
  have hMr : t0M * ↑ₘ(τ' * τx) = reflM a :=
    matrix_ext_mulVec fun w => by rw [hMs, sref_eq_reflM (root7_b8 hδ ha)]
  obtain ⟨m', hm', hm'a⟩ := exists_reflM_mem h hδ horb ha
  refine ⟨m' * (τ' * τx)⁻¹, X.mul_mem hm'.1 (X.inv_mem hnX), ?_⟩
  rw [Units.val_mul, hm'a, ← hMr, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.mul_one]

end CFSG.StandardType.FrameRoute.FS81.E7Row

end
