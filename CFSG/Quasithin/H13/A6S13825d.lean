module

public import CFSG.Quasithin.H13.A6S13825c

public section

namespace CFSG.Quasithin.H13.A6.L4Ind

open Matrix

@[expose] def repList : List (M4 × M4) :=
  [(!![1,0,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,1],
    !![1,0,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,1]),
   (!![1,0,0,0; 0,0,1,0; 0,1,0,0; 0,0,0,1],
    !![1,0,0,0; 0,0,1,0; 0,1,0,0; 0,0,0,1]),
   (!![1,0,0,0; 0,1,1,0; 0,1,0,0; 0,0,0,1],
    !![1,0,0,0; 0,0,1,0; 0,1,1,0; 0,0,0,1]),
   (!![1,0,0,0; 0,0,1,0; 0,0,0,1; 0,1,0,0],
    !![1,0,0,0; 0,0,0,1; 0,1,0,0; 0,0,1,0]),
   (!![1,0,0,0; 0,1,1,0; 0,0,0,1; 0,1,0,0],
    !![1,0,0,0; 0,0,0,1; 0,1,0,1; 0,0,1,0]),
   (!![1,0,0,0; 0,0,1,0; 0,1,0,1; 0,1,0,0],
    !![1,0,0,0; 0,0,0,1; 0,1,0,0; 0,0,1,1]),
   (!![1,0,0,0; 0,1,1,0; 0,1,0,1; 0,1,0,0],
    !![1,0,0,0; 0,0,0,1; 0,1,0,1; 0,0,1,1]),
   (!![0,0,1,0; 1,0,0,0; 0,1,0,0; 0,0,0,1],
    !![0,1,0,0; 0,0,1,0; 1,0,0,0; 0,0,0,1]),
   (!![0,1,1,0; 1,0,0,0; 0,1,0,0; 0,0,0,1],
    !![0,1,0,0; 0,0,1,0; 1,0,1,0; 0,0,0,1]),
   (!![0,0,1,0; 1,0,0,0; 0,0,0,1; 0,1,0,0],
    !![0,1,0,0; 0,0,0,1; 1,0,0,0; 0,0,1,0]),
   (!![0,1,1,0; 1,0,0,0; 0,0,0,1; 0,1,0,0],
    !![0,1,0,0; 0,0,0,1; 1,0,0,1; 0,0,1,0]),
   (!![0,0,1,0; 1,0,0,0; 0,1,0,1; 0,1,0,0],
    !![0,1,0,0; 0,0,0,1; 1,0,0,0; 0,0,1,1]),
   (!![0,1,1,0; 1,0,0,0; 0,1,0,1; 0,1,0,0],
    !![0,1,0,0; 0,0,0,1; 1,0,0,1; 0,0,1,1]),
   (!![1,0,1,0; 1,0,0,0; 0,1,0,0; 0,0,0,1],
    !![0,1,0,0; 0,0,1,0; 1,1,0,0; 0,0,0,1]),
   (!![1,1,1,0; 1,0,0,0; 0,1,0,0; 0,0,0,1],
    !![0,1,0,0; 0,0,1,0; 1,1,1,0; 0,0,0,1]),
   (!![1,0,1,0; 1,0,0,0; 0,0,0,1; 0,1,0,0],
    !![0,1,0,0; 0,0,0,1; 1,1,0,0; 0,0,1,0]),
   (!![1,1,1,0; 1,0,0,0; 0,0,0,1; 0,1,0,0],
    !![0,1,0,0; 0,0,0,1; 1,1,0,1; 0,0,1,0]),
   (!![1,0,1,0; 1,0,0,0; 0,1,0,1; 0,1,0,0],
    !![0,1,0,0; 0,0,0,1; 1,1,0,0; 0,0,1,1]),
   (!![1,1,1,0; 1,0,0,0; 0,1,0,1; 0,1,0,0],
    !![0,1,0,0; 0,0,0,1; 1,1,0,1; 0,0,1,1]),
   (!![0,0,1,0; 0,0,0,1; 1,0,0,0; 0,1,0,0],
    !![0,0,1,0; 0,0,0,1; 1,0,0,0; 0,1,0,0]),
   (!![0,1,1,0; 0,0,0,1; 1,0,0,0; 0,1,0,0],
    !![0,0,1,0; 0,0,0,1; 1,0,0,1; 0,1,0,0]),
   (!![0,0,1,0; 0,1,0,1; 1,0,0,0; 0,1,0,0],
    !![0,0,1,0; 0,0,0,1; 1,0,0,0; 0,1,0,1]),
   (!![0,1,1,0; 0,1,0,1; 1,0,0,0; 0,1,0,0],
    !![0,0,1,0; 0,0,0,1; 1,0,0,1; 0,1,0,1]),
   (!![1,0,1,0; 0,0,0,1; 1,0,0,0; 0,1,0,0],
    !![0,0,1,0; 0,0,0,1; 1,0,1,0; 0,1,0,0]),
   (!![1,1,1,0; 0,0,0,1; 1,0,0,0; 0,1,0,0],
    !![0,0,1,0; 0,0,0,1; 1,0,1,1; 0,1,0,0]),
   (!![1,0,1,0; 0,1,0,1; 1,0,0,0; 0,1,0,0],
    !![0,0,1,0; 0,0,0,1; 1,0,1,0; 0,1,0,1]),
   (!![1,1,1,0; 0,1,0,1; 1,0,0,0; 0,1,0,0],
    !![0,0,1,0; 0,0,0,1; 1,0,1,1; 0,1,0,1]),
   (!![0,0,1,0; 1,0,0,1; 1,0,0,0; 0,1,0,0],
    !![0,0,1,0; 0,0,0,1; 1,0,0,0; 0,1,1,0]),
   (!![0,1,1,0; 1,0,0,1; 1,0,0,0; 0,1,0,0],
    !![0,0,1,0; 0,0,0,1; 1,0,0,1; 0,1,1,0]),
   (!![0,0,1,0; 1,1,0,1; 1,0,0,0; 0,1,0,0],
    !![0,0,1,0; 0,0,0,1; 1,0,0,0; 0,1,1,1]),
   (!![0,1,1,0; 1,1,0,1; 1,0,0,0; 0,1,0,0],
    !![0,0,1,0; 0,0,0,1; 1,0,0,1; 0,1,1,1]),
   (!![1,0,1,0; 1,0,0,1; 1,0,0,0; 0,1,0,0],
    !![0,0,1,0; 0,0,0,1; 1,0,1,0; 0,1,1,0]),
   (!![1,1,1,0; 1,0,0,1; 1,0,0,0; 0,1,0,0],
    !![0,0,1,0; 0,0,0,1; 1,0,1,1; 0,1,1,0]),
   (!![1,0,1,0; 1,1,0,1; 1,0,0,0; 0,1,0,0],
    !![0,0,1,0; 0,0,0,1; 1,0,1,0; 0,1,1,1]),
   (!![1,0,1,0; 1,0,0,1; 1,1,0,0; 0,1,0,0],
    !![0,0,1,1; 0,0,0,1; 1,0,1,1; 0,1,1,1])]

@[expose] def repM (i : Fin 35) : M4 := (repList.getD i (1, 1)).1

@[expose] def repInvM (i : Fin 35) : M4 := (repList.getD i (1, 1)).2

theorem rep_mul_inv : ∀ i : Fin 35, repM i * repInvM i = 1 := by
  decide

@[expose] def rep (i : Fin 35) : SL4 := mkSL (repM i) (repInvM i) (rep_mul_inv i)

abbrev allV4 : List V4 := allV2.flatMap fun p => allV2.map fun q => ![p 0, p 1, q 0, q 1]

theorem mem_allV4 : ∀ v : V4, v ∈ allV4 := by
  decide

@[expose] def idxAB (a b : V4) : Fin 35 :=
  ((List.finRange 35).find? fun i =>
    decide (InL0 (repInvM i *ᵥ a) ∧ InL0 (repInvM i *ᵥ b))).getD 0

@[expose] def idxOkB : Bool := allV4.all fun a => allV4.all fun b =>
  a == 0 || b == 0 || a == b ||
    decide (InL0 (repInvM (idxAB a b) *ᵥ a) ∧ InL0 (repInvM (idxAB a b) *ᵥ b))

theorem idxOk : idxOkB = true := by
  decide

theorem idxAB_spec {a b : V4} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    InL0 (repInvM (idxAB a b) *ᵥ a) ∧ InL0 (repInvM (idxAB a b) *ᵥ b) := by
  have h := idxOk
  simp only [idxOkB, List.all_eq_true] at h
  have := h a (mem_allV4 a) b (mem_allV4 b)
  simpa [ha, hb, hab] using this

@[expose] def idx (g : M4) : Fin 35 := idxAB (g *ᵥ e0) (g *ᵥ e1)

theorem mulVec_ne_zero (g : SL4) {v : V4} (hv : v ≠ 0) : (g : M4) *ᵥ v ≠ 0 := by
  intro h
  apply hv
  rw [← inv_mulVec_mulVec g v, h, mulVec_zero]

theorem idx_spec (g : SL4) : InQ2 (repInvM (idx (g : M4)) * (g : M4)) := by
  have h0 : (g : M4) *ᵥ e0 ≠ 0 := mulVec_ne_zero g (by decide)
  have h1 : (g : M4) *ᵥ e1 ≠ 0 := mulVec_ne_zero g (by decide)
  have h01 : (g : M4) *ᵥ e0 ≠ (g : M4) *ᵥ e1 := by
    intro h
    have h' := congrArg (fun v => ((g⁻¹ : SL4) : M4) *ᵥ v) h
    simp only [inv_mulVec_mulVec] at h'
    exact absurd h' (by decide)
  obtain ⟨ha, hb⟩ := idxAB_spec h0 h1 h01
  rw [inQ2_iff, ← mulVec_mulVec, ← mulVec_mulVec]
  exact ⟨ha, hb⟩

@[expose] def nf (g : M4) (z : V4) : Fin 35 → V4 :=
  fun j => if j = idx g then (repInvM (idx g) * g) *ᵥ z else 0

variable {M : Type*} [CommGroup M]

@[expose] def eval (φ : SL4 →* MulAut M) (m₀ m₁ : M) (c : Fin 35 → V4) : M :=
  ∏ j, φ (rep j) (mvec m₀ m₁ (c j))

theorem eval_add (hM : ∀ x : M, x * x = 1) (φ : SL4 →* MulAut M) (m₀ m₁ : M)
    (c c' : Fin 35 → V4) : eval φ m₀ m₁ (c + c') = eval φ m₀ m₁ c * eval φ m₀ m₁ c' := by
  simp only [eval, Pi.add_apply, mvec_add hM, map_mul, Finset.prod_mul_distrib]

theorem eval_zero (φ : SL4 →* MulAut M) (m₀ m₁ : M) : eval φ m₀ m₁ 0 = 1 := by
  simp [eval, mvec_zero]

variable {φ : SL4 →* MulAut M} {m₀ m₁ : M}

theorem eval_nf (hG : Gen φ m₀ m₁) (g : SL4) {z : V4} (hz : InL0 z) :
    φ g (mvec m₀ m₁ z) = eval φ m₀ m₁ (nf (g : M4) z) := by
  set i := idx (g : M4) with hi
  set p : SL4 := (rep i)⁻¹ * g with hpdef
  have hpM : (p : M4) = repInvM i * (g : M4) := by
    rw [hpdef, Matrix.SpecialLinearGroup.coe_mul, rep, coe_mkSL_inv]
  have hpQ : InQ2 (p : M4) := by
    rw [hpM]
    exact idx_spec g
  have h1 : eval φ m₀ m₁ (nf (g : M4) z) =
      φ (rep i) (mvec m₀ m₁ ((repInvM i * (g : M4)) *ᵥ z)) := by
    unfold eval
    rw [Finset.prod_eq_single i]
    · simp only [nf, ← hi, ite_true]
    · intro j _ hj
      simp only [nf, ← hi, hj, ite_false, mvec_zero, map_one]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [h1, ← hpM, ← hG.hP p hpQ z hz, ← MulAut.mul_apply, ← map_mul, hpdef,
    mul_inv_cancel_left]

theorem phi_m0 (hG : Gen φ m₀ m₁) (g : SL4) : φ g m₀ = eval φ m₀ m₁ (nf (g : M4) e0) := by
  rw [← eval_nf hG g (by decide), mvec_e0]

theorem quad_eval (hG : Gen φ m₀ m₁) {x y : SL4}
    (hq : ∀ v : M, φ x (φ y v * v⁻¹) = φ y v * v⁻¹) (k : SL4) {z : V4} (hz : InL0 z) :
    eval φ m₀ m₁ (nf ((x * y * k : SL4) : M4) z + nf ((x * k : SL4) : M4) z +
      nf ((y * k : SL4) : M4) z + nf (k : M4) z) = 1 := by
  rw [eval_add hG.sq, eval_add hG.sq, eval_add hG.sq, ← eval_nf hG _ hz, ← eval_nf hG _ hz,
    ← eval_nf hG _ hz, ← eval_nf hG _ hz]
  set v := φ k (mvec m₀ m₁ z) with hv
  have e1 : φ (x * y * k) (mvec m₀ m₁ z) = φ x (φ y v) := by
    rw [hv, map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply]
  have e2 : φ (x * k) (mvec m₀ m₁ z) = φ x v := by
    rw [hv, map_mul, MulAut.mul_apply]
  have e3 : φ (y * k) (mvec m₀ m₁ z) = φ y v := by
    rw [hv, map_mul, MulAut.mul_apply]
  rw [e1, e2, e3]
  have hinv : ∀ a : M, a⁻¹ = a := fun a => inv_eq_of_mul_eq_one_right (hG.sq a)
  have h := hq v
  rw [map_mul, map_inv, hinv, hinv] at h
  calc φ x (φ y v) * φ x v * φ y v * v = (φ x (φ y v) * φ x v) * (φ y v * v) := by group
    _ = (φ y v * v) * (φ y v * v) := by rw [h]
    _ = 1 := hG.sq _

abbrev gy3M : M4 := !![0, 0, 1, 0; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1]
abbrev gy3I : M4 := !![0, 1, 0, 0; 0, 0, 1, 0; 1, 0, 0, 0; 0, 0, 0, 1]

abbrev gy4M : M4 := !![0, 0, 1, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0]
abbrev gy4I : M4 := !![0, 1, 0, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 1, 0]

abbrev gy3pM : M4 := !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]
abbrev gy3pI : M4 := !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

abbrev gy5aM : M4 := !![0, 1, 0, 0; 0, 0, 1, 0; 1, 0, 0, 0; 0, 0, 0, 1]
abbrev gy5aI : M4 := !![0, 0, 1, 0; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1]

abbrev gu3M : M4 := !![0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0]
abbrev gu3I : M4 := !![0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0]

abbrev kAM : M4 := !![0, 0, 1, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 1, 0]
abbrev kAI : M4 := !![0, 1, 0, 0; 1, 0, 0, 1; 1, 0, 0, 0; 0, 0, 1, 0]

abbrev kBM : M4 := !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 1, 0]
abbrev kBI : M4 := !![0, 0, 1, 0; 1, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

abbrev kCM : M4 := !![1, 0, 0, 0; 0, 1, 0, 1; 0, 0, 1, 0; 0, 1, 1, 0]
abbrev kCI : M4 := !![1, 0, 0, 0; 0, 0, 1, 1; 0, 0, 1, 0; 0, 1, 1, 1]

abbrev kDM : M4 := !![0, 0, 1, 0; 1, 0, 0, 0; 0, 1, 1, 0; 0, 0, 0, 1]
abbrev kDI : M4 := !![0, 1, 0, 0; 1, 0, 1, 0; 1, 0, 0, 0; 0, 0, 0, 1]

abbrev hR1M : M4 := !![1, 0, 1, 0; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1]
abbrev hR1I : M4 := !![0, 1, 0, 0; 0, 0, 1, 0; 1, 1, 0, 0; 0, 0, 0, 1]

abbrev hR2M : M4 := !![1, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1]
abbrev hR2I : M4 := !![0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 1, 0; 0, 0, 0, 1]

abbrev kRM : M4 := !![1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; 0, 1, 0, 0]
abbrev kRI : M4 := !![1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0]

abbrev d2M : M4 := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]
abbrev d2I : M4 := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]

abbrev d23M : M4 := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 1]
abbrev d23I : M4 := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 1; 0, 0, 1, 0]


abbrev a2M : M4 := !![1, 0, 1, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

abbrev a3M : M4 := !![1, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def a2 : SL4 := mkSL a2M a2M (by decide)

@[expose] def a3 : SL4 := mkSL a3M a3M (by decide)

@[expose] def gy3 : SL4 := mkSL gy3M gy3I (by decide)

@[expose] def gy4 : SL4 := mkSL gy4M gy4I (by decide)

@[expose] def gy3p : SL4 := mkSL gy3pM gy3pI (by decide)

@[expose] def gy5a : SL4 := mkSL gy5aM gy5aI (by decide)

@[expose] def gu3 : SL4 := mkSL gu3M gu3I (by decide)

@[expose] def kA : SL4 := mkSL kAM kAI (by decide)

@[expose] def kB : SL4 := mkSL kBM kBI (by decide)

@[expose] def kC : SL4 := mkSL kCM kCI (by decide)

@[expose] def kD : SL4 := mkSL kDM kDI (by decide)

@[expose] def hR1 : SL4 := mkSL hR1M hR1I (by decide)

@[expose] def hR2 : SL4 := mkSL hR2M hR2I (by decide)

@[expose] def kR : SL4 := mkSL kRM kRI (by decide)

@[expose] def d2 : SL4 := mkSL d2M d2I (by decide)

@[expose] def d23 : SL4 := mkSL d23M d23I (by decide)

@[expose] def Quad23 (φ : SL4 →* MulAut M) : Prop :=
  ∀ h : SL4, ∀ v : M, φ (h * a2 * h⁻¹) (φ (h * a3 * h⁻¹) v * v⁻¹) = φ (h * a3 * h⁻¹) v * v⁻¹

abbrev x1M : M4 := !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

abbrev y1M : M4 := !![1, 0, 0, 1; 0, 1, 0, 1; 0, 0, 1, 0; 0, 0, 0, 1]

abbrev x2M : M4 := !![0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1]

abbrev y2M : M4 := !![1, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 1; 0, 0, 0, 1]

@[expose] def x1 : SL4 := mkSL x1M x1M (by decide)

@[expose] def y1 : SL4 := mkSL y1M y1M (by decide)

@[expose] def x2 : SL4 := mkSL x2M x2M (by decide)

@[expose] def y2 : SL4 := mkSL y2M y2M (by decide)

theorem conj_hR1_a2 : hR1 * a2 * hR1⁻¹ = x1 := by
  rw [hR1, conj_mkSL]
  exact Subtype.ext (by decide)

theorem conj_hR1_a3 : hR1 * a3 * hR1⁻¹ = y1 := by
  rw [hR1, conj_mkSL]
  exact Subtype.ext (by decide)

theorem conj_hR2_a2 : hR2 * a2 * hR2⁻¹ = x2 := by
  rw [hR2, conj_mkSL]
  exact Subtype.ext (by decide)

theorem conj_hR2_a3 : hR2 * a3 * hR2⁻¹ = y2 := by
  rw [hR2, conj_mkSL]
  exact Subtype.ext (by decide)

theorem rel12 (hG : Gen φ m₀ m₁) (hq : Quad23 φ) :
    eval φ m₀ m₁ (nf ((x1 * y1 * kR : SL4) : M4) e0 + nf ((x1 * kR : SL4) : M4) e0 +
      nf ((y1 * kR : SL4) : M4) e0 + nf (kR : M4) e0) = 1 ∧
    eval φ m₀ m₁ (nf ((x2 * y2 * kR : SL4) : M4) e0 + nf ((x2 * kR : SL4) : M4) e0 +
      nf ((y2 * kR : SL4) : M4) e0 + nf (kR : M4) e0) = 1 := by
  have r1 := quad_eval hG (hq hR1) kR (z := e0) (by decide)
  have r2 := quad_eval hG (hq hR2) kR (z := e0) (by decide)
  rw [conj_hR1_a2, conj_hR1_a3] at r1
  rw [conj_hR2_a2, conj_hR2_a3] at r2
  exact ⟨r1, r2⟩

theorem eval_eq_one_of_zero (φ : SL4 →* MulAut M) (m₀ m₁ : M) {X : Fin 35 → V4} (hX : X = 0) :
    eval φ m₀ m₁ X = 1 := by
  rw [hX, eval_zero]

theorem eval_eq_one_of_two (hG : Gen φ m₀ m₁) {X R₁ R₂ : Fin 35 → V4} (hX : X = R₁ + R₂)
    (h₁ : eval φ m₀ m₁ R₁ = 1) (h₂ : eval φ m₀ m₁ R₂ = 1) : eval φ m₀ m₁ X = 1 := by
  rw [hX, eval_add hG.sq, h₁, h₂, one_mul]

theorem certA (hG : Gen φ m₀ m₁) :
    φ (a3 * gy4) m₀ * φ gy4 m₀ * (φ kA m₀ * φ (kA * g0) m₀) = 1 := by
  simp only [phi_m0 hG, ← eval_add hG.sq]
  exact eval_eq_one_of_zero φ m₀ m₁ (by decide)

theorem certB (hG : Gen φ m₀ m₁) :
    φ (a3 * gy3p) m₀ * φ gy3p m₀ * (φ kB m₀ * φ (kB * g0) m₀) = 1 := by
  simp only [phi_m0 hG, ← eval_add hG.sq]
  exact eval_eq_one_of_zero φ m₀ m₁ (by decide)

theorem certC (hG : Gen φ m₀ m₁) (hq : Quad23 φ) :
    φ (a3 * gy4) m₀ * φ (a3 * gy3p) m₀ * (φ gy4 m₀ * φ gy3p m₀) *
      (φ kC m₀ * φ (kC * g0) m₀) = 1 := by
  obtain ⟨r1, r2⟩ := rel12 hG hq
  simp only [phi_m0 hG, ← eval_add hG.sq]
  exact eval_eq_one_of_two hG (by decide) r1 r2

theorem certD (hG : Gen φ m₀ m₁) :
    φ (a2 * gy3) m₀ * φ gy3 m₀ * (φ kD m₀ * φ (kD * g0) m₀) = 1 := by
  simp only [phi_m0 hG, ← eval_add hG.sq]
  exact eval_eq_one_of_zero φ m₀ m₁ (by decide)


theorem phi_phi (a g : SL4) (x : M) : φ a (φ g x) = φ (a * g) x := by
  rw [map_mul, MulAut.mul_apply]

theorem translate_ne (hG : Gen φ m₀ m₁) (hne : φ g0 m₀ ≠ m₀) (k : SL4) :
    φ k m₀ * φ (k * g0) m₀ ≠ 1 := by
  intro h
  rw [← phi_phi, ← map_mul] at h
  have h' : m₀ * φ g0 m₀ = 1 := by
    have := congrArg (φ k⁻¹) h
    rwa [phi_phi, inv_mul_cancel, map_one, MulAut.one_apply, map_one] at this
  apply hne
  have hinv : m₀⁻¹ = m₀ := inv_eq_of_mul_eq_one_right (hG.sq m₀)
  exact (eq_inv_of_mul_eq_one_right h').trans hinv

theorem moves_of_cert (hG : Gen φ m₀ m₁) (hne : φ g0 m₀ ≠ m₀) {a k : SL4} {X : M}
    (h : φ a X * X * (φ k m₀ * φ (k * g0) m₀) = 1) : φ a X ≠ X := by
  intro hX
  rw [hX, hG.sq, one_mul] at h
  exact translate_ne hG hne k h

theorem moves_y4 (hG : Gen φ m₀ m₁) (hne : φ g0 m₀ ≠ m₀) : φ a3 (φ gy4 m₀) ≠ φ gy4 m₀ := by
  refine moves_of_cert hG hne (k := kA) ?_
  rw [phi_phi]
  exact certA hG

theorem moves_y3p (hG : Gen φ m₀ m₁) (hne : φ g0 m₀ ≠ m₀) : φ a3 (φ gy3p m₀) ≠ φ gy3p m₀ := by
  refine moves_of_cert hG hne (k := kB) ?_
  rw [phi_phi]
  exact certB hG

theorem moves_y4y3p (hG : Gen φ m₀ m₁) (hq : Quad23 φ) (hne : φ g0 m₀ ≠ m₀) :
    φ a3 (φ gy4 m₀ * φ gy3p m₀) ≠ φ gy4 m₀ * φ gy3p m₀ := by
  refine moves_of_cert hG hne (k := kC) ?_
  rw [map_mul, phi_phi, phi_phi]
  exact certC hG hq

theorem moves_y3 (hG : Gen φ m₀ m₁) (hne : φ g0 m₀ ≠ m₀) : φ a2 (φ gy3 m₀) ≠ φ gy3 m₀ := by
  refine moves_of_cert hG hne (k := kD) ?_
  rw [phi_phi]
  exact certD hG

theorem moves_y5 (hG : Gen φ m₀ m₁) (hne : φ g0 m₀ ≠ m₀) :
    φ a3 (φ gy5a m₀ * φ gy3p m₀) ≠ φ gy5a m₀ * φ gy3p m₀ := by
  refine moves_of_cert hG hne (k := kB) ?_
  rw [map_mul, phi_phi, phi_phi]
  simp only [phi_m0 hG, ← eval_add hG.sq]
  exact eval_eq_one_of_zero φ m₀ m₁ (by decide)

theorem moves_y3y4 (hG : Gen φ m₀ m₁) (hne : φ g0 m₀ ≠ m₀) :
    φ a2 (φ gy3 m₀ * φ gy4 m₀) ≠ φ gy3 m₀ * φ gy4 m₀ := by
  refine moves_of_cert hG hne (k := kD) ?_
  rw [map_mul, phi_phi, phi_phi]
  simp only [phi_m0 hG, ← eval_add hG.sq]
  exact eval_eq_one_of_zero φ m₀ m₁ (by decide)

theorem moves_y3y5 (hG : Gen φ m₀ m₁) (hne : φ g0 m₀ ≠ m₀) :
    φ a3 (φ gy3 m₀ * (φ gy5a m₀ * φ gy3p m₀)) ≠ φ gy3 m₀ * (φ gy5a m₀ * φ gy3p m₀) := by
  refine moves_of_cert hG hne (k := kB) ?_
  rw [map_mul, map_mul, phi_phi, phi_phi, phi_phi]
  simp only [phi_m0 hG, ← eval_add hG.sq]
  exact eval_eq_one_of_zero φ m₀ m₁ (by decide)

theorem moves_y4y5 (hG : Gen φ m₀ m₁) (hq : Quad23 φ) (hne : φ g0 m₀ ≠ m₀) :
    φ a3 (φ gy4 m₀ * (φ gy5a m₀ * φ gy3p m₀)) ≠ φ gy4 m₀ * (φ gy5a m₀ * φ gy3p m₀) := by
  obtain ⟨r1, r2⟩ := rel12 hG hq
  refine moves_of_cert hG hne (k := kC) ?_
  rw [map_mul, map_mul, phi_phi, phi_phi, phi_phi]
  simp only [phi_m0 hG, ← eval_add hG.sq]
  exact eval_eq_one_of_two hG (by decide) r1 r2

theorem moves_y3y4y5 (hG : Gen φ m₀ m₁) (hq : Quad23 φ) (hne : φ g0 m₀ ≠ m₀) :
    φ a3 (φ gy3 m₀ * φ gy4 m₀ * (φ gy5a m₀ * φ gy3p m₀)) ≠
      φ gy3 m₀ * φ gy4 m₀ * (φ gy5a m₀ * φ gy3p m₀) := by
  obtain ⟨r1, r2⟩ := rel12 hG hq
  refine moves_of_cert hG hne (k := kC) ?_
  rw [map_mul, map_mul, map_mul, phi_phi, phi_phi, phi_phi, phi_phi]
  simp only [phi_m0 hG, ← eval_add hG.sq]
  exact eval_eq_one_of_two hG (by decide) r1 r2


@[expose] def powL {n : ℕ} (x : Fin n → M) (l : Fin n → ZMod 2) : M :=
  ∏ i, if l i = 1 then x i else 1

theorem powL_add (hM : ∀ x : M, x * x = 1) {n : ℕ} (x : Fin n → M) (l l' : Fin n → ZMod 2) :
    powL x (l + l') = powL x l * powL x l' := by
  simp only [powL, Pi.add_apply, ite_add_one hM, Finset.prod_mul_distrib]

theorem zmod2_eq_of_add : ∀ a b : ZMod 2, a + b = 0 → a = b := by
  decide

theorem index_ge [Finite M] (hM : ∀ x : M, x * x = 1) {C : Subgroup M} {n : ℕ} (x : Fin n → M)
    (hx : ∀ l : Fin n → ZMod 2, l ≠ 0 → powL x l ∉ C) : 2 ^ n ≤ C.index := by
  classical
  have hinj : Function.Injective fun l : Fin n → ZMod 2 =>
      (QuotientGroup.mk (powL x l) : M ⧸ C) := by
    intro l l' h
    have h' : (powL x l)⁻¹ * powL x l' ∈ C := QuotientGroup.eq.mp h
    rw [inv_eq_of_mul_eq_one_right (hM _), ← powL_add hM] at h'
    by_contra hne
    refine hx (l + l') (fun h0 => hne ?_) h'
    funext i
    exact zmod2_eq_of_add _ _ (congrFun h0 i)
  have h1 := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_fintype_card (α := Fin n → ZMod 2), Fintype.card_fun, ZMod.card,
    Fintype.card_fin] at h1
  exact h1

@[expose] def fixSub (φ : SL4 →* MulAut M) (T : Set SL4) : Subgroup M where
  carrier := {v | ∀ a ∈ T, φ a v = v}
  mul_mem' {x y} hx hy a ha := by rw [map_mul, hx a ha, hy a ha]
  one_mem' a _ := map_one _
  inv_mem' {x} hx a ha := by rw [map_inv, hx a ha]

theorem mem_fixSub {T : Set SL4} {v : M} : v ∈ fixSub φ T ↔ ∀ a ∈ T, φ a v = v := Iff.rfl

theorem moves_of_beta (β : M →* Multiplicative V4)
    (hβ : ∀ g v, Multiplicative.toAdd (β (φ g v)) = (g : M4) *ᵥ Multiplicative.toAdd (β v))
    {a : SL4} {X : M}
    (h : (a : M4) *ᵥ Multiplicative.toAdd (β X) ≠ Multiplicative.toAdd (β X)) : φ a X ≠ X := by
  intro hX
  apply h
  rw [← hβ, hX]

theorem a2_moves : ∀ w : V4, w 2 = 1 → a2M *ᵥ w ≠ w := by
  decide

theorem a3_moves : ∀ w : V4, w 3 = 1 → a3M *ᵥ w ≠ w := by
  decide

theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by
  decide

theorem index_a3 [Finite M] (hG : Gen φ m₀ m₁) (hq : Quad23 φ) (β : M →* Multiplicative V4)
    (hβ : ∀ g v, Multiplicative.toAdd (β (φ g v)) = (g : M4) *ᵥ Multiplicative.toAdd (β v))
    (hβ0 : Multiplicative.toAdd (β m₀) = e0) (hne : φ g0 m₀ ≠ m₀) :
    8 ≤ (fixSub φ {a3}).index := by
  have hb : ∀ g : SL4, Multiplicative.toAdd (β (φ g m₀)) = (g : M4) *ᵥ e0 := fun g => by
    rw [hβ, hβ0]
  refine index_ge hG.sq (n := 3) ![φ gu3 m₀, φ gy4 m₀, φ gy3p m₀] fun l hl hmem => ?_
  have hfix := (mem_fixSub.1 hmem) a3 rfl
  obtain ⟨c₀, c₁, c₂, rfl⟩ : ∃ c₀ c₁ c₂ : ZMod 2, l = ![c₀, c₁, c₂] :=
    ⟨l 0, l 1, l 2, by ext i; fin_cases i <;> rfl⟩
  rcases zmod2_cases c₀ with rfl | rfl <;> rcases zmod2_cases c₁ with rfl | rfl <;>
    rcases zmod2_cases c₂ with rfl | rfl <;>
    simp only [powL, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, ite_true, ite_false, one_mul,
      mul_one, show (0 : ZMod 2) ≠ 1 by decide] at hfix hl
  · exact hl (by decide)
  · exact moves_y3p hG hne hfix
  · exact moves_y4 hG hne hfix
  · exact moves_y4y3p hG hq hne hfix
  all_goals
    refine moves_of_beta β hβ ?_ hfix
    simp only [map_mul, toAdd_mul, hb]
    exact a3_moves _ (by decide)

theorem index_E [Finite M] (hG : Gen φ m₀ m₁) (hq : Quad23 φ) (β : M →* Multiplicative V4)
    (hβ : ∀ g v, Multiplicative.toAdd (β (φ g v)) = (g : M4) *ᵥ Multiplicative.toAdd (β v))
    (hβ0 : Multiplicative.toAdd (β m₀) = e0) (hne : φ g0 m₀ ≠ m₀) :
    32 ≤ (fixSub φ {a2, a3}).index := by
  have hb : ∀ g : SL4, Multiplicative.toAdd (β (φ g m₀)) = (g : M4) *ᵥ e0 := fun g => by
    rw [hβ, hβ0]
  refine index_ge hG.sq (n := 5)
    ![φ gy3p m₀, φ gu3 m₀, φ gy3 m₀, φ gy4 m₀, φ gy5a m₀ * φ gy3p m₀] fun l hl hmem => ?_
  have hfix2 := (mem_fixSub.1 hmem) a2 (by simp)
  have hfix3 := (mem_fixSub.1 hmem) a3 (by simp)
  obtain ⟨c₀, c₁, c₂, c₃, c₄, rfl⟩ : ∃ c₀ c₁ c₂ c₃ c₄ : ZMod 2, l = ![c₀, c₁, c₂, c₃, c₄] :=
    ⟨l 0, l 1, l 2, l 3, l 4, by ext i; fin_cases i <;> rfl⟩
  have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := zmod2_cases
  rcases hc c₀ with rfl | rfl <;> rcases hc c₁ with rfl | rfl
  · rcases hc c₂ with rfl | rfl <;> rcases hc c₃ with rfl | rfl <;>
      rcases hc c₄ with rfl | rfl <;>
      simp only [powL, Fin.prod_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
        Matrix.tail_cons, ite_true, ite_false, one_mul, mul_one,
        show (0 : ZMod 2) ≠ 1 by decide] at hfix2 hfix3 hl
    · exact hl (by decide)
    · exact moves_y5 hG hne hfix3
    · exact moves_y4 hG hne hfix3
    · exact moves_y4y5 hG hq hne hfix3
    · exact moves_y3 hG hne hfix2
    · exact moves_y3y5 hG hne hfix3
    · exact moves_y3y4 hG hne hfix2
    · exact moves_y3y4y5 hG hq hne hfix3
  all_goals
    rcases hc c₂ with rfl | rfl <;> rcases hc c₃ with rfl | rfl <;>
      rcases hc c₄ with rfl | rfl <;>
      simp only [powL, Fin.prod_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
        Matrix.tail_cons, ite_true, ite_false, one_mul, mul_one,
        show (0 : ZMod 2) ≠ 1 by decide] at hfix2 hfix3
  all_goals
    first
    | (refine moves_of_beta β hβ ?_ hfix2
       simp only [map_mul, toAdd_mul, hb]
       exact a2_moves _ (by decide))
    | (refine moves_of_beta β hβ ?_ hfix3
       simp only [map_mul, toAdd_mul, hb]
       exact a3_moves _ (by decide))

end CFSG.Quasithin.H13.A6.L4Ind
