module

public import CFSG.Milestones.ASVolI.B4Natural

public section

namespace CFSG.ASVolI

open Matrix

section SL3Defs

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {K : Type} [Field K]

@[expose] def burnsideB49x_fixN (B : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)) :
    Submodule K (Fin 3 → K) where
  carrier := {x | ∀ b ∈ B, (b : Matrix (Fin 3) (Fin 3) K) *ᵥ x = x}
  add_mem' := by
    intro x y hx hy b hb
    rw [Matrix.mulVec_add, hx b hb, hy b hb]
  zero_mem' := by
    intro b _
    exact Matrix.mulVec_zero _
  smul_mem' := by
    intro c x hx b hb
    rw [Matrix.mulVec_smul, hx b hb]

@[expose] def burnsideB49x_fixD (B : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)) :
    Submodule K (Fin 3 → K) where
  carrier := {x | ∀ b ∈ B,
    ((b⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ *ᵥ x = x}
  add_mem' := by
    intro x y hx hy b hb
    rw [Matrix.mulVec_add, hx b hb, hy b hb]
  zero_mem' := by
    intro b _
    exact Matrix.mulVec_zero _
  smul_mem' := by
    intro c x hx b hb
    rw [Matrix.mulVec_smul, hx b hb]

@[expose] def burnsideB49x_RW (W : Submodule K (Fin 3 → K)) :
    Subgroup (Matrix.SpecialLinearGroup (Fin 3) K) where
  carrier := {g | (∀ x, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ x - x ∈ W) ∧
    ∀ w ∈ W, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ w = w}
  one_mem' := by
    refine ⟨fun x => ?_, fun w _ => ?_⟩
    · rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec, sub_self]
      exact W.zero_mem
    · rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨fun x => ?_, fun w hw => ?_⟩
    · rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
      have e : (a : Matrix (Fin 3) (Fin 3) K) *ᵥ ((b : Matrix (Fin 3) (Fin 3) K) *ᵥ x) - x =
          ((a : Matrix (Fin 3) (Fin 3) K) *ᵥ ((b : Matrix (Fin 3) (Fin 3) K) *ᵥ x) -
            (b : Matrix (Fin 3) (Fin 3) K) *ᵥ x) + ((b : Matrix (Fin 3) (Fin 3) K) *ᵥ x - x) := by
        abel
      rw [e]
      exact W.add_mem (ha1 _) (hb1 x)
    · rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hb2 w hw, ha2 w hw]
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    have hinv : ∀ y, (a : Matrix (Fin 3) (Fin 3) K) *ᵥ
        (((a⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ y) = y := by
      intro y
      rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    have hinv' : ∀ y, ((a⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        ((a : Matrix (Fin 3) (Fin 3) K) *ᵥ y) = y := by
      intro y
      rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    refine ⟨fun x => ?_, fun w hw => ?_⟩
    · have h := W.neg_mem (ha1
        (((a⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x))
      rwa [hinv, neg_sub] at h
    · calc ((a⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w =
            ((a⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
              ((a : Matrix (Fin 3) (Fin 3) K) *ᵥ w) := by rw [ha2 w hw]
        _ = w := hinv' w

theorem burnsideB49x_sl3_mem_RW {W : Submodule K (Fin 3 → K)}
    {g : Matrix.SpecialLinearGroup (Fin 3) K} :
    g ∈ burnsideB49x_RW W ↔ (∀ x, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ x - x ∈ W) ∧
      ∀ w ∈ W, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ w = w := Iff.rfl

theorem burnsideB49x_sl3_mem_fixN {B : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)}
    {x : Fin 3 → K} :
    x ∈ burnsideB49x_fixN B ↔ ∀ b ∈ B, (b : Matrix (Fin 3) (Fin 3) K) *ᵥ x = x := Iff.rfl

theorem burnsideB49x_sl3_mem_fixD {B : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)}
    {x : Fin 3 → K} :
    x ∈ burnsideB49x_fixD B ↔ ∀ b ∈ B,
      ((b⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ *ᵥ x = x :=
  Iff.rfl

end SL3Defs

section SL3Lin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {K : Type} [Field K]

theorem burnsideB49x_sl3_dot_ext {a a' : Fin 3 → K} (h : ∀ x, a ⬝ᵥ x = a' ⬝ᵥ x) : a = a' := by
  funext i
  have := h (Pi.single i 1)
  rwa [dotProduct_single_one, dotProduct_single_one] at this

theorem burnsideB49x_sl3_transpose_dot (M : Matrix (Fin 3) (Fin 3) K) (a b : Fin 3 → K) :
    (Mᵀ *ᵥ a) ⬝ᵥ b = a ⬝ᵥ (M *ᵥ b) := by
  rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]

theorem burnsideB49x_sl3_exists_dot_one {r : Fin 3 → K} (hr : r ≠ 0) :
    ∃ x : Fin 3 → K, r ⬝ᵥ x = 1 := by
  obtain ⟨i, hi⟩ : ∃ i, r i ≠ 0 := Function.ne_iff.1 hr
  refine ⟨Pi.single i (r i)⁻¹, ?_⟩
  rw [dotProduct_single]
  exact mul_inv_cancel₀ hi

@[expose] def burnsideB49x_sl3_tv (u r : Fin 3 → K) (h : r ⬝ᵥ u = 0) :
    Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨1 + Matrix.vecMulVec u r, by
    rw [Matrix.vecMulVec_eq (ι := Unit), Matrix.det_one_add_replicateCol_mul_replicateRow, h,
      add_zero]⟩

theorem burnsideB49x_sl3_tv_mulVec (u r : Fin 3 → K) (h : r ⬝ᵥ u = 0) (x : Fin 3 → K) :
    ((burnsideB49x_sl3_tv u r h : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ x = x + (r ⬝ᵥ x) • u := by
  show (1 + Matrix.vecMulVec u r) *ᵥ x = x + (r ⬝ᵥ x) • u
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul]

theorem burnsideB49x_sl3_hyperplane {H : Submodule K (Fin 3 → K)}
    (hH : Module.finrank K H = 2) : ∃ r : Fin 3 → K, r ≠ 0 ∧ ∀ x, x ∈ H ↔ r ⬝ᵥ x = 0 := by
  have hlt : H < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => ?_
    have h3 : Module.finrank K H = 3 := by
      rw [h, finrank_top, Module.finrank_fin_fun]
    omega
  obtain ⟨f, hf0, hHf⟩ := Submodule.exists_le_ker_of_lt_top H hlt
  obtain ⟨r, hfr⟩ : ∃ r : Fin 3 → K, ∀ x, f x = r ⬝ᵥ x := by
    refine ⟨fun i => f (fun j => if i = j then 1 else 0), fun x => ?_⟩
    rw [LinearMap.pi_apply_eq_sum_univ f x, dotProduct]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, mul_comm]
  have hr0 : r ≠ 0 := by
    intro h0
    apply hf0
    refine LinearMap.ext fun x => ?_
    rw [hfr, h0, zero_dotProduct, LinearMap.zero_apply]
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  rw [Module.finrank_fin_fun] at hrank
  have hrange : Module.finrank K (LinearMap.range f) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range f)
    rwa [Module.finrank_self] at this
  have hker : LinearMap.ker f ≠ ⊤ := fun h => hf0 (LinearMap.ker_eq_top.1 h)
  have hlt3 := Submodule.finrank_lt hker
  rw [Module.finrank_fin_fun] at hlt3
  have heq : H = LinearMap.ker f := Submodule.eq_of_le_of_finrank_eq hHf (by omega)
  refine ⟨r, hr0, fun x => ?_⟩
  rw [heq, LinearMap.mem_ker, hfr]

theorem burnsideB49x_sl3_rep {H : Submodule K (Fin 3 → K)} {r x₀ : Fin 3 → K}
    (hHr : ∀ x, x ∈ H ↔ r ⬝ᵥ x = 0) (hx₀ : r ⬝ᵥ x₀ = 1) {N : Matrix (Fin 3) (Fin 3) K}
    (hN : ∀ h ∈ H, N *ᵥ h = h) (x : Fin 3 → K) :
    N *ᵥ x = x + (r ⬝ᵥ x) • (N *ᵥ x₀ - x₀) := by
  have hmem : x - (r ⬝ᵥ x) • x₀ ∈ H := by
    rw [hHr, dotProduct_sub, dotProduct_smul, hx₀, smul_eq_mul, mul_one, sub_self]
  have h := hN _ hmem
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul] at h
  calc N *ᵥ x = (N *ᵥ x - (r ⬝ᵥ x) • (N *ᵥ x₀)) + (r ⬝ᵥ x) • (N *ᵥ x₀) :=
        (sub_add_cancel _ _).symm
    _ = (x - (r ⬝ᵥ x) • x₀) + (r ⬝ᵥ x) • (N *ᵥ x₀) := by rw [h]
    _ = x + (r ⬝ᵥ x) • (N *ᵥ x₀ - x₀) := by rw [smul_sub]; abel

theorem burnsideB49x_sl3_tv_mem {H : Submodule K (Fin 3 → K)} {r : Fin 3 → K}
    (hHr : ∀ x, x ∈ H ↔ r ⬝ᵥ x = 0) {u : Fin 3 → K} (hu : r ⬝ᵥ u = 0) :
    burnsideB49x_sl3_tv u r hu ∈ burnsideB49x_RW H := by
  refine burnsideB49x_sl3_mem_RW.2 ⟨fun x => ?_, fun w hw => ?_⟩
  · rw [burnsideB49x_sl3_tv_mulVec, add_sub_cancel_left]
    exact H.smul_mem _ ((hHr u).2 hu)
  · rw [burnsideB49x_sl3_tv_mulVec, (hHr w).1 hw, zero_smul, add_zero]

theorem burnsideB49x_sl3_RW_ne {H p : Submodule K (Fin 3 → K)} :
    Module.finrank K H = 2 → Module.finrank K p = 1 →
      burnsideB49x_RW H ≠ burnsideB49x_RW p := by
  intro hH hp heq
  obtain ⟨r, hr0, hHr⟩ := burnsideB49x_sl3_hyperplane hH
  obtain ⟨x₀, hx₀⟩ := burnsideB49x_sl3_exists_dot_one hr0
  have hle : H ≤ p := by
    intro u hu
    have hru : r ⬝ᵥ u = 0 := (hHr u).1 hu
    have hmem := burnsideB49x_sl3_tv_mem hHr hru
    rw [heq] at hmem
    have h1 := (burnsideB49x_sl3_mem_RW.1 hmem).1 x₀
    rwa [burnsideB49x_sl3_tv_mulVec, hx₀, one_smul, add_sub_cancel_left] at h1
  have := Submodule.finrank_mono hle
  omega

theorem burnsideB49x_sl3_tau_two (w : Fin 2 → K) (y : Fin 3 → K) :
    (((burnsideB49_tau w : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      y) 2 = y 2 := by
  rw [burnsideB49_tau_mulVec, burnsideB49_vec3_zero2]

theorem burnsideB49x_sl3_tau_fix (w : Fin 2 → K) {y : Fin 3 → K} (hy : y 2 = 0) :
    ((burnsideB49_tau w : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      y = y := by
  rw [burnsideB49_tau_mulVec, hy, zero_smul, add_zero]
  conv_rhs => rw [← burnsideB49_vec3_ysub y, hy]

theorem burnsideB49x_sl3_tau_conj {H : Submodule K (Fin 3 → K)} :
    Module.finrank K H = 2 → ∃ g : Matrix.SpecialLinearGroup (Fin 3) K, ∀ w : Fin 2 → K,
      g⁻¹ * burnsideB49_tau w * g ∈ burnsideB49x_RW H := by
  intro hH
  obtain ⟨r, hr0, hHr⟩ := burnsideB49x_sl3_hyperplane hH
  obtain ⟨g, hg⟩ := burnsideB49_exists_row r hr0
  have hrow : ∀ z : Fin 3 → K, ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ z) 2 = r ⬝ᵥ z := by
    intro z
    simp only [Matrix.mulVec, dotProduct, hg]
  have hconj : ∀ w : Fin 2 → K, g * (g⁻¹ * burnsideB49_tau w * g) = burnsideB49_tau w * g := by
    intro w
    group
  refine ⟨g, fun w => burnsideB49x_sl3_mem_RW.2 ⟨fun x => ?_, fun h hh => ?_⟩⟩
  · have key : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ
        (((g⁻¹ * burnsideB49_tau w * g : Matrix.SpecialLinearGroup (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) *ᵥ x) =
        ((burnsideB49_tau w : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
          ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ x) := by
      rw [burnsideB49_mulVec_mulVec_sl, burnsideB49_mulVec_mulVec_sl, hconj]
    rw [hHr, ← hrow, Matrix.mulVec_sub, key, Pi.sub_apply, burnsideB49x_sl3_tau_two, sub_self]
  · have hgh : ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ h) 2 = 0 := by
      rw [hrow]
      exact (hHr h).1 hh
    apply burnsideB49_mulVec_inj g
    rw [burnsideB49_mulVec_mulVec_sl, hconj, ← burnsideB49_mulVec_mulVec_sl,
      burnsideB49x_sl3_tau_fix w hgh]

theorem burnsideB49x_sl3_eq_bot_of_three {B : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)}
    (h : Module.finrank K (burnsideB49x_fixN B) = 3) : B = ⊥ := by
  have htop : burnsideB49x_fixN B = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [h, Module.finrank_fin_fun])
  rw [Subgroup.eq_bot_iff_forall]
  intro b hb
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_one]
  apply burnsideB49_eq_one_of_mulVec
  intro x
  have hx : x ∈ burnsideB49x_fixN B := by
    rw [htop]
    exact Submodule.mem_top
  exact burnsideB49x_sl3_mem_fixN.1 hx b hb

theorem burnsideB49x_sl3_dual_fwd {H : Submodule K (Fin 3 → K)} {r : Fin 3 → K}
    (hHr : ∀ x, x ∈ H ↔ r ⬝ᵥ x = 0) {M : Matrix (Fin 3) (Fin 3) K}
    (hM1 : ∀ y, M *ᵥ y - y ∈ K ∙ r) (hM2 : ∀ w ∈ K ∙ r, M *ᵥ w = w) :
    (∀ x, Mᵀ *ᵥ x - x ∈ H) ∧ ∀ h ∈ H, Mᵀ *ᵥ h = h := by
  have hMr : M *ᵥ r = r := hM2 r (Submodule.mem_span_singleton_self r)
  refine ⟨fun x => ?_, fun h hh => ?_⟩
  · rw [hHr, dotProduct_sub, dotProduct_comm r (Mᵀ *ᵥ x), burnsideB49x_sl3_transpose_dot, hMr,
      dotProduct_comm x r, sub_self]
  · apply burnsideB49x_sl3_dot_ext
    intro y
    rw [burnsideB49x_sl3_transpose_dot]
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (hM1 y)
    have hMy : M *ᵥ y = y + a • r := by
      rw [ha]
      abel
    rw [hMy, dotProduct_add, dotProduct_smul, dotProduct_comm h r, (hHr h).1 hh, smul_zero,
      add_zero]

theorem burnsideB49x_sl3_dual_bwd {H : Submodule K (Fin 3 → K)} {r x₀ : Fin 3 → K}
    (hHr : ∀ x, x ∈ H ↔ r ⬝ᵥ x = 0) (hx₀ : r ⬝ᵥ x₀ = 1) {M : Matrix (Fin 3) (Fin 3) K}
    (hN1 : ∀ x, Mᵀ *ᵥ x - x ∈ H) (hN2 : ∀ h ∈ H, Mᵀ *ᵥ h = h) :
    (∀ y, M *ᵥ y - y ∈ K ∙ r) ∧ ∀ w ∈ K ∙ r, M *ᵥ w = w := by
  have hdot : ∀ y x, (M *ᵥ y) ⬝ᵥ x = y ⬝ᵥ (Mᵀ *ᵥ x) := by
    intro y x
    rw [← burnsideB49x_sl3_transpose_dot, Matrix.transpose_transpose]
  refine ⟨fun y => ?_, fun w hw => ?_⟩
  · rw [Submodule.mem_span_singleton]
    refine ⟨y ⬝ᵥ (Mᵀ *ᵥ x₀ - x₀), ?_⟩
    apply burnsideB49x_sl3_dot_ext
    intro x
    rw [smul_dotProduct, sub_dotProduct, hdot, burnsideB49x_sl3_rep hHr hx₀ hN2 x,
      dotProduct_add, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    ring
  · obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
    rw [Matrix.mulVec_smul]
    congr 1
    apply burnsideB49x_sl3_dot_ext
    intro x
    rw [hdot]
    have h1 := (hHr _).1 (hN1 x)
    rw [dotProduct_sub, sub_eq_zero] at h1
    rw [h1]

theorem burnsideB49x_sl3_mem_RW_line_iff {H : Submodule K (Fin 3 → K)} {r : Fin 3 → K}
    (hHr : ∀ x, x ∈ H ↔ r ⬝ᵥ x = 0) (hr0 : r ≠ 0) (c : Matrix.SpecialLinearGroup (Fin 3) K) :
    c ∈ burnsideB49x_RW (K ∙ r) ↔
      CFSG.Quasithin.JonesParshall.invTransposeSL 3 K c ∈ burnsideB49x_RW H := by
  obtain ⟨x₀, hx₀⟩ := burnsideB49x_sl3_exists_dot_one hr0
  rw [← Subgroup.inv_mem_iff (x := c)]
  constructor
  · intro h
    have h' := burnsideB49x_sl3_mem_RW.1 h
    exact burnsideB49x_sl3_mem_RW.2 (burnsideB49x_sl3_dual_fwd hHr h'.1 h'.2)
  · intro h
    have h' := burnsideB49x_sl3_mem_RW.1 h
    exact burnsideB49x_sl3_mem_RW.2 (burnsideB49x_sl3_dual_bwd hHr hx₀ h'.1 h'.2)

theorem burnsideB49x_sl3_fixN_map (B : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)) :
    burnsideB49x_fixN (B.map (CFSG.Quasithin.JonesParshall.invTransposeSL 3 K).toMonoidHom) =
      burnsideB49x_fixD B := by
  ext x
  rw [burnsideB49x_sl3_mem_fixN, burnsideB49x_sl3_mem_fixD]
  constructor
  · intro h b hb
    exact h _ (Subgroup.mem_map_of_mem _ hb)
  · rintro h _ ⟨b, hb, rfl⟩
    exact h b hb

theorem burnsideB49x_sl3_map_comm {B : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)}
    (hc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) :
    ∀ b ∈ B.map (CFSG.Quasithin.JonesParshall.invTransposeSL 3 K).toMonoidHom,
      ∀ b' ∈ B.map (CFSG.Quasithin.JonesParshall.invTransposeSL 3 K).toMonoidHom,
        b * b' = b' * b := by
  rintro _ ⟨b, hb, rfl⟩ _ ⟨b', hb', rfl⟩
  rw [← map_mul, ← map_mul, hc b hb b' hb']

theorem burnsideB49x_sl3_map_sq {B : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)}
    (h2 : ∀ b ∈ B, b * b = 1) :
    ∀ b ∈ B.map (CFSG.Quasithin.JonesParshall.invTransposeSL 3 K).toMonoidHom, b * b = 1 := by
  rintro _ ⟨b, hb, rfl⟩
  rw [← map_mul, h2 b hb, map_one]

end SL3Lin

section SL3Card

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {K : Type} [Field K] [Finite K]

theorem burnsideB49x_sl3_card_RW_le (W : Submodule K (Fin 3 → K)) :
    Nat.card (burnsideB49x_RW W) ≤ Nat.card W ^ 3 := by
  let φ : burnsideB49x_RW W → (Fin 3 → W) := fun s i =>
    ⟨((s : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single i 1 -
      Pi.single i 1, (burnsideB49x_sl3_mem_RW.1 s.2).1 _⟩
  have hinj : Function.Injective φ := by
    intro s s' h
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    have h1 := congrArg Subtype.val (congrFun h j)
    simp only [φ, sub_left_inj, Matrix.mulVec_single_one] at h1
    exact congrFun h1 i
  have := Nat.card_le_card_of_injective φ hinj
  rwa [Nat.card_fun, Nat.card_fin] at this

theorem burnsideB49x_sl3_card_RW {H : Submodule K (Fin 3 → K)} :
    Module.finrank K H = 2 → Nat.card (burnsideB49x_RW H) = Nat.card K ^ 2 := by
  intro hH
  obtain ⟨r, hr0, hHr⟩ := burnsideB49x_sl3_hyperplane hH
  obtain ⟨x₀, hx₀⟩ := burnsideB49x_sl3_exists_dot_one hr0
  let φ : burnsideB49x_RW H → H := fun s =>
    ⟨((s : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x₀ - x₀,
      (burnsideB49x_sl3_mem_RW.1 s.2).1 x₀⟩
  have hinj : Function.Injective φ := by
    intro s s' h
    have h1 := congrArg Subtype.val h
    simp only [φ, sub_left_inj] at h1
    apply Subtype.ext
    apply burnsideB49_sl_ext
    intro x
    rw [burnsideB49x_sl3_rep hHr hx₀ (burnsideB49x_sl3_mem_RW.1 s.2).2 x,
      burnsideB49x_sl3_rep hHr hx₀ (burnsideB49x_sl3_mem_RW.1 s'.2).2 x, h1]
  have hsurj : Function.Surjective φ := by
    rintro ⟨u, hu⟩
    have hru : r ⬝ᵥ u = 0 := (hHr u).1 hu
    refine ⟨⟨burnsideB49x_sl3_tv u r hru, burnsideB49x_sl3_tv_mem hHr hru⟩, ?_⟩
    apply Subtype.ext
    show ((burnsideB49x_sl3_tv u r hru : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ x₀ - x₀ = u
    rw [burnsideB49x_sl3_tv_mulVec, hx₀, one_smul, add_sub_cancel_left]
  rw [Nat.card_eq_of_bijective φ ⟨hinj, hsurj⟩, Module.natCard_eq_pow_finrank (K := K), hH]

end SL3Card

section SL3Pair

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {K : Type} [Field K] [CharP K 2]

theorem burnsideB49x_sl3_pair (b t : Matrix.SpecialLinearGroup (Fin 3) K) {u r : Fin 3 → K}
    (hu : u ≠ 0) (hr : r ≠ 0)
    (ht : ∀ x, (t : Matrix (Fin 3) (Fin 3) K) *ᵥ x = x + (r ⬝ᵥ x) • u)
    (hbt : b * t = t * b) (hb2 : b * b = 1) (x : Fin 3 → K) :
    (t : Matrix (Fin 3) (Fin 3) K) *ᵥ ((b : Matrix (Fin 3) (Fin 3) K) *ᵥ x - x) =
      (b : Matrix (Fin 3) (Fin 3) K) *ᵥ x - x := by
  have hcomm : ∀ y, (b : Matrix (Fin 3) (Fin 3) K) *ᵥ ((t : Matrix (Fin 3) (Fin 3) K) *ᵥ y) =
      (t : Matrix (Fin 3) (Fin 3) K) *ᵥ ((b : Matrix (Fin 3) (Fin 3) K) *ᵥ y) := by
    intro y
    rw [burnsideB49_mulVec_mulVec_sl, burnsideB49_mulVec_mulVec_sl, hbt]
  have hbb : ∀ y, (b : Matrix (Fin 3) (Fin 3) K) *ᵥ ((b : Matrix (Fin 3) (Fin 3) K) *ᵥ y) = y := by
    intro y
    rw [burnsideB49_mulVec_mulVec_sl, hb2, burnsideB49_mulVec_one_sl]
  have h1 : ∀ y, (r ⬝ᵥ ((b : Matrix (Fin 3) (Fin 3) K) *ᵥ y)) • u =
      (r ⬝ᵥ y) • ((b : Matrix (Fin 3) (Fin 3) K) *ᵥ u) := by
    intro y
    have h := hcomm y
    rw [ht y, ht ((b : Matrix (Fin 3) (Fin 3) K) *ᵥ y), Matrix.mulVec_add,
      Matrix.mulVec_smul] at h
    exact (add_left_cancel h).symm
  obtain ⟨x₀, hx₀⟩ := burnsideB49x_sl3_exists_dot_one hr
  set c := r ⬝ᵥ ((b : Matrix (Fin 3) (Fin 3) K) *ᵥ x₀) with hc
  have hbu : (b : Matrix (Fin 3) (Fin 3) K) *ᵥ u = c • u := by
    have h := h1 x₀
    rw [hx₀, one_smul] at h
    exact h.symm
  have hc1 : c = 1 := by
    have h := hbb u
    rw [hbu, Matrix.mulVec_smul, hbu, smul_smul] at h
    have h' : (c * c - 1) • u = 0 := by rw [sub_smul, h, one_smul, sub_self]
    have hcc : c * c - 1 = 0 := by
      rcases smul_eq_zero.1 h' with h'' | h''
      · exact h''
      · exact absurd h'' hu
    have htwo : (2 : K) = 0 := CharTwo.two_eq_zero
    have hsq : (c - 1) ^ 2 = 0 := by linear_combination hcc + (1 - c) * htwo
    exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 hsq)
  have hrb : ∀ y, r ⬝ᵥ ((b : Matrix (Fin 3) (Fin 3) K) *ᵥ y) = r ⬝ᵥ y := by
    intro y
    have h := h1 y
    rw [hbu, hc1, one_smul] at h
    exact smul_left_injective K hu h
  rw [ht, dotProduct_sub, hrb, sub_self, zero_smul, add_zero]

end SL3Pair

section SL3Main

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem burnsideB49x_sl3_rank_one (t : Matrix.SpecialLinearGroup (Fin 3) K) (ht1 : t ≠ 1)
    (ht2 : t * t = 1) :
    ∃ u r : Fin 3 → K, u ≠ 0 ∧ r ≠ 0 ∧
      ∀ x, (t : Matrix (Fin 3) (Fin 3) K) *ᵥ x = x + (r ⬝ᵥ x) • u := by
  apply burnsideB49_rank_one_of_card t ht1
  set f := Matrix.mulVecLin ((t : Matrix (Fin 3) (Fin 3) K) - 1) with hf
  have hfx : ∀ x, f x = (t : Matrix (Fin 3) (Fin 3) K) *ᵥ x - x := by
    intro x
    rw [hf, Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec]
  have hle : LinearMap.range f ≤ LinearMap.ker f := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, hfx, hfx, Matrix.mulVec_sub, burnsideB49_mulVec_mulVec_sl, ht2,
      burnsideB49_mulVec_one_sl]
    have htwo : (2 : K) = 0 := CharTwo.two_eq_zero
    funext i
    simp only [Pi.sub_apply, Pi.zero_apply]
    linear_combination (x i - ((t : Matrix (Fin 3) (Fin 3) K) *ᵥ x) i) * htwo
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  rw [Module.finrank_fin_fun] at hrank
  have hmono := Submodule.finrank_mono hle
  have h1 : Module.finrank K (LinearMap.range f) ≤ 1 := by omega
  change Nat.card ↥(LinearMap.range f) ≤ Nat.card K
  rw [Module.natCard_eq_pow_finrank (K := K) (V := ↥(LinearMap.range f))]
  calc Nat.card K ^ Module.finrank K (LinearMap.range f) ≤ Nat.card K ^ 1 :=
        Nat.pow_le_pow_right Nat.card_pos h1
    _ = Nat.card K := pow_one _

theorem burnsideB49x_sl3_le_RW {B : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)}
    (hc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) (h2 : ∀ b ∈ B, b * b = 1) :
    B ≤ burnsideB49x_RW (burnsideB49x_fixN B) := by
  intro b hb
  refine burnsideB49x_sl3_mem_RW.2 ⟨fun x => burnsideB49x_sl3_mem_fixN.2 fun t ht => ?_,
    fun w hw => burnsideB49x_sl3_mem_fixN.1 hw b hb⟩
  by_cases ht1 : t = 1
  · rw [ht1, burnsideB49_mulVec_one_sl]
  obtain ⟨u, r, hu, hr, htx⟩ := burnsideB49x_sl3_rank_one t ht1 (h2 t ht)
  exact burnsideB49x_sl3_pair b t hu hr htx (hc b hb t ht) (h2 b hb) x

theorem burnsideB49x_sl3_lt_of_le_one {B : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)}
    (hc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) (h2 : ∀ b ∈ B, b * b = 1)
    (h : Module.finrank K (burnsideB49x_fixN B) ≤ 1) :
    Nat.card B * Nat.card (burnsideB49x_fixN B) ^ 2 < Nat.card K ^ 6 := by
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hF : Nat.card (burnsideB49x_fixN B) ≤ Nat.card K := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := ↥(burnsideB49x_fixN B))]
    calc Nat.card K ^ Module.finrank K (burnsideB49x_fixN B) ≤ Nat.card K ^ 1 :=
          Nat.pow_le_pow_right (by omega) h
      _ = Nat.card K := pow_one _
  have hB : Nat.card B ≤ Nat.card (burnsideB49x_fixN B) ^ 3 :=
    (Subgroup.card_le_of_le (burnsideB49x_sl3_le_RW hc h2)).trans
      (burnsideB49x_sl3_card_RW_le _)
  calc Nat.card B * Nat.card (burnsideB49x_fixN B) ^ 2
      ≤ Nat.card (burnsideB49x_fixN B) ^ 3 * Nat.card (burnsideB49x_fixN B) ^ 2 :=
        Nat.mul_le_mul_right _ hB
    _ = Nat.card (burnsideB49x_fixN B) ^ 5 := by ring
    _ ≤ Nat.card K ^ 5 := Nat.pow_le_pow_left hF 5
    _ < Nat.card K ^ 6 := Nat.pow_lt_pow_right hq (by norm_num)

theorem burnsideB49x_sl3_boundN {B : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)}
    (hc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) (h2 : ∀ b ∈ B, b * b = 1) :
    Nat.card B * Nat.card (burnsideB49x_fixN B) ^ 2 ≤ Nat.card K ^ 6 := by
  have hd : Module.finrank K (burnsideB49x_fixN B) ≤ 3 := by
    have := Submodule.finrank_le (burnsideB49x_fixN B)
    rwa [Module.finrank_fin_fun] at this
  have hcard := Module.natCard_eq_pow_finrank (K := K) (V := ↥(burnsideB49x_fixN B))
  rcases (by omega : Module.finrank K (burnsideB49x_fixN B) ≤ 1 ∨
      Module.finrank K (burnsideB49x_fixN B) = 2 ∨ Module.finrank K (burnsideB49x_fixN B) = 3)
    with h | h | h
  · exact (burnsideB49x_sl3_lt_of_le_one hc h2 h).le
  · have hB : Nat.card B ≤ Nat.card K ^ 2 :=
      (Subgroup.card_le_of_le (burnsideB49x_sl3_le_RW hc h2)).trans_eq
        (burnsideB49x_sl3_card_RW h)
    rw [hcard, h]
    calc Nat.card B * (Nat.card K ^ 2) ^ 2 ≤ Nat.card K ^ 2 * (Nat.card K ^ 2) ^ 2 :=
          Nat.mul_le_mul_right _ hB
      _ = Nat.card K ^ 6 := by ring
  · have hB1 : Nat.card B = 1 := by
      rw [burnsideB49x_sl3_eq_bot_of_three h, Subgroup.card_bot]
    rw [hB1, hcard, h]
    ring_nf
    exact le_rfl

theorem burnsideB49x_sl3_eqN {B : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)}
    (hc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) (h2 : ∀ b ∈ B, b * b = 1) :
    B ≠ ⊥ → Nat.card B * Nat.card (burnsideB49x_fixN B) ^ 2 = Nat.card K ^ 6 →
      ∃ H : Submodule K (Fin 3 → K), Module.finrank K H = 2 ∧ B = burnsideB49x_RW H := by
  intro hB heq
  have hd : Module.finrank K (burnsideB49x_fixN B) ≤ 3 := by
    have := Submodule.finrank_le (burnsideB49x_fixN B)
    rwa [Module.finrank_fin_fun] at this
  have hcard := Module.natCard_eq_pow_finrank (K := K) (V := ↥(burnsideB49x_fixN B))
  have hq : 1 < Nat.card K := Finite.one_lt_card
  rcases (by omega : Module.finrank K (burnsideB49x_fixN B) ≤ 1 ∨
      Module.finrank K (burnsideB49x_fixN B) = 2 ∨ Module.finrank K (burnsideB49x_fixN B) = 3)
    with h | h | h
  · exact absurd heq (burnsideB49x_sl3_lt_of_le_one hc h2 h).ne
  · refine ⟨burnsideB49x_fixN B, h, ?_⟩
    have hBq : Nat.card B = Nat.card K ^ 2 := by
      rw [hcard, h] at heq
      have hpos : 0 < (Nat.card K ^ 2) ^ 2 := by positivity
      refine Nat.eq_of_mul_eq_mul_right hpos ?_
      rw [heq]
      ring
    exact Subgroup.eq_of_le_of_card_ge (burnsideB49x_sl3_le_RW hc h2)
      (by rw [burnsideB49x_sl3_card_RW h, hBq])
  · exact absurd (burnsideB49x_sl3_eq_bot_of_three h) hB

theorem burnsideB49x_sl3_boundD {B : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)}
    (hc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) (h2 : ∀ b ∈ B, b * b = 1) :
    Nat.card B * Nat.card (burnsideB49x_fixD B) ^ 2 ≤ Nat.card K ^ 6 := by
  have h := burnsideB49x_sl3_boundN (burnsideB49x_sl3_map_comm hc) (burnsideB49x_sl3_map_sq h2)
  rwa [Subgroup.card_map_of_injective (CFSG.Quasithin.JonesParshall.invTransposeSL 3 K).injective,
    burnsideB49x_sl3_fixN_map] at h

theorem burnsideB49x_sl3_eqD {B : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)}
    (hc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) (h2 : ∀ b ∈ B, b * b = 1) :
    B ≠ ⊥ → Nat.card B * Nat.card (burnsideB49x_fixD B) ^ 2 = Nat.card K ^ 6 →
      ∃ p : Submodule K (Fin 3 → K), Module.finrank K p = 1 ∧ B = burnsideB49x_RW p := by
  intro hB heq
  have hθ : Function.Injective (CFSG.Quasithin.JonesParshall.invTransposeSL 3 K).toMonoidHom :=
    (CFSG.Quasithin.JonesParshall.invTransposeSL 3 K).injective
  have hB' : B.map (CFSG.Quasithin.JonesParshall.invTransposeSL 3 K).toMonoidHom ≠ ⊥ :=
    fun h => hB ((Subgroup.map_eq_bot_iff_of_injective B hθ).1 h)
  obtain ⟨H, hH, hBH⟩ := burnsideB49x_sl3_eqN (burnsideB49x_sl3_map_comm hc)
    (burnsideB49x_sl3_map_sq h2) hB'
    (by rw [Subgroup.card_map_of_injective hθ, burnsideB49x_sl3_fixN_map]; exact heq)
  obtain ⟨r, hr0, hHr⟩ := burnsideB49x_sl3_hyperplane hH
  refine ⟨K ∙ r, finrank_span_singleton hr0, ?_⟩
  ext b
  rw [burnsideB49x_sl3_mem_RW_line_iff hHr hr0 b, ← hBH]
  exact (Subgroup.mem_map_iff_mem hθ).symm

end SL3Main

end CFSG.ASVolI
