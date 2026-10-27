module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45PairSpOrd3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.PairSpLem

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
variable {B : LinearMap.BilinForm (ZMod 2) W} {a b : W ≃ₗ[ZMod 2] W}

structure FiveVec (a b : W ≃ₗ[ZMod 2] W) (w : Fin 5 → W) : Prop where
  inj : Function.Injective w
  a0 : a (w 0) = w 1
  a1 : a (w 1) = w 2
  a2 : a (w 2) = w 0
  a3 : a (w 3) = w 3
  a4 : a (w 4) = w 4
  b0 : b (w 0) = w 0
  b1 : b (w 1) = w 1
  b2 : b (w 2) = w 3
  b3 : b (w 3) = w 4
  b4 : b (w 4) = w 2
  span_a : commSp a ≤ Submodule.span (ZMod 2) (Set.range w)
  span_b : commSp b ≤ Submodule.span (ZMod 2) (Set.range w)

structure A5Data (B : LinearMap.BilinForm (ZMod 2) W) (a b : W ≃ₗ[ZMod 2] W) (p₀ q₀ : W) :
    Prop where
  hp₀ : p₀ ∈ commSp a
  hp₀0 : p₀ ≠ 0
  hp₀Q : ∀ q ∈ commSp b, B p₀ q = 0
  hq₀ : q₀ ∈ commSp b
  hq₀0 : q₀ ≠ 0
  hq₀P : ∀ p ∈ commSp a, B p q₀ = 0
  hnotperp : ∃ p₁ ∈ commSp a, ∃ q₁ ∈ commSp b, B p₁ q₁ ≠ 0

variable {p₀ q₀ : W}

theorem zmod2_eq_one_of_ne_zero {t : ZMod 2} (h : t ≠ 0) : t = 1 := by
  revert t; decide

theorem A5Data.a_q₀ (h : PairHyp B a b) (d : A5Data B a b p₀ q₀) : a q₀ = q₀ :=
  (fixed_iff_mem_orth h.nondeg h.ha.isom q₀).mpr
    (LinearMap.BilinForm.mem_orthogonal_iff.mpr d.hq₀P)

theorem A5Data.b_p₀ (h : PairHyp B a b) (d : A5Data B a b p₀ q₀) : b p₀ = p₀ :=
  (fixed_iff_mem_orth h.nondeg h.hb.isom p₀).mpr
    (LinearMap.BilinForm.mem_orthogonal_iff.mpr fun q hq => by
      rw [bil_comm_of_alt h.alt]; exact d.hp₀Q q hq)

theorem A5Data.bil_one (h : PairHyp B a b) (d : A5Data B a b p₀ q₀) :
    B (a p₀) (b q₀) = 1 := by
  obtain ⟨p₁, hp₁, q₁, hq₁, hne⟩ := d.hnotperp
  have hP := commSp_cases h.nondeg h.ha d.hp₀ d.hp₀0 p₁ hp₁
  have hQ := commSp_cases h.nondeg h.hb d.hq₀ d.hq₀0 q₁ hq₁
  rw [apply_sq_of_mem h.ha d.hp₀] at hP
  rw [apply_sq_of_mem h.hb d.hq₀] at hQ
  apply zmod2_eq_one_of_ne_zero
  intro h0
  apply hne
  rcases hP with rfl | rfl | rfl | rfl <;> rcases hQ with rfl | rfl | rfl | rfl <;>
    simp [map_add, h0, d.hp₀Q _ d.hq₀, d.hq₀P _ d.hp₀, d.hp₀Q _ (apply_mem_commSp d.hq₀),
      d.hq₀P _ (apply_mem_commSp d.hp₀)]

theorem A5Data.bil_a_p₀_p₀ (h : PairHyp B a b) (d : A5Data B a b p₀ q₀) : B (a p₀) p₀ = 1 := by
  rw [bil_comm_of_alt h.alt]; exact bil_self_apply h.nondeg h.alt h.ha d.hp₀ d.hp₀0

theorem A5Data.bil_b_q₀_q₀ (h : PairHyp B a b) (d : A5Data B a b p₀ q₀) : B (b q₀) q₀ = 1 := by
  rw [bil_comm_of_alt h.alt]; exact bil_self_apply h.nondeg h.alt h.hb d.hq₀ d.hq₀0

@[expose] def fiveW (a b : W ≃ₗ[ZMod 2] W) (p₀ q₀ : W) : Fin 5 → W :=
  ![a p₀ + q₀, a (a p₀) + q₀, p₀ + q₀, p₀ + b q₀, p₀ + b (b q₀)]

theorem A5Data.w3_orth (h : PairHyp B a b) (d : A5Data B a b p₀ q₀) :
    p₀ + b q₀ ∈ B.orthogonal (commSp a) := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro p hp
  have hP := commSp_cases h.nondeg h.ha d.hp₀ d.hp₀0 p hp
  rw [apply_sq_of_mem h.ha d.hp₀] at hP
  have h1 := d.bil_one h
  have h2 := d.bil_a_p₀_p₀ h
  have h3 : ∀ t : ZMod 2, t + t = 0 := by decide
  rcases hP with rfl | rfl | rfl | rfl <;>
    simp [map_add, h.alt.self_eq_zero, d.hp₀Q _ (apply_mem_commSp d.hq₀), h1, h2, h3]

theorem A5Data.w0_orth (h : PairHyp B a b) (d : A5Data B a b p₀ q₀) :
    a p₀ + q₀ ∈ B.orthogonal (commSp b) := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro q hq
  have hQ := commSp_cases h.nondeg h.hb d.hq₀ d.hq₀0 q hq
  rw [apply_sq_of_mem h.hb d.hq₀] at hQ
  have h1 := d.bil_one h
  have h1' : B (b q₀) (a p₀) = 1 := by rw [bil_comm_of_alt h.alt]; exact h1
  have h2 := d.bil_b_q₀_q₀ h
  have h3 : ∀ t : ZMod 2, t + t = 0 := by decide
  have h4 : B q₀ (a p₀) = 0 := by
    rw [bil_comm_of_alt h.alt]; exact d.hq₀P _ (apply_mem_commSp d.hp₀)
  rcases hQ with rfl | rfl | rfl | rfl <;>
    simp [map_add, h.alt.self_eq_zero, h1', h2, h3, h4]

theorem A5Data.five_inj (h : PairHyp B a b) (d : A5Data B a b p₀ q₀) :
    Function.Injective (fiveW a b p₀ q₀) := by
  have hP := apply_sq_of_mem h.ha d.hp₀
  have hQ := apply_sq_of_mem h.hb d.hq₀
  have g12 : B p₀ (a p₀) = 1 := bil_self_apply h.nondeg h.alt h.ha d.hp₀ d.hp₀0
  have g21 := d.bil_a_p₀_p₀ h
  have g24 := d.bil_one h
  have g42 : B (b q₀) (a p₀) = 1 := by rw [bil_comm_of_alt h.alt]; exact g24
  have g34 : B q₀ (b q₀) = 1 := bil_self_apply h.nondeg h.alt h.hb d.hq₀ d.hq₀0
  have g43 := d.bil_b_q₀_q₀ h
  have g13 : B p₀ q₀ = 0 := d.hp₀Q _ d.hq₀
  have g14 : B p₀ (b q₀) = 0 := d.hp₀Q _ (apply_mem_commSp d.hq₀)
  have g23 : B (a p₀) q₀ = 0 := d.hq₀P _ (apply_mem_commSp d.hp₀)
  have g31 : B q₀ p₀ = 0 := by rw [bil_comm_of_alt h.alt]; exact g13
  have g41 : B (b q₀) p₀ = 0 := by rw [bil_comm_of_alt h.alt]; exact g14
  have g32 : B q₀ (a p₀) = 0 := by rw [bil_comm_of_alt h.alt]; exact g23
  intro i j hij
  have e1 := congrArg (fun x => B x p₀) hij
  have e2 := congrArg (fun x => B x (a p₀)) hij
  have e3 := congrArg (fun x => B x q₀) hij
  have e4 := congrArg (fun x => B x (b q₀)) hij
  fin_cases i <;> fin_cases j <;>
    simp [fiveW, hP, hQ, map_add, h.alt.self_eq_zero, g12, g21, g24, g42, g43, g34, g13, g14, g23,
      g31, g41, g32] at e1 e2 e3 e4 ⊢

theorem A5Data.a_w3 (h : PairHyp B a b) (d : A5Data B a b p₀ q₀) :
    a (p₀ + b q₀) = p₀ + b q₀ :=
  (fixed_iff_mem_orth h.nondeg h.ha.isom _).mpr (d.w3_orth h)

theorem A5Data.a_w4 (h : PairHyp B a b) (d : A5Data B a b p₀ q₀) :
    a (p₀ + b (b q₀)) = p₀ + b (b q₀) := by
  refine (fixed_iff_mem_orth h.nondeg h.ha.isom _).mpr ?_
  have hQ := apply_sq_of_mem h.hb d.hq₀
  have hq₀P : q₀ ∈ B.orthogonal (commSp a) := LinearMap.BilinForm.mem_orthogonal_iff.mpr d.hq₀P
  have : p₀ + b (b q₀) = (p₀ + b q₀) + q₀ := by rw [hQ]; abel
  rw [this]
  exact add_mem (d.w3_orth h) hq₀P

theorem A5Data.b_w0 (h : PairHyp B a b) (d : A5Data B a b p₀ q₀) :
    b (a p₀ + q₀) = a p₀ + q₀ :=
  (fixed_iff_mem_orth h.nondeg h.hb.isom _).mpr (d.w0_orth h)

theorem A5Data.b_w1 (h : PairHyp B a b) (d : A5Data B a b p₀ q₀) :
    b (a (a p₀) + q₀) = a (a p₀) + q₀ := by
  refine (fixed_iff_mem_orth h.nondeg h.hb.isom _).mpr ?_
  have hP := apply_sq_of_mem h.ha d.hp₀
  have hp₀Q : p₀ ∈ B.orthogonal (commSp b) :=
    (fixed_iff_mem_orth h.nondeg h.hb.isom p₀).mp (d.b_p₀ h)
  have : a (a p₀) + q₀ = (a p₀ + q₀) + p₀ := by rw [hP]; abel
  rw [this]
  exact add_mem (d.w0_orth h) hp₀Q

theorem A5Data.span_a (h : PairHyp B a b) (d : A5Data B a b p₀ q₀) :
    commSp a ≤ Submodule.span (ZMod 2) (Set.range (fiveW a b p₀ q₀)) := by
  have hP := apply_sq_of_mem h.ha d.hp₀
  have m : ∀ i, fiveW a b p₀ q₀ i ∈ Submodule.span (ZMod 2) (Set.range (fiveW a b p₀ q₀)) :=
    fun i => Submodule.subset_span ⟨i, rfl⟩
  have c2 : ∀ x : W, x + x = 0 := fun x => add_self_eq_zero' x
  intro x hx
  have hc := commSp_cases h.nondeg h.ha d.hp₀ d.hp₀0 x hx
  have e1 : p₀ = fiveW a b p₀ q₀ 0 + fiveW a b p₀ q₀ 1 := by
    simp only [fiveW]; simp [hP]
    calc p₀ = p₀ + (a p₀ + a p₀) + (q₀ + q₀) := by rw [c2, c2, add_zero, add_zero]
      _ = _ := by abel
  have e2 : a p₀ = fiveW a b p₀ q₀ 1 + fiveW a b p₀ q₀ 2 := by
    simp only [fiveW]; simp [hP]
    calc a p₀ = a p₀ + (p₀ + p₀) + (q₀ + q₀) := by rw [c2, c2, add_zero, add_zero]
      _ = _ := by abel
  have e3 : a (a p₀) = fiveW a b p₀ q₀ 0 + fiveW a b p₀ q₀ 2 := by
    simp only [fiveW]; simp [hP]
    calc p₀ + a p₀ = p₀ + a p₀ + (q₀ + q₀) := by rw [c2, add_zero]
      _ = _ := by abel
  rcases hc with h0 | h0 | h0 | h0
  · rw [h0]; exact zero_mem _
  · rw [h0]; have := add_mem (m 0) (m 1); rwa [← e1] at this
  · rw [h0]; have := add_mem (m 1) (m 2); rwa [← e2] at this
  · rw [h0]; have := add_mem (m 0) (m 2); rwa [← e3] at this

theorem A5Data.span_b (h : PairHyp B a b) (d : A5Data B a b p₀ q₀) :
    commSp b ≤ Submodule.span (ZMod 2) (Set.range (fiveW a b p₀ q₀)) := by
  have hQ := apply_sq_of_mem h.hb d.hq₀
  have m : ∀ i, fiveW a b p₀ q₀ i ∈ Submodule.span (ZMod 2) (Set.range (fiveW a b p₀ q₀)) :=
    fun i => Submodule.subset_span ⟨i, rfl⟩
  have c2 : ∀ x : W, x + x = 0 := fun x => add_self_eq_zero' x
  intro x hx
  have hc := commSp_cases h.nondeg h.hb d.hq₀ d.hq₀0 x hx
  have e1 : q₀ = fiveW a b p₀ q₀ 3 + fiveW a b p₀ q₀ 4 := by
    simp only [fiveW]; simp [hQ]
    calc q₀ = q₀ + (p₀ + p₀) + (b q₀ + b q₀) := by rw [c2, c2, add_zero, add_zero]
      _ = _ := by abel
  have e2 : b q₀ = fiveW a b p₀ q₀ 2 + fiveW a b p₀ q₀ 4 := by
    simp only [fiveW]; simp [hQ]
    calc b q₀ = b q₀ + (p₀ + p₀) + (q₀ + q₀) := by rw [c2, c2, add_zero, add_zero]
      _ = _ := by abel
  have e3 : b (b q₀) = fiveW a b p₀ q₀ 2 + fiveW a b p₀ q₀ 3 := by
    simp only [fiveW]; simp [hQ]
    calc q₀ + b q₀ = q₀ + b q₀ + (p₀ + p₀) := by rw [c2, add_zero]
      _ = _ := by abel
  rcases hc with h0 | h0 | h0 | h0
  · rw [h0]; exact zero_mem _
  · rw [h0]; have := add_mem (m 3) (m 4); rwa [← e1] at this
  · rw [h0]; have := add_mem (m 2) (m 4); rwa [← e2] at this
  · rw [h0]; have := add_mem (m 2) (m 3); rwa [← e3] at this

theorem A5Data.fiveVec (h : PairHyp B a b) (d : A5Data B a b p₀ q₀) :
    FiveVec a b (fiveW a b p₀ q₀) := by
  have hP := apply_sq_of_mem h.ha d.hp₀
  have hQ := apply_sq_of_mem h.hb d.hq₀
  have haq := d.a_q₀ h
  have hbp := d.b_p₀ h
  have hca := h.ha.apply_cube p₀
  have hcb := h.hb.apply_cube q₀
  refine ⟨d.five_inj h, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, d.span_a h, d.span_b h⟩
  · simp [fiveW, map_add, haq]
  · simp [fiveW, map_add, haq, hca]
  · simp [fiveW, map_add, haq]
  · simpa [fiveW] using d.a_w3 h
  · simpa [fiveW] using d.a_w4 h
  · simpa [fiveW] using d.b_w0 h
  · simpa [fiveW] using d.b_w1 h
  · simp [fiveW, map_add, hbp]
  · simp [fiveW, map_add, hbp]
  · simp [fiveW, map_add, hbp, hcb]

end CFSG.LocalAnalysis.UniquenessCase.UCK.PairSpLem
