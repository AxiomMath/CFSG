module

public import CFSG.Quasithin.Vol2.Ch3E213MP6BA

public section

namespace CFSG.Quasithin.Ch3E213M

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp glMat uElt antiUnipotentCenter)

namespace P6B

variable {k : Type} [Field k] [CharP k 2]

section Vectors

variable {W : Submodule k (Fin 4 → k)}

omit [CharP k 2] in
theorem mem_of_smul_mem {a : k} (ha : a ≠ 0) {v : Fin 4 → k} (h : a • v ∈ W) : v ∈ W := by
  have := W.smul_mem a⁻¹ h
  rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at this

omit [CharP k 2] in
theorem natAct_sub_mem {g : antiSp k} (hg : ∀ w ∈ W, natAct g w ∈ W) {w : Fin 4 → k}
    (hw : w ∈ W) : natAct g w - w ∈ W :=
  W.sub_mem (hg w hw) hw

theorem mem_e01 {b c b' c' : k} (hdet : c * b' - c' * b ≠ 0)
    (hz : ∀ w ∈ W, natAct (uElt 0 b c 0 : antiSp k) w ∈ W)
    (hz' : ∀ w ∈ W, natAct (uElt 0 b' c' 0 : antiSp k) w ∈ W) {w : Fin 4 → k} (hw : w ∈ W)
    (h3 : w 3 ≠ 0) : ![1, 0, 0, 0] ∈ W ∧ ![0, 1, 0, 0] ∈ W := by
  have hp := natAct_sub_mem hz hw
  have hp' := natAct_sub_mem hz' hw
  rw [natAct_uElt_center] at hp hp'
  set A := c * w 3 + b * w 2
  set B := b * w 3
  set A' := c' * w 3 + b' * w 2
  set B' := b' * w 3
  have hd : A * B' - A' * B ≠ 0 := by
    have e : A * B' - A' * B = w 3 ^ 2 * (c * b' - c' * b) := by ring
    rw [e]
    exact mul_ne_zero (pow_ne_zero 2 h3) hdet
  have ep : ![w 0 + A, w 1 + B, w 2, w 3] - w = ![A, B, 0, 0] := by
    funext i; fin_cases i <;> simp
  have ep' : ![w 0 + A', w 1 + B', w 2, w 3] - w = ![A', B', 0, 0] := by
    funext i; fin_cases i <;> simp
  rw [ep] at hp
  rw [ep'] at hp'
  refine ⟨mem_of_smul_mem hd ?_, mem_of_smul_mem hd ?_⟩
  · have e : (A * B' - A' * B) • ![(1 : k), 0, 0, 0] =
        B' • ![A, B, 0, 0] - B • ![A', B', 0, 0] := by
      funext i; fin_cases i <;> simp <;> ring
    rw [e]
    exact W.sub_mem (W.smul_mem _ hp) (W.smul_mem _ hp')
  · have e : (A * B' - A' * B) • ![(0 : k), 1, 0, 0] =
        A • ![A', B', 0, 0] - A' • ![A, B, 0, 0] := by
      funext i; fin_cases i <;> simp
      ring
    rw [e]
    exact W.sub_mem (W.smul_mem _ hp') (W.smul_mem _ hp)

theorem mem_e0_of_three_eq_zero {b c : k} (hb : b ≠ 0)
    (hz : ∀ w ∈ W, natAct (uElt 0 b c 0 : antiSp k) w ∈ W) {w : Fin 4 → k} (hw : w ∈ W)
    (h3 : w 3 = 0) (h2 : w 2 ≠ 0) : ![1, 0, 0, 0] ∈ W := by
  have hp := natAct_sub_mem hz hw
  rw [natAct_uElt_center] at hp
  have e : ![w 0 + (c * w 3 + b * w 2), w 1 + b * w 3, w 2, w 3] - w =
      (b * w 2) • ![(1 : k), 0, 0, 0] := by
    funext i; fin_cases i <;> simp [h3]
  rw [e] at hp
  exact mem_of_smul_mem (mul_ne_zero hb h2) hp

theorem mem_e0 {b c b' c' : k} (hb : b ≠ 0) (hdet : c * b' - c' * b ≠ 0)
    (hz : ∀ w ∈ W, natAct (uElt 0 b c 0 : antiSp k) w ∈ W)
    (hz' : ∀ w ∈ W, natAct (uElt 0 b' c' 0 : antiSp k) w ∈ W) {w : Fin 4 → k} (hw : w ∈ W)
    (h : w 2 ≠ 0 ∨ w 3 ≠ 0) : ![1, 0, 0, 0] ∈ W := by
  by_cases h3 : w 3 = 0
  · exact mem_e0_of_three_eq_zero hb hz hw h3 (h.resolve_right (not_not.mpr h3))
  · exact (mem_e01 hdet hz hz' hw h3).1

end Vectors

omit [CharP k 2] in
theorem eq_zero_of_opp {g : antiSp k} (hg : IsOppStd g) {u : Fin 4 → k} (h2 : u 2 = 0)
    (h3 : u 3 = 0) (h2' : natAct g u 2 = 0) (h3' : natAct g u 3 = 0) : u = 0 := by
  obtain ⟨e2, e3⟩ := natAct_apply_two_three g h2 h3
  rw [e2] at h2'
  rw [e3] at h3'
  obtain ⟨-, hdet⟩ := hg
  set a := glMat (g : GL (Fin 4) k) 2 0
  set b := glMat (g : GL (Fin 4) k) 2 1
  set c := glMat (g : GL (Fin 4) k) 3 0
  set d := glMat (g : GL (Fin 4) k) 3 1
  have h0 : u 0 = 0 := by
    have e : (a * d - b * c) * u 0 = d * (a * u 0 + b * u 1) - b * (c * u 0 + d * u 1) := by ring
    rw [h2', h3', mul_zero, mul_zero, sub_zero] at e
    exact (mul_eq_zero.mp e).resolve_left hdet
  have h1 : u 1 = 0 := by
    have e : (a * d - b * c) * u 1 = a * (c * u 0 + d * u 1) - c * (a * u 0 + b * u 1) := by ring
    rw [h2', h3', mul_zero, mul_zero, sub_zero] at e
    exact (mul_eq_zero.mp e).resolve_left hdet
  funext i
  fin_cases i <;> simp [h0, h1, h2, h3]

omit [CharP k 2] in
theorem eq_top_of_opp {g : antiSp k} (hg : IsOppStd g) {W : Submodule k (Fin 4 → k)}
    (h0 : ![1, 0, 0, 0] ∈ W) (h1 : ![0, 1, 0, 0] ∈ W) (h0' : natAct g ![1, 0, 0, 0] ∈ W)
    (h1' : natAct g ![0, 1, 0, 0] ∈ W) : W = ⊤ := by
  rw [natAct_e0] at h0'
  rw [natAct_e1] at h1'
  obtain ⟨-, hdet⟩ := hg
  set M := glMat (g : GL (Fin 4) k)
  refine Submodule.eq_top_iff'.mpr fun v => ?_
  set D := M 2 0 * M 3 1 - M 2 1 * M 3 0
  set c := (v 2 * M 3 1 - v 3 * M 2 1) / D
  set d := (v 3 * M 2 0 - v 2 * M 3 0) / D
  have hc2 : c * M 2 0 + d * M 2 1 = v 2 := by
    simp only [c, d]
    field_simp
    ring
  have hc3 : c * M 3 0 + d * M 3 1 = v 3 := by
    simp only [c, d]
    field_simp
    ring
  have e : v = (v 0 - c * M 0 0 - d * M 0 1) • ![(1 : k), 0, 0, 0] +
      (v 1 - c * M 1 0 - d * M 1 1) • ![(0 : k), 1, 0, 0] + c • ![M 0 0, M 1 0, M 2 0, M 3 0] +
      d • ![M 0 1, M 1 1, M 2 1, M 3 1] := by
    funext i
    fin_cases i
    · simp; ring
    · simp; ring
    · simpa using hc2.symm
    · simpa using hc3.symm
  rw [e]
  exact W.add_mem (W.add_mem (W.add_mem (W.smul_mem _ h0) (W.smul_mem _ h1)) (W.smul_mem _ h0'))
    (W.smul_mem _ h1')

theorem eq_bot_or_top_of_invariant {g : antiSp k} (hg : IsOppStd g) {b c b' c' : k}
    (hb : b ≠ 0) (hdet : c * b' - c' * b ≠ 0) {W : Submodule k (Fin 4 → k)}
    (hz : ∀ w ∈ W, natAct (uElt 0 b c 0 : antiSp k) w ∈ W)
    (hz' : ∀ w ∈ W, natAct (uElt 0 b' c' 0 : antiSp k) w ∈ W)
    (hy : ∀ w ∈ W, natAct (g * uElt 0 b c 0 * g⁻¹ : antiSp k) w ∈ W)
    (hy' : ∀ w ∈ W, natAct (g * uElt 0 b' c' 0 * g⁻¹ : antiSp k) w ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  set W' := W.comap (natLin g) with hW'
  have hmem : ∀ u, u ∈ W' ↔ natAct g u ∈ W := fun u => by
    rw [hW', Submodule.mem_comap]
    rfl
  have hgg : ∀ u, natAct g (natAct g⁻¹ u) = u := fun u => by
    rw [← natAct_mul, mul_inv_cancel, natAct_one]
  have hconj : ∀ x : antiSp k, ∀ u, natAct (g * x * g⁻¹) (natAct g u) = natAct g (natAct x u) :=
    fun x u => by rw [natAct_mul, natAct_mul, ← natAct_mul g⁻¹ g, inv_mul_cancel, natAct_one]
  have hz₁ : ∀ u ∈ W', natAct (uElt 0 b c 0 : antiSp k) u ∈ W' := fun u hu => by
    rw [hmem] at hu ⊢
    rw [← hconj]
    exact hy _ hu
  have hz₂ : ∀ u ∈ W', natAct (uElt 0 b' c' 0 : antiSp k) u ∈ W' := fun u hu => by
    rw [hmem] at hu ⊢
    rw [← hconj]
    exact hy' _ hu
  have h30 := hg.1
  have hge0 : (natAct g ![1, 0, 0, 0]) 3 ≠ 0 := by
    rw [natAct_e0]
    simpa using h30
  have he0 : ![1, 0, 0, 0] ∈ W := by
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    by_cases hw23 : w 2 ≠ 0 ∨ w 3 ≠ 0
    · exact mem_e0 hb hdet hz hz' hw hw23
    · push Not at hw23
      have hu : natAct g⁻¹ w ∈ W' := by rw [hmem, hgg]; exact hw
      have hu23 : (natAct g⁻¹ w) 2 ≠ 0 ∨ (natAct g⁻¹ w) 3 ≠ 0 := by
        by_contra hc
        push Not at hc
        apply hw0
        have h0 := eq_zero_of_opp hg hc.1 hc.2 (by rw [hgg]; exact hw23.1)
          (by rw [hgg]; exact hw23.2)
        rw [← hgg w, h0]
        simp [natAct]
      have hg0 : natAct g ![1, 0, 0, 0] ∈ W := (hmem _).mp (mem_e0 hb hdet hz₁ hz₂ hu hu23)
      exact (mem_e01 hdet hz hz' hg0 hge0).1
  have hu0 : natAct g⁻¹ ![1, 0, 0, 0] ∈ W' := by rw [hmem, hgg]; exact he0
  have hu03 : (natAct g⁻¹ ![1, 0, 0, 0]) 3 ≠ 0 := by
    rw [natAct_e0, inv_three_zero]
    simpa using h30
  obtain ⟨hg0, hg1⟩ := mem_e01 hdet hz₁ hz₂ hu0 hu03
  rw [hmem] at hg0 hg1
  obtain ⟨-, he1⟩ := mem_e01 hdet hz hz' hg0 hge0
  exact eq_top_of_opp hg he0 he1 hg0 hg1

theorem exists_indep {W : Subgroup (antiSp k)} (hWc : W ≤ antiUnipotentCenter k)
    (hW : SpansCenter W) :
    ∃ b c b' c' : k, (uElt 0 b c 0 : antiSp k) ∈ W ∧ (uElt 0 b' c' 0 : antiSp k) ∈ W ∧ b ≠ 0 ∧
      c * b' - c' * b ≠ 0 := by
  obtain ⟨x, hxW, hxl⟩ := IsConcreteLE.not_le_iff_exists.mp (hW 1 0 (Or.inl one_ne_zero))
  obtain ⟨b, c, rfl⟩ := hWc hxW
  have hb : b ≠ 0 := by
    rintro rfl
    exact hxl ⟨c, by rw [mul_zero, mul_one]⟩
  obtain ⟨y, hyW, hyl⟩ := IsConcreteLE.not_le_iff_exists.mp (hW c b (Or.inr hb))
  obtain ⟨b', c', rfl⟩ := hWc hyW
  refine ⟨b, c, b', c', hxW, hyW, hb, fun hdet => hyl ⟨b' / b, ?_⟩⟩
  have e1 : b' / b * b = b' := div_mul_cancel₀ b' hb
  have e2 : b' / b * c = c' := by
    rw [div_mul_eq_mul_div, div_eq_iff hb]
    linear_combination hdet
  rw [e1, e2]

end P6B

open P6B in
theorem irrStatement_holds : IrrStatement := by
  intro k _ _ W g hWc hW hg U hU
  obtain ⟨b, c, b', c', hz, hz', hb, hdet⟩ := exists_indep hWc hW
  have hc : ∀ x ∈ W, g * x * g⁻¹ ∈ W.map (MulAut.conj g).toMonoidHom := fun x hx => ⟨x, hx, rfl⟩
  exact eq_bot_or_top_of_invariant hg hb hdet (hU _ (Subgroup.mem_sup_left hz))
    (hU _ (Subgroup.mem_sup_left hz')) (hU _ (Subgroup.mem_sup_right (hc _ hz)))
    (hU _ (Subgroup.mem_sup_right (hc _ hz')))

end CFSG.Quasithin.Ch3E213M
