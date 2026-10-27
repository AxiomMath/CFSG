module

public import CFSG.Quasithin.Vol2.Ch3E213MG41W

public section

namespace CFSG.Quasithin.Ch3E213M

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  (antiSp glMat minorJ minorJ_apply uElt uMat glMat_uElt antiSp_ext)

variable {k : Type} [Field k]

theorem spBil_apply (x y : Fin 4 → k) :
    spBil x y = x 0 * y 3 + x 1 * y 2 + x 2 * y 1 + x 3 * y 0 := by
  simp [spBil, Matrix.toBilin'_apply, Fin.sum_univ_four, minorJ_apply]

theorem spBil_comm (x y : Fin 4 → k) : spBil x y = spBil y x := by
  rw [spBil_apply, spBil_apply]
  ring

theorem natLin_apply (g : antiSp k) (v : Fin 4 → k) : natLin g v = natAct g v :=
  Matrix.toLin'_apply _ _

section CharTwo

variable [CharP k 2]

theorem natAct_zl (a : k) (v : Fin 4 → k) :
    natAct (uElt 0 0 a 0) v = v + (a * v 3) • Pi.single 0 1 := by
  ext i
  fin_cases i <;> simp [natAct, glMat_uElt, uMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem natAct_zs (b : k) (v : Fin 4 → k) :
    natAct (uElt 0 b 0 0) v = v + (b * v 2) • Pi.single 0 1 + (b * v 3) • Pi.single 1 1 := by
  ext i
  fin_cases i <;> simp [natAct, glMat_uElt, uMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem natAct_zl_three (a : k) (v : Fin 4 → k) : natAct (uElt 0 0 a 0) v 3 = v 3 := by
  simp [natAct_zl]

theorem natAct_zs_three (b : k) (v : Fin 4 → k) : natAct (uElt 0 b 0 0) v 3 = v 3 := by
  simp [natAct_zs]

theorem isTransvection_zl {a : k} (ha : a ≠ 0) : IsTransvection (uElt 0 0 a 0) := by
  refine ⟨fun h => ?_, ?_⟩
  · have h1 := congrArg (fun g : antiSp k => glMat (g : GL (Fin 4) k) 0 3) h
    simp [glMat_uElt, uMat] at h1
    exact ha h1
  · have hc : commSpace (uElt 0 0 a 0) = Submodule.span k {(Pi.single 0 1 : Fin 4 → k)} := by
      apply le_antisymm
      · rintro _ ⟨v, rfl⟩
        have e : Matrix.toLin' (glMat ((uElt 0 0 a 0 : antiSp k) : GL (Fin 4) k) - 1) v =
            (a * v 3) • Pi.single 0 1 := by
          rw [Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec]
          have := natAct_zl a v
          simp only [natAct] at this
          rw [this, add_sub_cancel_left]
        rw [e]
        exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        refine ⟨a⁻¹ • Pi.single 3 1, ?_⟩
        rw [Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec]
        have := natAct_zl a (a⁻¹ • Pi.single 3 1)
        simp only [natAct] at this
        rw [this, add_sub_cancel_left]
        simp [ha]
    rw [hc, finrank_span_singleton]
    exact Pi.single_ne_zero_iff.mpr one_ne_zero

theorem not_g41Orth {G₀ : Subgroup (antiSp k)} {a b : k} (ha : a ≠ 0) (hb : b ≠ 0)
    (hl : uElt 0 0 a 0 ∈ G₀) (hs : uElt 0 b 0 0 ∈ G₀) : ¬ G41OrthW G₀ := by
  rintro ⟨Q, hQ, hG⟩
  have hpol : ∀ x y, Q (x + y) = Q x + Q y + spBil x y := fun x y => by
    rw [← hQ]
    unfold QuadraticMap.polar
    ring
  have hQl := hG _ hl (Pi.single 3 1)
  have hQs := hG _ hs (Pi.single 2 1)
  rw [natAct_zl, hpol, QuadraticMap.map_smul, spBil_apply] at hQl
  rw [natAct_zs, hpol, hpol, QuadraticMap.map_smul, QuadraticMap.map_smul, spBil_apply,
    spBil_apply] at hQs
  simp at hQl hQs
  have h0 : Q (Pi.single 0 1) = 0 := by
    rcases hQs with h | h
    · exact absurd h hb
    · exact h
  rw [h0, mul_zero, add_zero] at hQl
  simp at hQl
  exact ha hQl

omit [CharP k 2] in
theorem exists_ne_zero_three_eq_zero {X : Submodule k (Fin 4 → k)}
    (hX : Module.finrank k X = 2) : ∃ v ∈ X, v ≠ 0 ∧ v 3 = 0 := by
  let φ : X →ₗ[k] k := (LinearMap.proj 3).comp X.subtype
  have hker : LinearMap.ker φ ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by rw [hX, Module.finrank_self]; norm_num)
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨x, x.2, fun h => hx0 (Subtype.ext h), hx⟩

theorem zs_not_fix {b : k} (hb : b ≠ 0) {X : Submodule k (Fin 4 → k)}
    (hX : Module.finrank k X = 2) (hnd : ∀ v ∈ X, (∀ w ∈ X, spBil w v = 0) → v = 0)
    (hfix : X.map (natLin (uElt 0 b 0 0)) = X) : False := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hx : ∃ x ∈ X, x 2 ≠ 0 ∨ x 3 ≠ 0 := by
    by_contra hc
    push Not at hc
    have hbot : X = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro v hv
      exact hnd v hv fun w hw => by
        rw [spBil_apply, (hc w hw).1, (hc w hw).2, (hc v hv).1, (hc v hv).2]
        ring
    rw [hbot, finrank_bot] at hX
    norm_num at hX
  obtain ⟨x, hxX, hx23⟩ := hx
  set y : Fin 4 → k := (b * x 2) • Pi.single 0 1 + (b * x 3) • Pi.single 1 1 with hydef
  have hy : y ∈ X := by
    have h1 : natAct (uElt 0 b 0 0) x ∈ X := by
      rw [← hfix, ← natLin_apply]
      exact Submodule.mem_map_of_mem hxX
    rw [natAct_zs] at h1
    have h3 := X.sub_mem h1 hxX
    rwa [add_assoc, add_sub_cancel_left] at h3
  have hy0 : y ≠ 0 := by
    intro h
    have e0 := congrFun h 0
    have e1 := congrFun h 1
    simp [hydef] at e0 e1
    rcases hx23 with h | h
    · exact h (e0.resolve_left hb)
    · exact h (e1.resolve_left hb)
  have hxy : spBil x y = 0 := by
    rw [spBil_apply]
    simp [hydef]
    linear_combination b * x 2 * x 3 * h2
  have hyy : spBil y y = 0 := by
    rw [spBil_apply]
    simp [hydef]
  have hli : LinearIndependent k ![x, y] := by
    rw [LinearIndependent.pair_iff]
    intro p q hpq
    have e2 := congrFun hpq 2
    have e3 := congrFun hpq 3
    simp [hydef] at e2 e3
    have hp : p = 0 := by
      rcases hx23 with h | h
      · exact e2.resolve_right h
      · exact e3.resolve_right h
    subst hp
    rw [zero_smul, zero_add] at hpq
    exact ⟨rfl, (smul_eq_zero.1 hpq).resolve_right hy0⟩
  have hspan : Submodule.span k (Set.range ![x, y]) = X := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le, Set.range_subset_iff]
      intro i
      fin_cases i
      exacts [hxX, hy]
    · rw [hX, finrank_span_eq_card hli, Fintype.card_fin]
  apply hy0
  apply hnd y hy
  intro w hw
  rw [← hspan, Submodule.mem_span_range_iff_exists_fun] at hw
  obtain ⟨c, rfl⟩ := hw
  simp [Fin.sum_univ_two, hxy, hyy]

end CharTwo

end CFSG.Quasithin.Ch3E213M
