module

public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveModelSpan

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal

set_option backward.isDefEq.respectTransparency false

theorem fiveFormVec_smul' (k : ℕ) (ε : Bool) (a : ZMod 5)
    (y : Fin (k + 1) → ZMod 5) :
    fiveFormVec k ε (a • y) = a • fiveFormVec k ε y := by
  funext j
  simp only [fiveFormVec, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

theorem fiveForm_smul_smul (k : ℕ) (ε : Bool) (a b : ZMod 5)
    (x y : Fin (k + 1) → ZMod 5) :
    fiveForm k ε (a • x) (b • y) = a * b * fiveForm k ε x y := by
  rw [fiveForm_eq_dotProduct, fiveFormVec_smul', smul_dotProduct, dotProduct_smul,
    smul_eq_mul, smul_eq_mul, ← fiveForm_eq_dotProduct]
  ring

theorem fiveForm_self_add (k : ℕ) (ε : Bool) (x y : Fin (k + 1) → ZMod 5) :
    fiveForm k ε (x + y) (x + y) =
      fiveForm k ε x x + fiveForm k ε y y + 2 * fiveForm k ε x y := by
  calc fiveForm k ε (x + y) (x + y) = fiveQ k ε (x + y) := (fiveQ_apply k ε (x + y)).symm
    _ = fiveQ k ε x + fiveQ k ε y + polar (fiveQ k ε) x y :=
        QuadraticMap.map_add (fiveQ k ε) x y
    _ = fiveForm k ε x x + fiveForm k ε y y + 2 * fiveForm k ε x y := by
        rw [fiveQ_apply, fiveQ_apply, fiveQ_polar]

theorem isSquare_neg_iff_zmod5 {a : ZMod 5} : IsSquare (-a) ↔ IsSquare a := by
  fin_cases a <;> decide

@[expose] def centerSignSet (k : ℕ) (ε π : Bool) : Set (Fin (k + 1) → ZMod 5) :=
  {v | fiveForm k ε v v ≠ 0 ∧ (IsSquare (fiveForm k ε v v) ↔ π = true)}

theorem centerSignSet_mem (k : ℕ) (ε π : Bool) (v : Fin (k + 1) → ZMod 5) :
    v ∈ centerSignSet k ε π ↔
      fiveForm k ε v v ≠ 0 ∧ (IsSquare (fiveForm k ε v v) ↔ π = true) := by
  simp only [centerSignSet, Set.mem_setOf_eq]

theorem centerBasis_mem_span (k : ℕ) (ε π : Bool) (hk : 4 ≤ k) (i : Fin (k + 1)) :
    Pi.single i (1 : ZMod 5) ∈ Submodule.span (ZMod 5) (centerSignSet k ε π) := by
  have hcard : 1 < k := by omega
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
  · by_cases hπ : π = true
    · refine Submodule.subset_span ?_
      rw [centerSignSet_mem]
      refine ⟨?_, ?_⟩
      · rw [fiveForm_single_self_eq_fiveWeight k ε i'.castSucc, fiveWeight_castSucc k ε i']; decide
      · rw [fiveForm_single_self_eq_fiveWeight k ε i'.castSucc, fiveWeight_castSucc k ε i', hπ]; decide
    · obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card (α := Fin k)
        (by rw [Fintype.card_fin]; omega) i'
      have hij : (i'.castSucc : Fin (k + 1)) ≠ j.castSucc :=
        fun h => hj (Fin.castSucc_injective k h.symm)
      have hπf : π = false := by cases π <;> simp_all
      have h1 : Pi.single i'.castSucc (1 : ZMod 5) + Pi.single j.castSucc 1 ∈
          centerSignSet k ε π := by
        rw [centerSignSet_mem]
        refine ⟨?_, ?_⟩
        · rw [fiveForm_sq_eq_two k ε hij, fiveWeight_castSucc k ε i',
            fiveWeight_castSucc k ε j]; decide
        · rw [fiveForm_sq_eq_two k ε hij, fiveWeight_castSucc k ε i',
            fiveWeight_castSucc k ε j, hπf]; decide
      have h2 : Pi.single i'.castSucc (1 : ZMod 5) - Pi.single j.castSucc 1 ∈
          centerSignSet k ε π := by
        rw [centerSignSet_mem]
        refine ⟨?_, ?_⟩
        · rw [fiveForm_sq_sub k ε hij, fiveWeight_castSucc k ε i',
            fiveWeight_castSucc k ε j]; decide
        · rw [fiveForm_sq_sub k ε hij, fiveWeight_castSucc k ε i',
            fiveWeight_castSucc k ε j, hπf]; decide
      have hsum : (Pi.single i'.castSucc (1 : ZMod 5) + Pi.single j.castSucc 1) +
          (Pi.single i'.castSucc 1 - Pi.single j.castSucc 1) =
          (2 : ZMod 5) • Pi.single i'.castSucc 1 := by
        module
      have hmem : (2 : ZMod 5) • Pi.single i'.castSucc (1 : ZMod 5) ∈
          Submodule.span (ZMod 5) (centerSignSet k ε π) := by
        rw [← hsum]
        exact Submodule.add_mem _ (Submodule.subset_span h1) (Submodule.subset_span h2)
      have heq : Pi.single i'.castSucc (1 : ZMod 5) =
          ((2 : ZMod 5)⁻¹) • ((2 : ZMod 5) • Pi.single i'.castSucc 1) := by
        rw [smul_smul, inv_mul_cancel₀ (by decide : (2 : ZMod 5) ≠ 0), one_smul]
      rw [heq]
      exact Submodule.smul_mem _ _ hmem
  · by_cases hε : ε = true
    · by_cases hπ : π = true
      · refine Submodule.subset_span ?_
        rw [centerSignSet_mem]
        refine ⟨?_, ?_⟩
        · rw [fiveForm_single_self_eq_fiveWeight k ε (Fin.last k), fiveWeight_last k ε, hε]; decide
        · rw [fiveForm_single_self_eq_fiveWeight k ε (Fin.last k), fiveWeight_last k ε, hε, hπ]; decide
      · have hlast0 : Fin.last k ≠ (0 : Fin (k + 1)) := by
          intro h; have := congrArg Fin.val h; simp at this; omega
        have hπf : π = false := by cases π <;> simp_all
        have h1 : Pi.single (Fin.last k) (1 : ZMod 5) +
            (2 : ZMod 5) • Pi.single (0 : Fin (k + 1)) 1 ∈ centerSignSet k ε π := by
          rw [centerSignSet_mem]
          refine ⟨?_, ?_⟩
          · rw [fiveForm_sq_add_smul k ε hlast0 (2 : ZMod 5),
              fiveWeight_last k ε, fiveWeight_zero k ε (by omega), hε]; decide
          · rw [fiveForm_sq_add_smul k ε hlast0 (2 : ZMod 5),
              fiveWeight_last k ε, fiveWeight_zero k ε (by omega), hε, hπf]; decide
        have h2 : Pi.single (Fin.last k) (1 : ZMod 5) -
            (2 : ZMod 5) • Pi.single (0 : Fin (k + 1)) 1 ∈ centerSignSet k ε π := by
          have hneg : Pi.single (Fin.last k) (1 : ZMod 5) -
              (2 : ZMod 5) • Pi.single (0 : Fin (k + 1)) 1 =
              Pi.single (Fin.last k) 1 + (-2 : ZMod 5) • Pi.single (0 : Fin (k + 1)) 1 := by
            rw [neg_smul]
            abel
          rw [hneg, centerSignSet_mem]
          refine ⟨?_, ?_⟩
          · rw [fiveForm_sq_add_smul k ε hlast0 (-2 : ZMod 5),
              fiveWeight_last k ε, fiveWeight_zero k ε (by omega), hε]; decide
          · rw [fiveForm_sq_add_smul k ε hlast0 (-2 : ZMod 5),
              fiveWeight_last k ε, fiveWeight_zero k ε (by omega), hε, hπf]; decide
        have hsum : (Pi.single (Fin.last k) (1 : ZMod 5) +
            (2 : ZMod 5) • Pi.single (0 : Fin (k + 1)) 1) +
            (Pi.single (Fin.last k) 1 - (2 : ZMod 5) • Pi.single (0 : Fin (k + 1)) 1) =
            (2 : ZMod 5) • Pi.single (Fin.last k) 1 := by
          module
        have hmem : (2 : ZMod 5) • Pi.single (Fin.last k) (1 : ZMod 5) ∈
            Submodule.span (ZMod 5) (centerSignSet k ε π) := by
          rw [← hsum]
          exact Submodule.add_mem _ (Submodule.subset_span h1) (Submodule.subset_span h2)
        have heq : Pi.single (Fin.last k) (1 : ZMod 5) =
            ((2 : ZMod 5)⁻¹) • ((2 : ZMod 5) • Pi.single (Fin.last k) 1) := by
          rw [smul_smul, inv_mul_cancel₀ (by decide : (2 : ZMod 5) ≠ 0), one_smul]
        rw [heq]
        exact Submodule.smul_mem _ _ hmem
    · have hεf : ε = false := by cases ε <;> simp_all
      by_cases hπ : π = true
      · have hlast0 : Fin.last k ≠ (0 : Fin (k + 1)) := by
          intro h; have := congrArg Fin.val h; simp at this; omega
        have h1 : Pi.single (Fin.last k) (1 : ZMod 5) +
            Pi.single (0 : Fin (k + 1)) 1 ∈ centerSignSet k ε π := by
          rw [show Pi.single (Fin.last k) (1 : ZMod 5) + Pi.single (0 : Fin (k + 1)) 1 =
                Pi.single (Fin.last k) 1 + (1 : ZMod 5) • Pi.single (0 : Fin (k + 1)) 1 by
              rw [one_smul]]
          rw [centerSignSet_mem]
          refine ⟨?_, ?_⟩
          · rw [fiveForm_sq_add_smul k ε hlast0 (1 : ZMod 5),
              fiveWeight_last k ε, fiveWeight_zero k ε (by omega), hεf]; decide
          · rw [fiveForm_sq_add_smul k ε hlast0 (1 : ZMod 5),
              fiveWeight_last k ε, fiveWeight_zero k ε (by omega), hεf, hπ]; decide
        have h2 : Pi.single (Fin.last k) (1 : ZMod 5) -
            Pi.single (0 : Fin (k + 1)) 1 ∈ centerSignSet k ε π := by
          have hneg : Pi.single (Fin.last k) (1 : ZMod 5) - Pi.single (0 : Fin (k + 1)) 1 =
              Pi.single (Fin.last k) 1 + (-1 : ZMod 5) • Pi.single (0 : Fin (k + 1)) 1 := by
            rw [neg_smul, one_smul]
            abel
          rw [hneg, centerSignSet_mem]
          refine ⟨?_, ?_⟩
          · rw [fiveForm_sq_add_smul k ε hlast0 (-1 : ZMod 5),
              fiveWeight_last k ε, fiveWeight_zero k ε (by omega), hεf]; decide
          · rw [fiveForm_sq_add_smul k ε hlast0 (-1 : ZMod 5),
              fiveWeight_last k ε, fiveWeight_zero k ε (by omega), hεf, hπ]; decide
        have hsum : (Pi.single (Fin.last k) (1 : ZMod 5) +
            Pi.single (0 : Fin (k + 1)) 1) +
            (Pi.single (Fin.last k) 1 - Pi.single (0 : Fin (k + 1)) 1) =
            (2 : ZMod 5) • Pi.single (Fin.last k) 1 := by
          module
        have hmem : (2 : ZMod 5) • Pi.single (Fin.last k) (1 : ZMod 5) ∈
            Submodule.span (ZMod 5) (centerSignSet k ε π) := by
          rw [← hsum]
          exact Submodule.add_mem _ (Submodule.subset_span h1) (Submodule.subset_span h2)
        have heq : Pi.single (Fin.last k) (1 : ZMod 5) =
            ((2 : ZMod 5)⁻¹) • ((2 : ZMod 5) • Pi.single (Fin.last k) 1) := by
          rw [smul_smul, inv_mul_cancel₀ (by decide : (2 : ZMod 5) ≠ 0), one_smul]
        rw [heq]
        exact Submodule.smul_mem _ _ hmem
      · refine Submodule.subset_span ?_
        rw [centerSignSet_mem]
        refine ⟨?_, ?_⟩
        · rw [fiveForm_single_self_eq_fiveWeight k ε (Fin.last k), fiveWeight_last k ε, hεf]; decide
        · rw [fiveForm_single_self_eq_fiveWeight k ε (Fin.last k), fiveWeight_last k ε, hεf,
            show π = false from by cases π <;> simp_all]; decide

theorem centerSignSet_span (k : ℕ) (ε π : Bool) (hk : 4 ≤ k) :
    Submodule.span (ZMod 5) (centerSignSet k ε π) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun (ZMod 5) (Fin (k + 1))).span_eq]
  apply Submodule.span_le.mpr
  rintro x ⟨i, rfl⟩
  rw [Pi.basisFun_apply]
  exact centerBasis_mem_span k ε π hk i

theorem eq_one_or_eq_neg_one_of_mem_center_fiveReflectionGroup (k : ℕ) (ε π : Bool) (hk : 4 ≤ k)
    {g : GL (Fin (k + 1)) (ZMod 5)}
    (hg : g ∈ fiveReflectionGroup k ε π)
    (hcen : ∀ r ∈ fiveReflections k ε π, g * r = r * g) :
    g = 1 ∨ g = -1 := by
  set gL : (Fin (k + 1) → ZMod 5) ≃ₗ[ZMod 5] (Fin (k + 1) → ZMod 5) :=
    fiveGLIso k g with hgL
  have hiso : ∀ x y, fiveForm k ε (gL x) (gL y) = fiveForm k ε x y := by
    intro x y
    rw [hgL, fiveGLIso_apply, fiveGLIso_apply]
    exact fiveForm_mulVec_of_mem hg x y
  have hstep1 : ∀ v ∈ centerSignSet k ε π, ∃ a : ZMod 5, gL v = a • v := by
    intro v hv
    obtain ⟨hvQ, hvπ⟩ := (centerSignSet_mem k ε π v).mp hv
    have hrefl_mem : fiveReflOf k ε v ∈ fiveReflections k ε π := fiveReflOf_mem hvQ hvπ
    have hcommL : gL * fiveReflO k ε v = fiveReflO k ε v * gL := by
      rw [hgL]
      have h := congrArg (fun z : GL (Fin (k + 1)) (ZMod 5) => fiveGLIso k z)
        (hcen (fiveReflOf k ε v) hrefl_mem)
      simpa only [map_mul, fiveGLIso_fiveReflOf] using h
    have hrefl_self : fiveReflO k ε v v = -v := by
      have hvQ' : fiveQ k ε v ≠ 0 := by rwa [fiveQ_apply]
      letI : Invertible (fiveQ k ε v) := invertibleOfNonzero hvQ'
      rw [fiveReflO, reflect_eq_reflection]
      exact TauCeti.QuadraticMap.reflection_apply_self (fiveQ k ε) v
    have hxg : fiveReflO k ε v (gL v) = -(gL v) := by
      calc fiveReflO k ε v (gL v) = (fiveReflO k ε v * gL) v := rfl
        _ = (gL * fiveReflO k ε v) v := by rw [hcommL]
        _ = gL (fiveReflO k ε v v) := rfl
        _ = gL (-v) := by rw [hrefl_self]
        _ = -(gL v) := map_neg gL v
    have hvQ' : fiveQ k ε v ≠ 0 := by rwa [fiveQ_apply]
    letI : Invertible (fiveQ k ε v) := invertibleOfNonzero hvQ'
    let c : ZMod 5 := ⅟(fiveQ k ε v) * polar (fiveQ k ε) v (gL v)
    have hxg' : gL v - c • v = -(gL v) := by
      rw [fiveReflO, reflect_eq_reflection, TauCeti.QuadraticMap.reflection_apply] at hxg
      exact hxg
    have h4 : gL v = -(gL v) + c • v := (sub_eq_iff_eq_add).mp hxg'
    have h2x : gL v + gL v = c • v := by
      nth_rewrite 1 [h4]
      abel
    refine ⟨(2 : ZMod 5)⁻¹ * c, ?_⟩
    have h2 : (2 : ZMod 5) • (gL v) = c • v := by
      rw [two_smul]
      exact h2x
    calc gL v = (2 : ZMod 5)⁻¹ • ((2 : ZMod 5) • (gL v)) := by
          rw [smul_smul, inv_mul_cancel₀ (by decide : (2 : ZMod 5) ≠ 0), one_smul]
      _ = (2 : ZMod 5)⁻¹ • (c • v) := by rw [h2]
      _ = ((2 : ZMod 5)⁻¹ * c) • v := by rw [smul_smul]
  have hstep1' : ∀ v ∈ centerSignSet k ε π,
      ∃ a : ZMod 5, gL v = a • v ∧ a * a = 1 := by
    intro v hv
    obtain ⟨a, ha⟩ := hstep1 v hv
    refine ⟨a, ha, ?_⟩
    have hvQ : fiveForm k ε v v ≠ 0 := (centerSignSet_mem k ε π v).mp hv |>.1
    have h := hiso v v
    rw [ha] at h
    rw [fiveForm_smul_smul] at h
    have h2 : (a * a) * fiveForm k ε v v = 1 * fiveForm k ε v v := by
      rw [one_mul]
      exact h
    exact mul_right_cancel₀ hvQ h2
  have hstep2 : ∀ v ∈ centerSignSet k ε π, gL (gL v) = v := by
    intro v hv
    obtain ⟨a, ha, ha2⟩ := hstep1' v hv
    calc gL (gL v) = gL (a • v) := by rw [ha]
      _ = a • gL v := map_smul gL a v
      _ = a • (a • v) := by rw [ha]
      _ = (a * a) • v := by rw [smul_smul]
      _ = 1 • v := congrArg (fun z : ZMod 5 => z • v) ha2
      _ = v := one_smul _ _
  have hgL2 : gL * gL = 1 := by
    apply LinearEquiv.ext
    intro x
    show (gL * gL) x = x
    let Fix : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5) :=
      { carrier := {x | (gL * gL) x = x}
        zero_mem' := by show (gL * gL) 0 = 0; simp
        add_mem' := by
          intro x y hx hy
          have hx' : (gL * gL) x = x := hx
          have hy' : (gL * gL) y = y := hy
          show (gL * gL) (x + y) = x + y
          simp only [map_add, hx', hy']
        smul_mem' := by
          intro c x hx
          have hx' : (gL * gL) x = x := hx
          show (gL * gL) (c • x) = c • x
          simp only [map_smul, hx'] }
    have hFix : Fix = ⊤ := by
      rw [eq_top_iff, ← centerSignSet_span k ε π hk]
      exact Submodule.span_le.mpr (fun v hv => hstep2 v hv)
    have : x ∈ Fix := by rw [hFix]; trivial
    exact this
  have hgL2app : ∀ x, gL (gL x) = x := by
    intro x
    have := congrArg
      (fun e : (Fin (k + 1) → ZMod 5) ≃ₗ[ZMod 5] (Fin (k + 1) → ZMod 5) => e x) hgL2
    simpa [LinearEquiv.mul_apply] using this
  let Vp : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5) :=
    { carrier := {x | gL x = x}
      zero_mem' := by show gL 0 = 0; simp
      add_mem' := by
        intro x y hx hy
        show gL (x + y) = x + y
        rw [map_add, hx, hy]
      smul_mem' := by
        intro c x hx
        show gL (c • x) = c • x
        rw [map_smul, hx] }
  let Vm : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5) :=
    { carrier := {x | gL x = -x}
      zero_mem' := by show gL 0 = -0; simp
      add_mem' := by
        intro x y hx hy
        show gL (x + y) = -(x + y)
        rw [map_add, hx, hy]
        abel
      smul_mem' := by
        intro c x hx
        show gL (c • x) = -(c • x)
        rw [map_smul, hx]
        module }
  have hmemVp : ∀ x, x ∈ Vp ↔ gL x = x := fun x => Iff.rfl
  have hmemVm : ∀ x, x ∈ Vm ↔ gL x = -x := fun x => Iff.rfl
  have hsup : Vp ⊔ Vm = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hp : (2 : ZMod 5)⁻¹ • (x + gL x) ∈ Vp := by
      rw [hmemVp]
      show gL ((2 : ZMod 5)⁻¹ • (x + gL x)) = (2 : ZMod 5)⁻¹ • (x + gL x)
      rw [map_smul, map_add, hgL2app x]
      exact congrArg (fun z => (2 : ZMod 5)⁻¹ • z) (add_comm (gL x) x)
    have hm : (2 : ZMod 5)⁻¹ • (x - gL x) ∈ Vm := by
      rw [hmemVm]
      show gL ((2 : ZMod 5)⁻¹ • (x - gL x)) = -((2 : ZMod 5)⁻¹ • (x - gL x))
      rw [map_smul, map_sub, hgL2app x, smul_sub, smul_sub]
      abel
    have hsum : (2 : ZMod 5)⁻¹ • (x + gL x) + (2 : ZMod 5)⁻¹ • (x - gL x) = x := by
      rw [← smul_add]
      rw [show (x + gL x) + (x - gL x) = (2 : ZMod 5) • x by rw [two_smul]; abel]
      rw [smul_smul, inv_mul_cancel₀ (by decide : (2 : ZMod 5) ≠ 0), one_smul]
    rw [← hsum]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hp) (Submodule.mem_sup_right hm)
  have hinf : Vp ⊓ Vm = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [Submodule.mem_inf] at hx
    have h1 : gL x = x := (hmemVp x).mp hx.1
    have h2 : gL x = -x := (hmemVm x).mp hx.2
    have hxneg : x = -x := h1.symm.trans h2
    have h2x : (2 : ZMod 5) • x = 0 := by
      rw [two_smul]
      nth_rewrite 2 [hxneg]
      rw [add_neg_cancel]
    calc x = (2 : ZMod 5)⁻¹ • ((2 : ZMod 5) • x) := by
          rw [smul_smul, inv_mul_cancel₀ (by decide : (2 : ZMod 5) ≠ 0), one_smul]
      _ = 0 := by rw [h2x, smul_zero]
  haveI : Invertible (2 : ZMod 5) := invertibleOfNonzero (by decide : (2 : ZMod 5) ≠ 0)
  let B : LinearMap.BilinForm (ZMod 5) (Fin (k + 1) → ZMod 5) :=
    QuadraticMap.polarBilin (fiveQ k ε)
  have hB_apply : ∀ x y, B x y = polar (fiveQ k ε) x y := by
    intro x y
    exact QuadraticMap.polarBilin_apply_apply (fiveQ k ε) x y
  have hB : B.Nondegenerate := by
    change (QuadraticMap.polarBilin (fiveQ k ε)).Nondegenerate
    exact QuadraticMap.nondegenerate_polar_iff.mpr (fiveQ_nondegenerate k ε)
  have hBs : B.IsSymm := by
    rw [LinearMap.BilinForm.isSymm_def]
    intro x y
    rw [hB_apply, hB_apply]
    exact polar_comm (fiveQ k ε) x y
  have hgO : gL ∈ TauCeti.QuadraticMap.orthogonalGroup (fiveQ k ε) := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro x
    rw [fiveQ_apply, fiveQ_apply]
    exact hiso x x
  have horth : ∀ u ∈ Vp, ∀ w ∈ Vm, fiveForm k ε u w = 0 := by
    intro u hu w hw
    have hu' : gL u = u := (hmemVp u).mp hu
    have hw' : gL w = -w := (hmemVm w).mp hw
    have hpol := polar_map_of_mem hgO u w
    rw [hu', hw', polar_neg_right] at hpol
    have hzero : polar (fiveQ k ε) u w = 0 := by
      have h2 : (2 : ZMod 5) • polar (fiveQ k ε) u w = 0 := by
        rw [two_smul]
        exact (eq_neg_iff_add_eq_zero).mp hpol.symm
      calc polar (fiveQ k ε) u w
          = (2 : ZMod 5)⁻¹ • ((2 : ZMod 5) • polar (fiveQ k ε) u w) := by
            rw [smul_smul, inv_mul_cancel₀ (by decide : (2 : ZMod 5) ≠ 0), one_smul]
        _ = 0 := by rw [h2, smul_zero]
    rw [fiveQ_polar] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left (by decide : (2 : ZMod 5) ≠ 0)
  have hB_Vp_Vm : ∀ u ∈ Vp, ∀ w ∈ Vm, B u w = 0 := by
    intro u hu w hw
    rw [hB_apply, fiveQ_polar, horth u hu w hw, mul_zero]
  have hdisjVp : Disjoint Vp (B.orthogonal Vp) := by
    rw [disjoint_iff_inf_le]
    intro x hx
    rw [Submodule.mem_inf] at hx
    rw [Submodule.mem_bot]
    apply hB.1 x
    intro y
    obtain ⟨p, hp, m, hm, rfl⟩ :=
      Submodule.mem_sup.mp (show y ∈ Vp ⊔ Vm from by rw [hsup]; trivial)
    rw [map_add, hBs.eq x p, hx.2 p hp, hB_Vp_Vm x hx.1 m hm, zero_add]
  have hdisjVm : Disjoint Vm (B.orthogonal Vm) := by
    rw [disjoint_iff_inf_le]
    intro x hx
    rw [Submodule.mem_inf] at hx
    rw [Submodule.mem_bot]
    apply hB.1 x
    intro y
    obtain ⟨p, hp, m, hm, rfl⟩ :=
      Submodule.mem_sup.mp (show y ∈ Vp ⊔ Vm from by rw [hsup]; trivial)
    rw [map_add, hBs.eq x m, hx.2 m hm, hBs.eq x p, hB_Vp_Vm p hp x hx.1, zero_add]
  have hBWp : (B.restrict Vp).Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal B hBs.isRefl hdisjVp
  have hBWm : (B.restrict Vm).Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal B hBs.isRefl hdisjVm
  have hSW : ∀ s ∈ centerSignSet k ε π, s ∈ Vp ∨ s ∈ Vm := by
    intro s hs
    obtain ⟨a, ha, ha2⟩ := hstep1' s hs
    have hax : a = 1 ∨ a = -1 := by
      have h : (a - 1) * (a + 1) = 0 := by
        rw [show (a - 1) * (a + 1) = a * a - 1 by ring, ha2, sub_self]
      rcases mul_eq_zero.mp h with h | h
      · left; exact sub_eq_zero.mp h
      · right; exact (eq_neg_iff_add_eq_zero).mpr h
    rcases hax with rfl | rfl
    · left; rw [hmemVp, ha]; simp
    · right; rw [hmemVm, ha]; simp
  have hfinV : Module.finrank (ZMod 5) (Fin (k + 1) → ZMod 5) = k + 1 := by
    rw [Module.finrank_pi, Fintype.card_fin]
  have hdimsum : Module.finrank (ZMod 5) Vp + Module.finrank (ZMod 5) Vm = k + 1 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq Vp Vm
    rw [hsup, hinf, finrank_top, finrank_bot, hfinV] at h
    omega
  have key : ∀ (W W' : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)),
      W' ≠ ⊥ → 2 ≤ Module.finrank (ZMod 5) W →
      (∀ s ∈ centerSignSet k ε π, s ∈ W ∨ s ∈ W') → W ⊓ W' = ⊥ →
      (∀ u ∈ W, ∀ w ∈ W', fiveForm k ε u w = 0) →
      (B.restrict W).Nondegenerate → False := by
    intro W W' hW'ne hWdim hSW' hdisj horth' hBW
    have hSinter : ∃ w ∈ centerSignSet k ε π, w ∈ W' := by
      by_contra hcon
      have hcon' : ∀ w, w ∈ centerSignSet k ε π → w ∉ W' := by
        intro w hw hw'
        exact hcon ⟨w, hw, hw'⟩
      have hSleW : centerSignSet k ε π ⊆ (W : Set (Fin (k + 1) → ZMod 5)) :=
        fun s hs => (hSW' s hs).resolve_right (hcon' s hs)
      have hWtop : W = ⊤ := by
        have hle : Submodule.span (ZMod 5) (centerSignSet k ε π) ≤ W :=
          Submodule.span_le.mpr hSleW
        rw [centerSignSet_span k ε π hk] at hle
        exact top_le_iff.mp hle
      have hW'bot : W' = ⊥ := by
        calc W' = ⊤ ⊓ W' := (top_inf_eq W').symm
          _ = W ⊓ W' := by rw [hWtop]
          _ = ⊥ := hdisj
      exact hW'ne hW'bot
    obtain ⟨w, hwS, hwW'⟩ := hSinter
    have hwQ : fiveForm k ε w w ≠ 0 := (centerSignSet_mem k ε π w).mp hwS |>.1
    have hw_ne : w ≠ 0 := by
      intro h0
      rw [h0] at hwQ
      simp [fiveForm] at hwQ
    have hcard5 : Fintype.card (ZMod 5) % 2 = 1 := by decide
    obtain ⟨v, hv⟩ := CFSG.LocalAnalysis.ComponentInitial.exists_bilin_self_eq
      (k := ZMod 5) (V := W) hcard5 hWdim hBW (hBs.restrict W)
      (2 * (-2 * fiveForm k ε w w))
    let u : Fin (k + 1) → ZMod 5 := v
    have huW : u ∈ W := v.2
    have hBuu : B u u = 2 * (-2 * fiveForm k ε w w) := by
      have h := hv
      rw [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply] at h
      exact h
    have huQ : fiveForm k ε u u = -2 * fiveForm k ε w w := by
      have h := hBuu
      rw [hB_apply, fiveQ_polar] at h
      exact mul_left_cancel₀ (by decide : (2 : ZMod 5) ≠ 0) h
    have hu_ne : u ≠ 0 := by
      intro h0
      have hz : -2 * fiveForm k ε w w = 0 := by rw [← huQ, h0]; simp [fiveForm]
      exact (mul_ne_zero (by decide : (-2 : ZMod 5) ≠ 0) hwQ) hz
    have hxQ : fiveForm k ε (u + w) (u + w) = -fiveForm k ε w w := by
      rw [fiveForm_self_add, horth' u huW w hwW', mul_zero, add_zero, huQ]
      ring
    have hxS : u + w ∈ centerSignSet k ε π := by
      rw [centerSignSet_mem]
      refine ⟨?_, ?_⟩
      · rw [hxQ]
        exact neg_ne_zero.mpr hwQ
      · rw [hxQ, isSquare_neg_iff_zmod5]
        exact (centerSignSet_mem k ε π w).mp hwS |>.2
    have huw_notW : u + w ∉ W := by
      intro h
      have hwW : w ∈ W := by
        have : (u + w) - u ∈ W := W.sub_mem h huW
        simpa using this
      have : w ∈ W ⊓ W' := ⟨hwW, hwW'⟩
      rw [hdisj, Submodule.mem_bot] at this
      exact hw_ne this
    have huw_notW' : u + w ∉ W' := by
      intro h
      have huW' : u ∈ W' := by
        have : (u + w) - w ∈ W' := W'.sub_mem h hwW'
        simpa using this
      have : u ∈ W ⊓ W' := ⟨huW, huW'⟩
      rw [hdisj, Submodule.mem_bot] at this
      exact hu_ne this
    rcases hSW' (u + w) hxS with h | h
    · exact huw_notW h
    · exact huw_notW' h
  have hVp_or : Vp = ⊥ ∨ Vm = ⊥ := by
    by_contra h
    rw [not_or] at h
    obtain ⟨hVpne, hVmne⟩ := h
    by_cases hdimVp : 2 ≤ Module.finrank (ZMod 5) Vp
    · exact key Vp Vm hVmne hdimVp hSW hinf horth hBWp
    · have hdimVp' : Module.finrank (ZMod 5) Vp ≤ 1 := by omega
      have hdimVm : 2 ≤ Module.finrank (ZMod 5) Vm := by omega
      exact key Vm Vp hVpne hdimVm (fun s hs => (hSW s hs).symm)
        (by rw [inf_comm]; exact hinf)
        (fun u hu w hw => by rw [fiveForm_comm]; exact horth w hw u hu) hBWm
  rcases hVp_or with hVp | hVm
  · right
    have hgL_pt : ∀ x, gL x = -x := by
      intro x
      have hx : x ∈ Vm := by
        have : x ∈ Vp ⊔ Vm := by rw [hsup]; trivial
        rw [hVp, bot_sup_eq] at this
        exact this
      exact (hmemVm x).mp hx
    have hmap : fiveGLIso k g = fiveGLIso k (-1 : GL (Fin (k + 1)) (ZMod 5)) := by
      rw [show fiveGLIso k g = gL from hgL.symm]
      apply LinearEquiv.ext
      intro x
      rw [hgL_pt x, fiveGLIso_apply]
      rw [show ((-1 : GL (Fin (k + 1)) (ZMod 5)) :
          Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) =
          -(1 : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) from rfl]
      rw [Matrix.neg_mulVec, Matrix.one_mulVec]
    exact (fiveGLIso k).injective hmap
  · left
    have hgL_eq : gL = 1 := by
      apply LinearEquiv.ext
      intro x
      have hx : x ∈ Vp := by
        have : x ∈ Vp ⊔ Vm := by rw [hsup]; trivial
        rw [hVm, sup_bot_eq] at this
        exact this
      have := (hmemVp x).mp hx
      simpa using this
    have hmap : fiveGLIso k g = fiveGLIso k 1 := by
      rw [show fiveGLIso k g = gL from hgL.symm, hgL_eq]
      exact (map_one (fiveGLIso k)).symm
    exact (fiveGLIso k).injective hmap

end CFSG.OddTranspositions.PartThree
