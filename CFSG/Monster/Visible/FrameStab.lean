module

public import CFSG.Monster.FrameFiber
public import CFSG.Monster.Visible.SignFixed
public import CFSG.Monster.Visible.PermCompat

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Visible

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
  CFSG.Monster.Lifts Matrix

theorem mem_AutPerm_of_comp_mem {p : Equiv.Perm (Fin 24)} (h : ∀ x ∈ C, x ∘ ⇑p ∈ C) :
    p ∈ AutPerm := by
  intro x
  refine ⟨h x, fun hx => ?_⟩
  let f : C → C := fun y => ⟨(y : Fin 24 → ZMod 2) ∘ ⇑p, h y y.2⟩
  have hf : Function.Injective f := fun y y' hyy' => by
    apply Subtype.ext
    funext i
    have := congrFun (congrArg Subtype.val hyy') (p⁻¹ i)
    simpa [f] using this
  obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.1 hf) ⟨x ∘ ⇑p, hx⟩
  have hyx : (y : Fin 24 → ZMod 2) = x := by
    funext i
    have := congrFun (congrArg Subtype.val hy) (p⁻¹ i)
    simpa [f] using this
  rw [← hyx]
  exact y.2

theorem twoΩCls_eq_frameClass : twoΩCls = frameClass := rfl

theorem modTwoEnd_gO_frameClass (a : C) : modTwoEnd (gO a) frameClass = frameClass :=
  (modTwoEnd_gO_cls_eq_iff a twoΩ_mem).2 (maskVec_twoΩ_mem a.2)

theorem modTwoEnd_PO_frameClass (p : AutPerm) : modTwoEnd (PO p) frameClass = frameClass := by
  change modTwoEnd (PO p) (Submodule.Quotient.mk ⟨twoΩ, twoΩ_mem⟩) =
    Submodule.Quotient.mk ⟨twoΩ, twoΩ_mem⟩
  rw [modTwoEnd_mk]
  congr 1
  apply Subtype.ext
  apply ratVec_injective
  rw [ratVec_latHom, mat_PO, vecMul_Pmat]
  rfl

private theorem codeForm_eightE (i : Fin 24) :
    codeForm (ratVec ((8 : ℤ) • (Pi.single i 1 : Fin 24 → ℤ)))
      (ratVec ((8 : ℤ) • (Pi.single i 1 : Fin 24 → ℤ))) = 8 := by
  rw [codeForm_eq_dotProduct]
  have e : ratVec ((8 : ℤ) • (Pi.single i 1 : Fin 24 → ℤ)) = (8 : ℚ) • Pi.single i 1 := by
    funext k
    simp only [ratVec, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    split_ifs <;> norm_num
  rw [e, smul_dotProduct, dotProduct_smul, single_dotProduct, Pi.single_eq_same]
  norm_num

private theorem ratVec_eightE (i : Fin 24) :
    ratVec ((8 : ℤ) • (Pi.single i 1 : Fin 24 → ℤ)) = (8 : ℚ) • Pi.single i 1 := by
  funext k
  simp only [ratVec, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  split_ifs <;> norm_num

private theorem ratVec_neg_eightE (i : Fin 24) :
    ratVec (-((8 : ℤ) • (Pi.single i 1 : Fin 24 → ℤ))) = -((8 : ℚ) • Pi.single i 1) := by
  rw [ratVec_neg, ratVec_eightE]

theorem row_of_fix {g : latticeO} (hfix : modTwoEnd g frameClass = frameClass) (i : Fin 24) :
    ∃ j : Fin 24, mat g i = Pi.single j 1 ∨ mat g i = -Pi.single j 1 := by
  have hu : (8 : ℤ) • (Pi.single i 1 : Fin 24 → ℤ) ∈ codeLattice C :=
    smul_eight_mem_codeLattice _
  have hfu : (Submodule.Quotient.mk (⟨_, hu⟩ : codeLatticeSubgroup allOnes_mem_C) : L2) =
      frameClass := by
    obtain ⟨hv, hmk, -⟩ := (coordinate_frame_mod_two_fiber.2.2.2.1
      ((8 : ℤ) • (Pi.single i 1 : Fin 24 → ℤ))).2 ⟨i, Or.inl rfl⟩
    exact hmk
  have hcls : (Submodule.Quotient.mk (latHom g ⟨_, hu⟩) : L2) = frameClass := by
    rw [← modTwoEnd_mk, hfu, hfix]
  have hnorm : codeForm (fun k => (((latHom g ⟨_, hu⟩ : codeLatticeSubgroup allOnes_mem_C) :
      Fin 24 → ℤ) k : ℚ)) (fun k => (((latHom g ⟨_, hu⟩ : codeLatticeSubgroup allOnes_mem_C) :
      Fin 24 → ℤ) k : ℚ)) = 8 := by
    change codeForm (ratVec (latHom g ⟨_, hu⟩)) (ratVec (latHom g ⟨_, hu⟩)) = 8
    rw [ratVec_latHom, codeForm_vecMul_vecMul (mat_mul_transpose g)]
    exact codeForm_eightE i
  obtain ⟨j, hj⟩ := (coordinate_frame_mod_two_fiber.2.2.2.1
    ((latHom g ⟨_, hu⟩ : codeLatticeSubgroup allOnes_mem_C) : Fin 24 → ℤ)).1
      ⟨(latHom g ⟨_, hu⟩).2, hcls, hnorm⟩
  have hrat : ratVec (latHom g ⟨_, hu⟩) = (8 : ℚ) • mat g i := by
    rw [ratVec_latHom]
    change ratVec ((8 : ℤ) • (Pi.single i 1 : Fin 24 → ℤ)) ᵥ* mat g = _
    rw [ratVec_eightE, smul_vecMul, single_one_vecMul]
    rfl
  have h8 : (8 : ℚ) ≠ 0 := by norm_num
  refine ⟨j, ?_⟩
  rcases hj with h | h
  · left
    have e := congrArg ratVec h
    rw [hrat, ratVec_eightE] at e
    exact smul_right_injective _ h8 e
  · right
    have e := congrArg ratVec h
    rw [hrat, ratVec_neg_eightE, ← smul_neg] at e
    exact smul_right_injective _ h8 e

theorem exists_signedPerm_of_fix {g : latticeO} (hfix : modTwoEnd g frameClass = frameClass) :
    ∃ (σ : Fin 24 → Fin 24) (a : Fin 24 → ZMod 2),
      ∀ i, mat g i = sgn (a i) • Pi.single (σ i) 1 := by
  choose σ hσ using row_of_fix hfix
  refine ⟨σ, fun i => if mat g i = Pi.single (σ i) 1 then 0 else 1, fun i => ?_⟩
  dsimp only
  split_ifs with h
  · rw [h]
    simp [sgn]
  · rw [(hσ i).resolve_left h]
    simp [sgn]

theorem sgn_ne_zero' (t : ZMod 2) : sgn t ≠ 0 := by
  unfold sgn
  split_ifs <;> norm_num

private theorem sgn_cases (t : ZMod 2) : (t = 0 ∧ sgn t = 1) ∨ (t = 1 ∧ sgn t = -1) := by
  rcases (show ∀ t : ZMod 2, t = 0 ∨ t = 1 by decide) t with rfl | rfl
  · exact .inl ⟨rfl, by simp [sgn]⟩
  · exact .inr ⟨rfl, by simp [sgn]⟩

private theorem bitLift_inj : ∀ s t : ZMod 2, bitLift s = bitLift t → s = t := by decide

theorem injective_of_rows {M : Matrix (Fin 24) (Fin 24) ℚ} (hM : M * Mᵀ = 1)
    {σ : Fin 24 → Fin 24} {a : Fin 24 → ZMod 2}
    (hrow : ∀ i, M i = sgn (a i) • Pi.single (σ i) 1) : Function.Injective σ := by
  intro i i' h
  by_contra hne
  have h1 := congrFun (congrFun hM i) i'
  rw [mul_apply, one_apply_ne hne] at h1
  have h2 : ∑ k, M i k * Mᵀ k i' = sgn (a i) * sgn (a i') := by
    simp only [transpose_apply, hrow, Pi.smul_apply, smul_eq_mul, h, Pi.single_apply]
    rw [Finset.sum_eq_single (σ i')]
    · simp
    · intro k _ hk
      simp [hk]
    · simp
  rw [h2] at h1
  exact mul_ne_zero (sgn_ne_zero' _) (sgn_ne_zero' _) h1

theorem vecMul_rows_apply {M : Matrix (Fin 24) (Fin 24) ℚ} {σ : Fin 24 → Fin 24}
    (hσ : Function.Injective σ) {a : Fin 24 → ZMod 2}
    (hrow : ∀ i, M i = sgn (a i) • Pi.single (σ i) 1) (v : Fin 24 → ℚ) (i : Fin 24) :
    (v ᵥ* M) (σ i) = v i * sgn (a i) := by
  simp only [vecMul, dotProduct, hrow, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro l _ hl
    have : σ i ≠ σ l := fun h => hl (hσ h).symm
    simp [this]
  · simp

theorem perm_mem_AutPerm_of_rows {g : latticeO} {σ : Equiv.Perm (Fin 24)} {a : Fin 24 → ZMod 2}
    (hrow : ∀ i, mat g i = sgn (a i) • Pi.single (σ i) 1) : σ ∈ AutPerm := by
  rw [← AutPerm.inv_mem_iff]
  apply mem_AutPerm_of_comp_mem
  intro x hx
  have hu := two_bitLift_mem weight_mod_four' hx
  obtain ⟨hw, hwr⟩ := latVec_spec g hu
  obtain ⟨m, hm, d, hd, hmod, -⟩ := hw
  have hxd : ∀ i, x i = d (σ i) := by
    intro i
    have e := congrFun hwr (σ i)
    rw [vecMul_rows_apply σ.injective hrow] at e
    have hz : latVec (mat g) (fun i => 2 * bitLift (x i)) (σ i) = 2 * bitLift (x i) ∨
        latVec (mat g) (fun i => 2 * bitLift (x i)) (σ i) = -(2 * bitLift (x i)) := by
      rcases sgn_cases (a i) with ⟨-, hs⟩ | ⟨-, hs⟩ <;> rw [hs] at e
      · left
        have e' : ((latVec (mat g) (fun i => 2 * bitLift (x i)) (σ i) : ℤ) : ℚ) =
            ((2 * bitLift (x i) : ℤ) : ℚ) := by
          simpa [ratVec] using e
        exact_mod_cast e'
      · right
        have e' : ((latVec (mat g) (fun i => 2 * bitLift (x i)) (σ i) : ℤ) : ℚ) =
            ((-(2 * bitLift (x i)) : ℤ) : ℚ) := by
          simp only [ratVec] at e
          push_cast at e ⊢
          linarith
        exact_mod_cast e'
    have hmi := hmod (σ i)
    unfold Int.ModEq at hmi
    have hb1 := bitLift_zero_or_one (x i)
    have hb2 := bitLift_zero_or_one (d (σ i))
    apply bitLift_inj
    rcases hm with rfl | rfl <;> omega
  have e : x ∘ ⇑σ⁻¹ = d := by
    funext k
    obtain ⟨i, rfl⟩ := σ.surjective k
    change x (σ⁻¹ (σ i)) = d (σ i)
    rw [show σ⁻¹ (σ i) = i from σ.symm_apply_apply i]
    exact hxd i
  rw [e]
  exact hd

theorem sign_mem_C_of_rows {g : latticeO} {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ AutPerm)
    {a : Fin 24 → ZMod 2} (hrow : ∀ i, mat g i = sgn (a i) • Pi.single (σ i) 1) : a ∈ C := by
  have hu : lam 0 ∈ codeLattice C := (mem_minVecs_iff.1 (lam_mem_minVecs 0)).1
  obtain ⟨hw, hwr⟩ := latVec_spec g hu
  obtain ⟨m, hm, d, hd, hmod, -⟩ := hw
  have hda : ∀ i, d (σ i) = a i := by
    intro i
    have e := congrFun hwr (σ i)
    rw [vecMul_rows_apply σ.injective hrow] at e
    have hl : lam 0 i = 1 ∨ lam 0 i = -3 := by
      simp only [lam]
      split_ifs <;> simp
    have hmi := hmod (σ i)
    unfold Int.ModEq at hmi
    have hb2 := bitLift_zero_or_one (d (σ i))
    apply bitLift_inj
    rcases sgn_cases (a i) with ⟨ha, hs⟩ | ⟨ha, hs⟩ <;> rw [hs] at e <;> rw [ha]
    · have e' : ((latVec (mat g) (lam 0) (σ i) : ℤ) : ℚ) = ((lam 0 i : ℤ) : ℚ) := by
        simpa [ratVec] using e
      have e'' : latVec (mat g) (lam 0) (σ i) = lam 0 i := by exact_mod_cast e'
      have h0 : bitLift (0 : ZMod 2) = 0 := rfl
      rw [h0]
      rcases hm with rfl | rfl <;> omega
    · have e' : ((latVec (mat g) (lam 0) (σ i) : ℤ) : ℚ) = ((-lam 0 i : ℤ) : ℚ) := by
        simp only [ratVec] at e
        push_cast at e ⊢
        linarith
      have e'' : latVec (mat g) (lam 0) (σ i) = -lam 0 i := by exact_mod_cast e'
      have h1 : bitLift (1 : ZMod 2) = 1 := rfl
      rw [h1]
      rcases hm with rfl | rfl <;> omega
  have e : d ∘ ⇑σ = a := funext hda
  rw [← e]
  exact comp_mem_of_mem_AutPerm hσ hd

theorem exists_of_fix {g : latticeO} (hfix : modTwoEnd g frameClass = frameClass) :
    ∃ (a : C) (p : AutPerm), mat g = gmat a * Pmat p := by
  obtain ⟨σ, a, hrow⟩ := exists_signedPerm_of_fix hfix
  have hinj := injective_of_rows (mat_mul_transpose g) hrow
  let p : Equiv.Perm (Fin 24) := Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hinj)
  have hrow' : ∀ i, mat g i = sgn (a i) • Pi.single (p i) 1 := hrow
  have hp := perm_mem_AutPerm_of_rows hrow'
  have ha := sign_mem_C_of_rows hp hrow'
  refine ⟨⟨a, ha⟩, ⟨p, hp⟩, Matrix.ext fun i k => ?_⟩
  have h1 : Pi.single i 1 ᵥ* (gmat ⟨a, ha⟩ * Pmat p) = sgn (a i) • Pi.single (p i) 1 := by
    rw [← vecMul_vecMul, single_vecMul_gmat, smul_vecMul, single_vecMul_Pmat]
  have h2 : (gmat ⟨a, ha⟩ * Pmat p) i k = (Pi.single i 1 ᵥ* (gmat ⟨a, ha⟩ * Pmat p)) k := by
    rw [single_one_vecMul]
    rfl
  change mat g i k = _
  rw [h2, h1, ← hrow' i]

theorem modTwoEnd_frameClass_eq_iff (g : latticeO) :
    modTwoEnd g frameClass = frameClass ↔ ∃ (a : C) (p : AutPerm), g = gO a * PO p := by
  constructor
  · intro hfix
    obtain ⟨a, p, h⟩ := exists_of_fix hfix
    exact ⟨a, p, mat_injective (by rw [mat_mul, mat_gO, mat_PO, h])⟩
  · rintro ⟨a, p, rfl⟩
    rw [modTwoEnd_mul, Module.End.mul_apply, modTwoEnd_gO_frameClass, modTwoEnd_PO_frameClass]

end CFSG.Monster.Visible
