module

public import CFSG.Quasithin.H13.L32NKGG22

public section

namespace CFSG.Quasithin.H13.KGCert

open scoped commutatorElement

@[expose] def powW (w : List Bool) (n : ℕ) : List Bool := (List.replicate n w).flatten

@[expose] def wX : List Bool :=
  [true, true, true, false, false, false, true, false, false, false, true, true, true]

@[expose] def wY : List Bool :=
  [false, true, true, false, true, false, false, false, false, true, false, false]

@[expose] def wA₂ : List Bool := [true, true, true, true, true, true, false, false, false, false]

@[expose] def wB₂ : List Bool :=
  [true, true, true, false, true, false, false, false, true, true, false, false, true]

theorem word_checks :
    evalWord (powW wX 7) = oneC ∧ evalWord wX ≠ oneC ∧ evalWord (powW wY 4) = oneC ∧
      evalWord (powW wX 6 ++ wY ++ (powW wY 3 ++ wX)) = oneC ∧
      evalWord (wY ++ powW wX 5 ++ (powW wX 2 ++ powW wY 3)) = oneC ∧
      evalWord wX = evalWord (powW wX 6 ++ wY ++ (wY ++ powW wX 5) ++ (powW wY 3 ++ wX) ++
        (powW wX 2 ++ powW wY 3)) ∧
      evalWord (powW wX 6 ++ wX) = oneC ∧
      evalWord (wY ++ wX ++ powW wY 3 ++ (wY ++ powW wX 6 ++ powW wY 3)) = oneC ∧
      evalWord wY = evalWord (powW wX 6 ++ (wY ++ wX ++ powW wY 3) ++ wX ++
        (wY ++ powW wX 6 ++ powW wY 3)) ∧
      evalWord (powW [true] 7) = oneC ∧ evalWord [true] ≠ oneC ∧
      evalWord (powW wA₂ 7) = oneC ∧ evalWord wA₂ ≠ oneC ∧
      evalWord (powW [true, true, true] 7) = oneC ∧ evalWord [true, true, true] ≠ oneC ∧
      evalWord (powW wB₂ 7) = oneC ∧ evalWord wB₂ ≠ oneC ∧
      evalWord (powW (true :: wA₂) 3) = oneC ∧ evalWord (true :: wA₂) ≠ oneC ∧
      evalWord (powW ([true, true, true] ++ wB₂) 3) = oneC ∧
      evalWord (true :: wA₂ ++ ([true, true, true] ++ wB₂)) =
        evalWord ([true, true, true] ++ wB₂ ++ true :: wA₂) ∧
      evalWord ([true, true, true] ++ wB₂) ≠ oneC ∧
      evalWord ([true, true, true] ++ wB₂) ≠ evalWord (true :: wA₂) ∧
      evalWord ([true, true, true] ++ wB₂) ≠ evalWord (powW (true :: wA₂) 2) := by
  decide +kernel

theorem gA_fix : ∀ n < 64, mulVecC gAc n = n → n = 0 := by decide +kernel

theorem validC_gAc : ValidC gAc := ⟨rfl, by decide⟩

theorem validC_gBc : ValidC gBc := ⟨rfl, by decide⟩

theorem validC_evalWord (w : List Bool) : ValidC (evalWord w) := by
  induction w with
  | nil => exact validC_oneC
  | cons g w ih =>
    rw [evalWord_cons]
    cases g
    · exact validC_mulC validC_gBc ih
    · exact validC_mulC validC_gAc ih

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def wordEval (γA γB : V ≃ₗ[ZMod 2] V) (w : List Bool) : V ≃ₗ[ZMod 2] V :=
  w.foldr (fun g acc => (if g then γA else γB) * acc) 1

theorem wordEval_append (γA γB : V ≃ₗ[ZMod 2] V) (w₁ w₂ : List Bool) :
    wordEval γA γB (w₁ ++ w₂) = wordEval γA γB w₁ * wordEval γA γB w₂ := by
  induction w₁ with
  | nil => simp [wordEval]
  | cons g w ih =>
    simp only [wordEval, List.cons_append, List.foldr_cons] at ih ⊢
    rw [ih, mul_assoc]

theorem wordEval_powW (γA γB : V ≃ₗ[ZMod 2] V) (w : List Bool) (n : ℕ) :
    wordEval γA γB (powW w n) = wordEval γA γB w ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [powW, List.replicate_succ, List.flatten_cons, wordEval_append, ← powW, ih, pow_succ']

theorem wordEval_mem {Γ : Subgroup (V ≃ₗ[ZMod 2] V)} {γA γB : V ≃ₗ[ZMod 2] V} (hA : γA ∈ Γ)
    (hB : γB ∈ Γ) (w : List Bool) : wordEval γA γB w ∈ Γ := by
  induction w with
  | nil => exact Γ.one_mem
  | cons g w ih =>
    cases g
    · exact Γ.mul_mem hB ih
    · exact Γ.mul_mem hA ih

variable [Finite V]

theorem exists_facts (hO : KGSp6Order12096) (B : LinearMap.BilinForm (ZMod 2) V)
    (hBalt : ∀ v, B v v = 0) (hBnd : ∀ v, (∀ w, B v w = 0) → v = 0)
    (hdim : Module.finrank (ZMod 2) V = 6) (Γ : Subgroup (V ≃ₗ[ZMod 2] V))
    (hΓB : ∀ γ ∈ Γ, ∀ v w, B (γ v) (γ w) = B v w) (hcard : Nat.card Γ = 12096) :
    (∃ P : Subgroup (V ≃ₗ[ZMod 2] V), P ≤ Γ ∧ P ≠ ⊥ ∧ ⁅P, P⁆ = P) ∧
    (∃ γ₀ ∈ Γ, γ₀ ^ 7 = 1 ∧ γ₀ ≠ 1 ∧ ∀ v, γ₀ v = v → v = 0) ∧
    (∃ a₁ ∈ Γ, ∃ a₂ ∈ Γ, ∃ b₁ ∈ Γ, ∃ b₂ ∈ Γ, a₁ ^ 7 = 1 ∧ a₁ ≠ 1 ∧ a₂ ^ 7 = 1 ∧ a₂ ≠ 1 ∧
      b₁ ^ 7 = 1 ∧ b₁ ≠ 1 ∧ b₂ ^ 7 = 1 ∧ b₂ ≠ 1 ∧ (a₁ * a₂) ^ 3 = 1 ∧ a₁ * a₂ ≠ 1 ∧
      (b₁ * b₂) ^ 3 = 1 ∧ a₁ * a₂ * (b₁ * b₂) = b₁ * b₂ * (a₁ * a₂) ∧ b₁ * b₂ ≠ 1 ∧
      b₁ * b₂ ≠ a₁ * a₂ ∧ b₁ * b₂ ≠ (a₁ * a₂) ^ 2) := by
  obtain ⟨b, hb⟩ := hO V B hBalt hBnd hdim Γ hΓB hcard
  set m : (V ≃ₗ[ZMod 2] V) → Matrix (Fin 6) (Fin 6) (ZMod 2) :=
    fun γ => LinearMap.toMatrix b b (γ : V →ₗ[ZMod 2] V) with hm
  have hmul : ∀ γ δ : V ≃ₗ[ZMod 2] V, m (γ * δ) = m γ * m δ := fun γ δ => by
    simp only [hm, LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul]
  have hone : m 1 = 1 := by
    simp only [hm, LinearEquiv.coe_toLinearMap_one, LinearMap.toMatrix_id]
  have hinj : ∀ γ δ : V ≃ₗ[ZMod 2] V, m γ = m δ → γ = δ := fun γ δ h =>
    LinearEquiv.toLinearMap_injective ((LinearMap.toMatrix b b).injective h)
  obtain ⟨γA, hγA, hmA⟩ := (hb (decodeC gAc)).mp (Submonoid.subset_closure (Or.inl rfl))
  obtain ⟨γB, hγB, hmB⟩ := (hb (decodeC gBc)).mp (Submonoid.subset_closure (Or.inr rfl))
  set W := wordEval γA γB with hW
  have hmW : ∀ w, m (W w) = decodeC (evalWord w) := by
    intro w
    induction w with
    | nil => rw [hW, wordEval, List.foldr_nil, hone, evalWord, List.foldr_nil, decodeC_oneC]
    | cons g w ih =>
      have e1 : W (g :: w) = (if g then γA else γB) * W w := rfl
      rw [e1, hmul, ih, evalWord_cons, decodeC_mulC _ _ (length_evalWord w)]
      cases g
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact congrArg (· * _) hmB
      · simp only [↓reduceIte]
        exact congrArg (· * _) hmA
  have heq : ∀ w w', evalWord w = evalWord w' → W w = W w' := fun w w' h =>
    hinj _ _ (by rw [hmW, hmW, h])
  have hne : ∀ w w', evalWord w ≠ evalWord w' → W w ≠ W w' := fun w w' h h' =>
    h (decodeC_injOn (validC_evalWord w) (validC_evalWord w') (by rw [← hmW, ← hmW, h']))
  have hW1 : W [] = 1 := rfl
  have hone' : ∀ w, evalWord w = oneC → W w = 1 := fun w h => heq w [] h
  have hne1 : ∀ w, evalWord w ≠ oneC → W w ≠ 1 := fun w h => hne w [] h
  have hpow : ∀ w n, W (powW w n) = W w ^ n := wordEval_powW γA γB
  have happ : ∀ w₁ w₂, W (w₁ ++ w₂) = W w₁ * W w₂ := wordEval_append γA γB
  have hmem : ∀ w, W w ∈ Γ := wordEval_mem hγA hγB
  obtain ⟨c1, c2, c3, cu, cv, cx, cc1, cc2, cy, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15,
    c16, c17, c18, c19, c20⟩ := word_checks
  have hinv : ∀ w w', evalWord (w ++ w') = oneC → (W w)⁻¹ = W w' := fun w w' h =>
    inv_eq_of_mul_eq_one_right (by rw [← happ]; exact hone' _ h)
  refine ⟨?_, ?_, ?_⟩
  ·
    obtain ⟨X, hX⟩ : ∃ X, W wX = X := ⟨_, rfl⟩
    obtain ⟨Y, hY⟩ : ∃ Y, W wY = Y := ⟨_, rfl⟩
    obtain ⟨P, hP⟩ : ∃ P : Subgroup (V ≃ₗ[ZMod 2] V), Subgroup.closure {X, Y} = P := ⟨_, rfl⟩
    have hXP : X ∈ P := hP ▸ Subgroup.subset_closure (Or.inl rfl)
    have hYP : Y ∈ P := hP ▸ Subgroup.subset_closure (Or.inr rfl)
    have hWP : ∀ n, W (powW wX n) ∈ P := fun n => by rw [hpow, hX]; exact P.pow_mem hXP n
    have hWP' : ∀ n, W (powW wY n) ∈ P := fun n => by rw [hpow, hY]; exact P.pow_mem hYP n
    have hX' : X = ⁅W (powW wX 6 ++ wY), W (wY ++ powW wX 5)⁆ := by
      rw [commutatorElement_def, hinv _ _ cu, hinv _ _ cv, ← happ, ← happ, ← happ, ← hX]
      exact heq _ _ cx
    have hY' : Y = ⁅W (powW wX 6), W (wY ++ wX ++ powW wY 3)⁆ := by
      rw [commutatorElement_def, hinv _ _ cc1, hinv _ _ cc2, ← happ, ← happ, ← happ, ← hY]
      exact heq _ _ cy
    refine ⟨P, ?_, ?_, ?_⟩
    · rw [← hP, Subgroup.closure_le]
      rintro z (rfl | rfl)
      · rw [← hX]; exact hmem _
      · rw [← hY]; exact hmem _
    · intro hb'
      have : X = 1 := by rw [← Subgroup.mem_bot, ← hb']; exact hXP
      exact hne1 _ c2 (hX.trans this)
    · refine le_antisymm (Subgroup.commutator_le.mpr fun a ha b hb => ?_) ?_
      · exact P.mul_mem (P.mul_mem (P.mul_mem ha hb) (P.inv_mem ha)) (P.inv_mem hb)
      · conv_lhs => rw [← hP]
        rw [Subgroup.closure_le]
        rintro z (rfl | rfl)
        · have h := Subgroup.commutator_mem_commutator
            (by rw [happ]; exact P.mul_mem (hWP 6) (hY ▸ hYP) : W (powW wX 6 ++ wY) ∈ P)
            (by rw [happ]; exact P.mul_mem (hY ▸ hYP) (hWP 5) : W (wY ++ powW wX 5) ∈ P)
          rw [← hX'] at h
          exact h
        · have h := Subgroup.commutator_mem_commutator (hWP 6)
            (by rw [happ, happ]; exact P.mul_mem (P.mul_mem (hY ▸ hYP) (hX ▸ hXP)) (hWP' 3) :
              W (wY ++ wX ++ powW wY 3) ∈ P)
          rw [← hY'] at h
          exact h
  ·
    refine ⟨W [true], hmem _, by rw [← hpow]; exact hone' _ c6, hne1 _ c7, fun v hv => ?_⟩
    have hWA : W [true] = γA := by
      show γA * 1 = γA
      rw [mul_one]
    rw [hWA] at hv
    have h1 := LinearMap.toMatrix_mulVec_repr b b (γA : V →ₗ[ZMod 2] V) v
    have h2 : LinearMap.toMatrix b b (γA : V →ₗ[ZMod 2] V) = decodeC gAc := hmA
    rw [h2] at h1
    have hv' : (γA : V →ₗ[ZMod 2] V) v = v := hv
    rw [hv'] at h1
    have h3 := vec6_code6 (b.repr v)
    rw [← h3, decodeC_mulVec] at h1
    have h4 := vec6_inj (mulVecC_lt validC_gAc _) (code6_lt _) h1
    have h5 := gA_fix _ (code6_lt _) h4
    rw [h5, vec6_zero] at h3
    exact b.repr.injective (by rw [map_zero]; exact Finsupp.ext (congrFun h3.symm))
  · refine ⟨W [true], hmem _, W wA₂, hmem _, W [true, true, true], hmem _, W wB₂, hmem _,
      by rw [← hpow]; exact hone' _ c6, hne1 _ c7, by rw [← hpow]; exact hone' _ c8,
      hne1 _ c9, by rw [← hpow]; exact hone' _ c10, hne1 _ c11,
      by rw [← hpow]; exact hone' _ c12, hne1 _ c13, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← happ, ← hpow]
      exact hone' _ c14
    · rw [← happ]
      exact hne1 _ c15
    · rw [← happ, ← hpow]
      exact hone' _ c16
    · rw [← happ, ← happ, ← happ, ← happ]
      exact heq _ _ c17
    · rw [← happ]
      exact hne1 _ c18
    · rw [← happ, ← happ]
      exact hne _ _ c19
    · rw [← happ, ← happ, ← hpow]
      exact hne _ _ c20

end CFSG.Quasithin.H13.KGCert
