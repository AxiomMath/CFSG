module

public import CFSG.Quasithin.H13.U3SixForm

public section

namespace CFSG.Quasithin.H13.U3.NLine

@[expose] def aList : List (List ℕ) :=
  [[1, 2, 4, 8, 16, 32], [1, 5, 8, 3, 63, 30], [1, 9, 3, 4, 46, 49], [1, 20, 44, 54, 46, 30],
   [1, 45, 54, 21, 63, 32], [1, 55, 21, 44, 16, 49], [6, 14, 22, 17, 59, 54],
   [6, 16, 17, 8, 2, 50], [6, 19, 43, 49, 59, 11], [6, 23, 8, 22, 63, 11], [6, 45, 49, 21, 63, 50],
   [6, 55, 21, 43, 2, 54], [10, 14, 36, 47, 19, 21], [10, 20, 44, 61, 9, 21],
   [10, 37, 4, 36, 16, 12], [10, 38, 61, 30, 19, 12], [10, 46, 47, 4, 9, 22],
   [10, 55, 30, 44, 16, 22], [13, 14, 50, 62, 38, 44], [13, 20, 32, 54, 46, 36],
   [13, 45, 54, 25, 5, 44], [13, 51, 3, 50, 46, 7], [13, 59, 25, 32, 38, 7],
   [13, 63, 62, 3, 5, 36], [24, 9, 35, 61, 20, 21], [24, 19, 43, 47, 14, 21],
   [24, 37, 17, 35, 2, 25], [24, 51, 47, 11, 20, 25], [24, 55, 11, 43, 2, 3],
   [24, 59, 61, 17, 14, 3], [27, 2, 30, 8, 16, 50], [27, 5, 8, 25, 45, 4], [27, 14, 36, 62, 38, 4],
   [27, 19, 25, 30, 38, 57], [27, 37, 21, 36, 16, 57], [27, 63, 62, 21, 45, 50],
   [28, 9, 35, 57, 51, 17], [28, 16, 11, 8, 2, 32], [28, 20, 12, 11, 51, 62],
   [28, 23, 8, 12, 45, 17], [28, 37, 21, 35, 2, 62], [28, 63, 57, 21, 45, 32],
   [31, 9, 32, 57, 51, 43], [31, 19, 50, 49, 59, 35], [31, 38, 22, 32, 59, 7],
   [31, 45, 49, 12, 23, 43], [31, 46, 12, 50, 51, 7], [31, 63, 57, 22, 23, 35],
   [33, 5, 49, 26, 23, 61], [33, 16, 26, 36, 37, 57], [33, 38, 22, 30, 19, 57],
   [33, 55, 30, 7, 37, 61], [33, 59, 36, 49, 19, 11], [33, 63, 7, 22, 23, 11],
   [34, 2, 4, 43, 55, 3], [34, 9, 32, 4, 46, 22], [34, 14, 50, 17, 59, 3],
   [34, 16, 17, 44, 55, 22], [34, 38, 43, 32, 59, 26], [34, 51, 44, 50, 46, 26],
   [41, 5, 57, 26, 23, 47], [41, 16, 26, 44, 55, 49], [41, 37, 4, 7, 55, 47],
   [41, 45, 7, 12, 23, 17], [41, 46, 12, 4, 9, 49], [41, 51, 44, 57, 9, 17],
   [42, 5, 57, 25, 45, 44], [42, 19, 25, 47, 14, 8], [42, 20, 12, 61, 9, 8],
   [42, 23, 62, 12, 45, 43], [42, 38, 61, 62, 14, 44], [42, 51, 47, 57, 9, 43],
   [48, 2, 30, 35, 37, 25], [48, 16, 11, 36, 37, 12], [48, 19, 50, 30, 38, 12],
   [48, 20, 32, 11, 51, 25], [48, 46, 35, 50, 51, 26], [48, 59, 36, 32, 38, 26],
   [52, 2, 26, 35, 37, 62], [52, 23, 54, 26, 5, 47], [52, 46, 35, 54, 20, 30],
   [52, 51, 3, 11, 20, 62], [52, 55, 11, 7, 37, 47], [52, 63, 7, 3, 5, 30], [56, 5, 49, 3, 63, 36],
   [56, 9, 3, 61, 20, 8], [56, 14, 22, 47, 19, 8], [56, 23, 54, 22, 63, 35],
   [56, 46, 47, 54, 20, 36], [56, 59, 61, 49, 19, 35], [60, 2, 26, 43, 55, 54],
   [60, 23, 62, 26, 5, 61], [60, 37, 17, 7, 55, 61], [60, 38, 43, 62, 14, 4],
   [60, 45, 7, 25, 5, 4], [60, 59, 25, 17, 14, 54]]

theorem aList_closed :
    id6 ∈ aList ∧ ∀ e ∈ aList, ∀ c ∈ [u6c 0, u6c 1, u6c 2, u6c 3], mul6 e c ∈ aList := by
  decide +kernel

@[expose] def kc : List ℕ := [28, 23, 8, 12, 45, 17]

@[expose] def c6List : List (List ℕ) :=
  [[1, 2, 4, 8, 16, 32], [28, 23, 8, 12, 45, 17], [41, 46, 12, 4, 9, 49], [1, 55, 21, 44, 16, 49],
   [41, 51, 44, 57, 9, 17], [28, 63, 57, 21, 45, 32]]

@[expose] def lineWords : List (List (Fin 5)) :=
  [[], [1, 3, 0, 0], [1, 1, 3, 0, 3], [1, 1, 2, 3, 0], [0, 1, 1, 3, 2], [1, 1, 1, 2],
   [1, 3, 0, 0, 2], [0, 0, 1, 1, 1], [1, 1, 2, 3], [2], [0, 3, 0, 0], [3, 3], [1, 3, 0, 3],
   [1, 3, 0, 0, 3], [0, 2, 3, 0], [0, 1, 1, 2, 3]]

theorem wordMat_k : wordMat [0, 3, 0] = kc := by decide +kernel

theorem aList_fix : ∀ e ∈ aList, vapp e 52 = 52 → e ∈ c6List := by
  decide +kernel

theorem aList_d : vapp dc 15 = 15 ∧ vapp dc 52 < 64 ∧ ∀ e ∈ aList, vapp e (vapp dc 52) ≠ 52 := by
  decide +kernel

theorem aList_lt : ∀ e ∈ aList, ∀ v < 64, vapp e v < 64 := by
  decide +kernel

@[expose] def c6f (e : List ℕ) : List ℕ := mul6 e (mul6 kc (mul6 e (mul6 kc kc)))

theorem c6List_cases : ∀ e ∈ c6List, e = id6 ∨
    (mul6 e (mul6 e e) = id6 ∧ ∃ v < 64, vapp e v ≠ v ∧ vapp e v < 64) ∨
    (mul6 (c6f e) (mul6 (c6f e) (c6f e)) = id6 ∧
      ∃ v < 64, vapp (c6f e) v ≠ v ∧ vapp (c6f e) v < 64) := by
  decide +kernel

theorem kc_order : mul6 kc (mul6 kc kc) = id6 ∧ kc ≠ id6 := by
  decide +kernel

theorem kc_fix_iff : ∀ v < 64, vapp kc v = v ↔ v = 0 ∨ v = 15 ∨ v = 52 ∨ v = 59 := by
  decide +kernel

theorem dotB_15_52 : dotB 15 (vapp b0c 52) = true := by
  decide +kernel

theorem lineWords_spec : (∀ w ∈ lineWords, vapp (wordMat w) 15 = 15) ∧
    ∀ c < 64, dotB 15 (vapp b0c c) = true →
      ∃ w ∈ lineWords, vapp (wordMat w) 52 = c ∨ vapp (wordMat w) 52 = c ^^^ 15 := by
  decide +kernel

theorem functional_cases : ∀ c < 64,
    (∀ m ∈ [u6c 0, u6c 1, u6c 2, u6c 3], ∀ y < 64, dotB c (vapp m y) = dotB c y) →
      (∀ y < 64, dotB c y = false) ∨ ∀ y < 64, dotB c y = dotB 15 (vapp b0c y) := by
  decide +kernel

open scoped Pointwise

theorem glLin_vecOf_of_coe {g : GL (Fin 6) (ZMod 2)} {e : List ℕ}
    (h : (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat e) (c : ℕ) :
    glLin g (vecOf c) = vecOf (vapp e c) := by
  rw [glLin_apply, h, colMat_mulVec_vecOf]

theorem exists_aList_of_mem_A
    (g : U33G) (hg : g ∈ u33Data.A) :
    ∃ e ∈ aList, ((rho6 g : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      colMat e := by
  refine mem_list_of_closure ((Units.coeHom _).comp rho6)
    (gens := [u6c 0, u6c 1, u6c 2, u6c 3]) ?_ aList_closed.1 aList_closed.2 g hg
  rintro g (rfl | rfl | rfl | rfl)
  · exact ⟨u6c 0, by simp, by rw [MonoidHom.comp_apply, rho6_abs.1]; rfl⟩
  · exact ⟨u6c 1, by simp, by rw [MonoidHom.comp_apply, rho6_abs.2.1]; rfl⟩
  · exact ⟨u6c 2, by simp, by rw [MonoidHom.comp_apply, rho6_abs.2.2.1]; rfl⟩
  · exact ⟨u6c 3, by simp, by rw [MonoidHom.comp_apply, rho6_abs.2.2.2.1]; rfl⟩

theorem exists_aList_of_fix
    {j : GL (Fin 6) (ZMod 2)} (hj : j ∈ J6) (h15 : glLin j (vecOf 15) = vecOf 15) :
    ∃ e ∈ aList, (j : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat e := by
  obtain ⟨g, rfl⟩ := hj
  have hw : psiW g w0 = w0 := by
    rw [w0, psiW_apply]
    exact congrArg Multiplicative.ofAdd h15
  exact exists_aList_of_mem_A g ((psiW_stab_w0.1 g).1 hw)

theorem dGL_zpow_cases (k : ℤ) : dGL ^ k = 1 ∨ dGL ^ k = dGL := by
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul, zpow_two, dGL_mul_self, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, dGL_mul_self, one_zpow, one_mul, zpow_one]

theorem mem_N6_cases
    {g : GL (Fin 6) (ZMod 2)}
    (hg : g ∈ N6) : g ∈ J6 ∨ ∃ j ∈ J6, g = j * dGL := by
  have hset : ((J6 ⊔ Subgroup.zpowers dGL : Subgroup (GL (Fin 6) (ZMod 2))) :
      Set (GL (Fin 6) (ZMod 2))) = (J6 : Set (GL (Fin 6) (ZMod 2))) * (Subgroup.zpowers dGL :
        Set (GL (Fin 6) (ZMod 2))) :=
    Subgroup.coe_mul_of_right_le_normalizer_left J6 (Subgroup.zpowers dGL)
      ((Subgroup.zpowers_le).2 dGL_mem_normalizer_J6)
  have hg' : g ∈ ((J6 ⊔ Subgroup.zpowers dGL : Subgroup (GL (Fin 6) (ZMod 2))) :
      Set (GL (Fin 6) (ZMod 2))) := by
    rw [sup_comm]
    exact hg
  rw [hset] at hg'
  obtain ⟨j, hj, _, ⟨k, rfl⟩, rfl⟩ := hg'
  rcases dGL_zpow_cases k with h | h
  · left
    simp only [h, mul_one]
    exact hj
  · exact Or.inr ⟨j, hj, by simp only [h]⟩

theorem exists_c6List_of_fix
    {g : GL (Fin 6) (ZMod 2)}
    (hg : g ∈ N6) (h15 : glLin g (vecOf 15) = vecOf 15) (h52 : glLin g (vecOf 52) = vecOf 52) :
    ∃ e ∈ c6List, (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat e := by
  have hd : ∀ c, glLin dGL (vecOf c) = vecOf (vapp dc c) := glLin_vecOf_of_coe rfl
  rcases mem_N6_cases hg with hJ | ⟨j, hj, rfl⟩
  · obtain ⟨e, he, hge⟩ := exists_aList_of_fix hJ h15
    refine ⟨e, aList_fix e he ?_, hge⟩
    rw [glLin_vecOf_of_coe hge] at h52
    exact vecOf_injective (aList_lt e he 52 (by norm_num)) (by norm_num) h52
  · exfalso
    have hjd : ∀ v, glLin (j * dGL) v = glLin j (glLin dGL v) := fun v => by
      rw [map_mul, LinearEquiv.mul_apply]
    rw [hjd, hd, aList_d.1] at h15
    obtain ⟨e, he, hje⟩ := exists_aList_of_fix hj h15
    rw [hjd, hd, glLin_vecOf_of_coe hje] at h52
    exact aList_d.2.2 e he (vecOf_injective (aList_lt e he _ aList_d.2.1) (by norm_num) h52)

noncomputable abbrev kGL : GL (Fin 6) (ZMod 2) := rho6 (wordElem [0, 3, 0])

theorem kGL_mem_J6 : kGL ∈ J6 := ⟨_, rfl⟩

theorem coe_kGL : (kGL : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat kc := by
  rw [coe_rho6_wordElem, wordMat_k]

theorem exists_J6_line
    {x y : W6} (hxy : b0 x y = 1) :
    ∃ j ∈ J6, glLin j (vecOf 15) = x ∧ (glLin j (vecOf 52) = y ∨ glLin j (vecOf 52) = y + x) := by
  have hx : Multiplicative.ofAdd x ≠ 1 := by
    intro h
    have hx0 : x = 0 := by
      have := congrArg Multiplicative.toAdd h
      simpa using this
    rw [hx0, LinearMap.map_zero₂] at hxy
    exact zero_ne_one hxy
  obtain ⟨g, hg⟩ := psiW_transitive _ hx
  have hg15 : glLin (rho6 g) (vecOf 15) = x := by
    rw [w0, psiW_apply] at hg
    exact congrArg Multiplicative.toAdd hg
  set y' := (glLin (rho6 g)).symm y with hy'
  have hyy : glLin (rho6 g) y' = y := LinearEquiv.apply_symm_apply _ _
  have hb : b0 (vecOf 15) y' = 1 := by
    have h1 := b0_mulVec_of_mem_b0Stab (J6_le_b0Stab ⟨g, rfl⟩) (vecOf 15) y'
    rw [← glLin_apply, ← glLin_apply, hg15, hyy, hxy] at h1
    exact h1.symm
  obtain ⟨c, hc, hcy⟩ := exists_vecOf y'
  have hdot : dotB 15 (vapp b0c c) = true := by
    rw [← hcy, b0_vecOf] at hb
    cases h : dotB 15 (vapp b0c c)
    · rw [h] at hb
      exact absurd hb (by decide)
    · rfl
  obtain ⟨w, hw, hw52⟩ := lineWords_spec.2 c hc hdot
  set a := rho6 (wordElem w) with ha
  have hca : (a : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat (wordMat w) := coe_rho6_wordElem w
  have ha15 : glLin a (vecOf 15) = vecOf 15 := by
    rw [glLin_vecOf_of_coe hca, lineWords_spec.1 w hw]
  refine ⟨rho6 g * a, mul_mem ⟨g, rfl⟩ ⟨_, rfl⟩, ?_, ?_⟩
  · rw [map_mul, LinearEquiv.mul_apply, ha15, hg15]
  · rw [map_mul, LinearEquiv.mul_apply, glLin_vecOf_of_coe hca]
    rcases hw52 with h | h
    · left
      rw [h, hcy, hyy]
    · right
      rw [h, vecOf_xor, hcy, map_add, hyy, hg15]

theorem exists_J6_vecOf15
    {x : W6} (hx : x ≠ 0) :
    ∃ j ∈ J6, glLin j (vecOf 15) = x := by
  have hx' : Multiplicative.ofAdd x ≠ 1 := fun h =>
    hx (by simpa using congrArg Multiplicative.toAdd h)
  obtain ⟨g, hg⟩ := psiW_transitive _ hx'
  refine ⟨rho6 g, ⟨g, rfl⟩, ?_⟩
  rw [w0, psiW_apply] at hg
  exact congrArg Multiplicative.toAdd hg

theorem exists_code_functional (f : W6 →ₗ[ZMod 2] ZMod 2) :
    ∃ c < 64, ∀ y, f y = vecOf c ⬝ᵥ y := by
  obtain ⟨c, hc, hcv⟩ := exists_vecOf (fun i => f (Pi.single i 1))
  refine ⟨c, hc, fun y => ?_⟩
  conv_lhs => rw [← Finset.univ_sum_single y]
  rw [map_sum, dotProduct, hcv]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : (Pi.single i (y i) : W6) = y i • (Pi.single i 1 : W6) := by
    rw [← Pi.single_smul', smul_eq_mul, mul_one]
  rw [h, map_smul, smul_eq_mul, mul_comm]

theorem bilin_eq_b0
    (B : LinearMap.BilinForm (ZMod 2) W6)
    (hB : ∀ j ∈ J6, ∀ x y, B (glLin j x) (glLin j y) = B x y) (hne : B ≠ 0) : B = b0 := by
  obtain ⟨c, hc, hf⟩ := exists_code_functional (B (vecOf 15))
  have hbit : ∀ v, B (vecOf 15) (vecOf v) = bit2 (dotB c v) := fun v => by
    rw [hf, vecOf_dotProduct]
  have key : ∀ i : Fin 5, i ≠ 4 → ∀ y,
      B (vecOf 15) (vecOf (vapp (u6c i) y)) = B (vecOf 15) (vecOf y) := by
    intro i hi y
    have h1 := hB (u6GL i) ⟨u33GenPG i, rho6_gen i⟩ (vecOf 15) (vecOf y)
    rwa [glLin_vecOf_of_coe (e := u6c i) rfl, glLin_vecOf_of_coe (e := u6c i) rfl,
      u6c_w0 i hi] at h1
  have hinv : ∀ m ∈ [u6c 0, u6c 1, u6c 2, u6c 3], ∀ y < 64, dotB c (vapp m y) = dotB c y := by
    intro m hm y _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · exact bit2_injective (by rw [← hbit, ← hbit]; exact key 0 (by decide) y)
    · exact bit2_injective (by rw [← hbit, ← hbit]; exact key 1 (by decide) y)
    · exact bit2_injective (by rw [← hbit, ← hbit]; exact key 2 (by decide) y)
    · exact bit2_injective (by rw [← hbit, ← hbit]; exact key 3 (by decide) y)
  have htr : ∀ (C : LinearMap.BilinForm (ZMod 2) W6),
      (∀ j ∈ J6, ∀ x y, C (glLin j x) (glLin j y) = C x y) →
        ∀ x y, x ≠ 0 → ∃ y', C x y = C (vecOf 15) y' ∧ b0 x y = b0 (vecOf 15) y' := by
    intro C hC x y hx
    obtain ⟨j, hj, rfl⟩ := exists_J6_vecOf15 hx
    refine ⟨(glLin j).symm y, ?_, ?_⟩
    · conv_lhs => rw [← LinearEquiv.apply_symm_apply (glLin j) y]
      exact hC j hj _ _
    · conv_lhs => rw [← LinearEquiv.apply_symm_apply (glLin j) y]
      have h1 := b0_mulVec_of_mem_b0Stab (J6_le_b0Stab hj) (vecOf 15) ((glLin j).symm y)
      rwa [← glLin_apply, ← glLin_apply] at h1
  rcases functional_cases c hc hinv with h0 | h1
  · exfalso
    apply hne
    refine LinearMap.ext₂ fun x y => ?_
    by_cases hx : x = 0
    · rw [hx, LinearMap.map_zero₂, LinearMap.zero_apply, LinearMap.zero_apply]
    obtain ⟨y', hy', -⟩ := htr B hB x y hx
    obtain ⟨v, hv, rfl⟩ := exists_vecOf y'
    rw [hy', hbit, h0 v hv, LinearMap.zero_apply, LinearMap.zero_apply]
    rfl
  · refine LinearMap.ext₂ fun x y => ?_
    by_cases hx : x = 0
    · rw [hx, LinearMap.map_zero₂, LinearMap.map_zero₂]
    obtain ⟨y', hy', hb⟩ := htr B hB x y hx
    obtain ⟨v, hv, rfl⟩ := exists_vecOf y'
    rw [hy', hb, hbit, h1 v hv, b0_vecOf]

end CFSG.Quasithin.H13.U3.NLine
