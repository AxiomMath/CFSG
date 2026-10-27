module

public import CFSG.ClassicalGroups.Symplectic.Model
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.H13.S127.L5.Sp4

open CFSG.Open Matrix

variable {F : Type} [Field F]

abbrev J : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F := fromBlocks 0 1 (-1) 0

theorem transpose_mul_J_mul (g : ↥(StatedSp 2 F)) :
    ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * J *
      ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = J := by
  obtain ⟨g, hg⟩ := g
  have h : g ∈ CFSG.Assembly.LowTwoRank.StatedSp 2 F := hg
  rw [CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic,
    TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup,
    ← CFSG.ClassicalGroups.Symplectic.blueprintGram_iff_mem_symplecticGroup] at h
  exact h

abbrev upperMat (S : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  fromBlocks 1 S 0 1

theorem upperMat_mul (S S' : Matrix (Fin 2) (Fin 2) F) :
    upperMat S * upperMat S' = upperMat (S + S') := by
  simp [upperMat, fromBlocks_multiply, add_comm]

@[expose] def upperGL (S : Matrix (Fin 2) (Fin 2) F) : GL (Fin 2 ⊕ Fin 2) F :=
  ⟨upperMat S, upperMat (-S), by rw [upperMat_mul]; simp, by rw [upperMat_mul]; simp⟩

theorem upperGL_mem {S : Matrix (Fin 2) (Fin 2) F} (hS : Sᵀ = S) :
    upperGL S ∈ StatedSp 2 F :=
  Subgroup.subset_closure (by
    show (upperMat S)ᵀ * fromBlocks 0 1 (-1) 0 * upperMat S = fromBlocks 0 1 (-1) 0
    simp [upperMat, fromBlocks_transpose, fromBlocks_multiply, hS])

abbrev symMat (a b c : F) : Matrix (Fin 2) (Fin 2) F := !![a, b; b, c]

omit [Field F] in
theorem symMat_transpose (a b c : F) : (symMat a b c)ᵀ = symMat a b c := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[expose] def upperHom : Multiplicative (F × F × F) →* ↥(StatedSp 2 F) where
  toFun s := ⟨upperGL (symMat (Multiplicative.toAdd s).1 (Multiplicative.toAdd s).2.1
    (Multiplicative.toAdd s).2.2), upperGL_mem (symMat_transpose _ _ _)⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    show upperMat (symMat 0 0 0) = 1
    have h0 : symMat (0 : F) 0 0 = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [h0]
    exact fromBlocks_one
  map_mul' s s' := by
    apply Subtype.ext
    apply Units.ext
    show upperMat _ = upperMat _ * upperMat _
    rw [upperMat_mul]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [symMat]

theorem coe_upperHom (a b c : F) :
    (((upperHom (Multiplicative.ofAdd (a, b, c)) : ↥(StatedSp 2 F)) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = upperMat (symMat a b c) := rfl

theorem upperMat_mulVec (S : Matrix (Fin 2) (Fin 2) F) (v : Fin 2 ⊕ Fin 2 → F) :
    upperMat S *ᵥ v = v + Sum.elim (S *ᵥ (v ∘ Sum.inr)) 0 := by
  rw [upperMat, fromBlocks_mulVec]
  funext i
  rcases i with i | i
  · simp only [Sum.elim_inl, Matrix.one_mulVec, Pi.add_apply, Function.comp_apply]
  · simp only [Sum.elim_inr, Matrix.zero_mulVec, Matrix.one_mulVec, zero_add, Pi.add_apply,
      Pi.zero_apply, add_zero, Function.comp_apply]

@[expose] def ell0 : Submodule F (Fin 2 ⊕ Fin 2 → F) where
  carrier := {v | ∀ i, v (Sum.inr i) = 0}
  add_mem' ha hb i := by simp [ha i, hb i]
  zero_mem' i := rfl
  smul_mem' c v hv i := by simp [hv i]

theorem mem_ell0 {v : Fin 2 ⊕ Fin 2 → F} : v ∈ ell0 ↔ ∀ i, v (Sum.inr i) = 0 := Iff.rfl

theorem elim_mem_ell0 (x : Fin 2 → F) : Sum.elim x 0 ∈ (ell0 : Submodule F _) := fun _ => rfl

@[expose] def ell0Equiv : ↥(ell0 (F := F)) ≃ₗ[F] (Fin 2 → F) where
  toFun v i := (v : Fin 2 ⊕ Fin 2 → F) (Sum.inl i)
  invFun x := ⟨Sum.elim x 0, elim_mem_ell0 x⟩
  map_add' v w := rfl
  map_smul' c v := rfl
  left_inv v := by
    apply Subtype.ext
    funext i
    rcases i with i | i
    · rfl
    · exact (v.2 i).symm
  right_inv x := rfl

theorem finrank_ell0 : Module.finrank F ↥(ell0 (F := F)) = 2 := by
  rw [ell0Equiv.finrank_eq, Module.finrank_fin_fun]

theorem exists_symMat_mulVec {y : Fin 2 → F} (hy : y ≠ 0) (x : Fin 2 → F) :
    ∃ a b c : F, symMat a b c *ᵥ y = x := by
  by_cases h0 : y 0 = 0
  · have h1 : y 1 ≠ 0 := fun h1 => hy (funext fun i => by fin_cases i <;> simp_all)
    refine ⟨0, x 0 / y 1, x 1 / y 1, funext fun i => ?_⟩
    fin_cases i <;> simp [symMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0] <;>
      field_simp
  · refine ⟨(x 0 - x 1 / y 0 * y 1) / y 0, x 1 / y 0, 0, funext fun i => ?_⟩
    fin_cases i <;> simp [symMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> field_simp
    ring

theorem eq_ell0_of_invariant (W : Submodule F (Fin 2 ⊕ Fin 2 → F))
    (hW : Module.finrank F ↥W = 2)
    (hinv : ∀ a b c : F, ∀ w ∈ W, upperMat (symMat a b c) *ᵥ w ∈ W) : W = ell0 := by
  have hdiff : ∀ a b c : F, ∀ w ∈ W,
      Sum.elim (symMat a b c *ᵥ (w ∘ Sum.inr)) 0 ∈ W := by
    intro a b c w hw
    have h := W.sub_mem (hinv a b c w hw) hw
    rwa [upperMat_mulVec, add_sub_cancel_left] at h
  have hle : W ≤ ell0 := by
    intro w hw
    by_contra hne
    have hy : w ∘ Sum.inr ≠ 0 := by
      intro h0
      exact hne fun i => congrFun h0 i
    have hge : ell0 ≤ W := by
      intro v hv
      obtain ⟨a, b, c, hS⟩ := exists_symMat_mulVec hy (fun i => v (Sum.inl i))
      have h := hdiff a b c w hw
      rw [hS] at h
      have hv' : v = Sum.elim (fun i => v (Sum.inl i)) 0 := by
        funext i
        rcases i with i | i
        · rfl
        · exact hv i
      rw [hv']
      exact h
    have heq : ell0 = W :=
      Submodule.eq_of_le_of_finrank_eq hge (by rw [finrank_ell0, hW])
    exact hne (heq ▸ hw)
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hW, finrank_ell0])

theorem eq_upperMat_of_fix (g : ↥(StatedSp 2 F))
    (hg : ∀ x : Fin 2 → F, ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
      *ᵥ Sum.elim x 0 = Sum.elim x 0) :
    ∃ a b c : F, ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      upperMat (symMat a b c) := by
  set M := ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) with hM
  have hJ := transpose_mul_J_mul g
  rw [← hM] at hJ
  have hblk := fromBlocks_toBlocks M
  have hA : M.toBlocks₁₁ = 1 := by
    ext i j
    have := congrFun (hg (Pi.single j 1)) (Sum.inl i)
    rw [← hblk] at this
    simpa [fromBlocks_mulVec, Matrix.one_apply, Pi.single_apply, eq_comm] using this
  have hC : M.toBlocks₂₁ = 0 := by
    ext i j
    have := congrFun (hg (Pi.single j 1)) (Sum.inr i)
    rw [← hblk] at this
    simpa [fromBlocks_mulVec, Pi.single_apply] using this
  rw [← hblk, hA, hC] at hJ
  simp only [fromBlocks_transpose, fromBlocks_multiply] at hJ
  simp at hJ
  obtain ⟨hD, hB⟩ := hJ
  have hD' : M.toBlocks₂₂ = 1 := hD
  rw [hD'] at hB
  simp at hB
  refine ⟨M.toBlocks₁₂ 0 0, M.toBlocks₁₂ 0 1, M.toBlocks₁₂ 1 1, ?_⟩
  rw [← hblk, hA, hC, hD']
  congr 1
  ext i j
  have hsym := congrFun (congrFun hB 1) 0
  simp at hsym
  have hsym' := neg_add_eq_zero.mp hsym
  fin_cases i <;> fin_cases j <;> simp [symMat, hsym']

abbrev diagMat (l : F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  fromBlocks (l • 1) 0 0 (l⁻¹ • 1)

@[expose] def diagGL {l : F} (hl : l ≠ 0) : GL (Fin 2 ⊕ Fin 2) F :=
  ⟨diagMat l, diagMat l⁻¹, by simp [diagMat, fromBlocks_multiply, smul_smul, hl],
    by simp [diagMat, fromBlocks_multiply, smul_smul, hl]⟩

theorem diagGL_mem {l : F} (hl : l ≠ 0) : diagGL hl ∈ StatedSp 2 F :=
  Subgroup.subset_closure (by
    show (diagMat l)ᵀ * fromBlocks 0 1 (-1) 0 * diagMat l = fromBlocks 0 1 (-1) 0
    simp [diagMat, fromBlocks_transpose, fromBlocks_multiply, smul_smul, hl])

theorem diagMat_mulVec_elim (l : F) (x : Fin 2 → F) :
    diagMat l *ᵥ Sum.elim x 0 = l • Sum.elim x 0 := by
  funext i
  rcases i with i | i <;> simp [diagMat, fromBlocks_mulVec, Matrix.smul_mulVec]

end CFSG.Quasithin.H13.S127.L5.Sp4
