module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8H1Cert
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8H1Coords

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.StandardType.Triality CFSG.LieType.SpinGeom CFSG.Quasithin.JonesParshall
open scoped Matrix

attribute [-instance] CFSG.Sporadic.Schreier.Tits.titsZMod2CharP

@[expose] def genC : Fin 8 → Fin 3 → ZMod 2 :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], 0, 0, 0, 0, 0]

@[expose] def genM : Fin 8 → Fin 3 → ZMod 2 :=
  ![0, 0, 0, ![1, 0, 0], ![0, 1, 0], ![0, 0, 1], 0, 0]

@[expose] def genA : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  ⟨!![1, 0, 0; 0, 1, 0; 1, 0, 1], by decide⟩

@[expose] def genB : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  ⟨!![0, 1, 0; 0, 0, 1; 1, 0, 0], by decide⟩

@[expose] def genG : Fin 8 → Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  ![1, 1, 1, 1, 1, 1, genA, genB]

@[expose] noncomputable def gensP (j : Fin 8) : ↥spinH := sEH (genC j) (genM j) (genG j)

private def sixteenC8H1Gens_cIdx (i : Fin 3) : Fin 8 := ⟨i.1, by omega⟩

private def sixteenC8H1Gens_mIdx (i : Fin 3) : Fin 8 := ⟨i.1 + 3, by omega⟩

private noncomputable def sixteenC8H1Gens_S : Subgroup ↥spinH :=
  Subgroup.closure (Set.range gensP)

private theorem sixteenC8H1Gens_sEH_mul (c₁ m₁ c₂ m₂ : Fin 3 → ZMod 2)
    (g₁ g₂ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    sEH c₁ m₁ g₁ * sEH c₂ m₂ g₂ =
      sEH (c₁ + (g₁ : Matrix (Fin 3) (Fin 3) (ZMod 2)).adjugateᵀ *ᵥ c₂ +
        CFSG.LieType.SpinGeom.altMat (ZMod 2)
          ((g₁ : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ m₂) *ᵥ m₁)
        (m₁ + (g₁ : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ m₂) (g₁ * g₂) := by
  apply Subtype.ext
  show spinHom (sE c₁ m₁ g₁) * spinHom (sE c₂ m₂ g₂) =
    spinHom (sE (c₁ + (g₁ : Matrix (Fin 3) (Fin 3) (ZMod 2)).adjugateᵀ *ᵥ c₂ +
        CFSG.LieType.SpinGeom.altMat (ZMod 2)
          ((g₁ : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ m₂) *ᵥ m₁)
        (m₁ + (g₁ : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ m₂) (g₁ * g₂))
  rw [← map_mul, sE_mul]

private theorem sixteenC8H1Gens_sEH_zero : sEH (0 : Fin 3 → ZMod 2) 0
    (1 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = 1 := by
  apply Subtype.ext
  show spinHom (sE (0 : Fin 3 → ZMod 2) 0
    (1 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) = 1
  rw [sE_one, map_one]

private theorem sixteenC8H1Gens_sEH_c_add (c₁ c₂ : Fin 3 → ZMod 2) :
    sEH (c₁ + c₂) 0 (1 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) =
      sEH c₁ 0 1 * sEH c₂ 0 1 := by
  rw [sixteenC8H1Gens_sEH_mul]
  simp [Matrix.adjugate_one]

private theorem sixteenC8H1Gens_sEH_m_add (m₁ m₂ : Fin 3 → ZMod 2) :
    sEH 0 (m₁ + m₂) 1 =
      (sEH (CFSG.LieType.SpinGeom.altMat (ZMod 2) m₂ *ᵥ m₁) 0 1)⁻¹ *
        (sEH 0 m₁ 1 * sEH 0 m₂ 1) := by
  have h : sEH 0 m₁ 1 * sEH 0 m₂ 1 =
      sEH (CFSG.LieType.SpinGeom.altMat (ZMod 2) m₂ *ᵥ m₁) 0 1 *
        sEH 0 (m₁ + m₂) 1 := by
    rw [sixteenC8H1Gens_sEH_mul, sixteenC8H1Gens_sEH_mul]
    simp [Matrix.adjugate_one]
  rw [h, inv_mul_cancel_left]

private theorem sixteenC8H1Gens_sEH_cm (c m : Fin 3 → ZMod 2) :
    sEH c m 1 = sEH c 0 1 * sEH 0 m 1 := by
  rw [sixteenC8H1Gens_sEH_mul]
  simp [Matrix.adjugate_one]

private theorem sixteenC8H1Gens_sEH_g (c m : Fin 3 → ZMod 2)
    (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    sEH c m g = sEH c m 1 * sEH 0 0 g := by
  rw [sixteenC8H1Gens_sEH_mul]
  simp [Matrix.adjugate_one, CFSG.LieType.SpinGeom.altMat_zero]

private theorem sixteenC8H1Gens_end_mul_apply {M : Type*} [AddCommMonoid M]
    (f g : AddMonoid.End M) (x : M) : (f * g) x = f (g x) := rfl

private theorem sixteenC8H1Gens_c_decomp (c : Fin 3 → ZMod 2) :
    (∑ i : Fin 3, c i • genC (sixteenC8H1Gens_cIdx i)) = c := by
  funext j
  fin_cases j <;> simp [Fin.sum_univ_three, genC, sixteenC8H1Gens_cIdx]

private theorem sixteenC8H1Gens_m_decomp (m : Fin 3 → ZMod 2) :
    (∑ i : Fin 3, m i • genM (sixteenC8H1Gens_mIdx i)) = m := by
  funext j
  fin_cases j <;> simp [Fin.sum_univ_three, genM, sixteenC8H1Gens_mIdx]

private theorem sixteenC8H1Gens_genM_cIdx (i : Fin 3) :
    genM (sixteenC8H1Gens_cIdx i) = 0 := by
  fin_cases i <;> rfl

private theorem sixteenC8H1Gens_genG_cIdx (i : Fin 3) :
    genG (sixteenC8H1Gens_cIdx i) = 1 := by
  fin_cases i <;> rfl

private theorem sixteenC8H1Gens_gensP_cIdx (i : Fin 3) :
    sEH (genC (sixteenC8H1Gens_cIdx i)) 0 1 = gensP (sixteenC8H1Gens_cIdx i) := by
  rw [gensP, sixteenC8H1Gens_genM_cIdx, sixteenC8H1Gens_genG_cIdx]

private theorem sixteenC8H1Gens_genC_mIdx (i : Fin 3) :
    genC (sixteenC8H1Gens_mIdx i) = 0 := by
  fin_cases i <;> rfl

private theorem sixteenC8H1Gens_genG_mIdx (i : Fin 3) :
    genG (sixteenC8H1Gens_mIdx i) = 1 := by
  fin_cases i <;> rfl

private theorem sixteenC8H1Gens_gensP_mIdx (i : Fin 3) :
    sEH 0 (genM (sixteenC8H1Gens_mIdx i)) 1 = gensP (sixteenC8H1Gens_mIdx i) := by
  rw [gensP, sixteenC8H1Gens_genC_mIdx, sixteenC8H1Gens_genG_mIdx]

private theorem sixteenC8H1Gens_mem_c (c : Fin 3 → ZMod 2) :
    sEH c 0 1 ∈ sixteenC8H1Gens_S := by
  have key : ∀ s : Finset (Fin 3),
      sEH (∑ i ∈ s, c i • genC (sixteenC8H1Gens_cIdx i)) 0 1 ∈ sixteenC8H1Gens_S := by
    intro s
    induction s using Finset.induction with
    | empty =>
        simp only [Finset.sum_empty]
        rw [sixteenC8H1Gens_sEH_zero]
        exact Subgroup.one_mem _
    | insert i s hi ih =>
        rw [Finset.sum_insert hi]
        rw [sixteenC8H1Gens_sEH_c_add]
        apply Subgroup.mul_mem
        · have hci : c i = 0 ∨ c i = 1 := by
            have : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
            exact this (c i)
          rcases hci with h0 | h1
          · rw [h0, zero_smul, sixteenC8H1Gens_sEH_zero]; exact Subgroup.one_mem _
          · rw [h1, one_smul, sixteenC8H1Gens_gensP_cIdx]
            exact Subgroup.subset_closure (Set.mem_range_self (sixteenC8H1Gens_cIdx i))
        · exact ih
  have h := key Finset.univ
  rwa [sixteenC8H1Gens_c_decomp] at h

private theorem sixteenC8H1Gens_mem_m (m : Fin 3 → ZMod 2) :
    sEH 0 m 1 ∈ sixteenC8H1Gens_S := by
  have key : ∀ s : Finset (Fin 3),
      sEH 0 (∑ i ∈ s, m i • genM (sixteenC8H1Gens_mIdx i)) 1 ∈ sixteenC8H1Gens_S := by
    intro s
    induction s using Finset.induction with
    | empty =>
        simp only [Finset.sum_empty]
        rw [sixteenC8H1Gens_sEH_zero]
        exact Subgroup.one_mem _
    | insert i s hi ih =>
        rw [Finset.sum_insert hi, add_comm (m i • genM (sixteenC8H1Gens_mIdx i))]
        rw [sixteenC8H1Gens_sEH_m_add]
        apply Subgroup.mul_mem
        · exact Subgroup.inv_mem _ (sixteenC8H1Gens_mem_c _)
        · apply Subgroup.mul_mem
          · exact ih
          · have hmi : m i = 0 ∨ m i = 1 := by
              have : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
              exact this (m i)
            rcases hmi with h0 | h1
            · rw [h0, zero_smul, sixteenC8H1Gens_sEH_zero]; exact Subgroup.one_mem _
            · rw [h1, one_smul, sixteenC8H1Gens_gensP_mIdx]
              exact Subgroup.subset_closure (Set.mem_range_self (sixteenC8H1Gens_mIdx i))
  have h := key Finset.univ
  rwa [sixteenC8H1Gens_m_decomp] at h

private def sixteenC8H1Gens_tw : Fin 3 → Fin 3 → List (Fin 2)
  | 0, 1 => [1, 1, 0, 1]
  | 0, 2 => [1, 0, 1, 0, 1, 1, 0, 1, 0, 1]
  | 1, 0 => [0, 1, 0, 1, 1, 0, 1, 0, 1, 1]
  | 1, 2 => [1, 0, 1, 1]
  | 2, 0 => [0]
  | 2, 1 => [0, 1, 1, 0, 1, 0, 1, 1, 0, 1]
  | _, _ => []

private theorem sixteenC8H1Gens_wordEval_mem {G : Type*} [Group G] {k : ℕ} {gens : Fin k → G}
    {H : Subgroup G} (h : ∀ i, gens i ∈ H) : ∀ w, wordEval gens w ∈ H := by
  intro w
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons i w ih =>
      change gens i * wordEval gens w ∈ H
      exact Subgroup.mul_mem H (h i) ih

private theorem sixteenC8H1Gens_transvection_mem (i j : Fin 3) (hij : i ≠ j) (c : ZMod 2) :
    (Matrix.TransvectionStruct.mk i j hij c).toSpecialLinearGroup ∈
      Subgroup.closure ({genA, genB} :
        Set (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) := by
  have hc : c = 0 ∨ c = 1 := by
    have : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    exact this c
  rcases hc with rfl | rfl
  · rw [show (Matrix.TransvectionStruct.mk i j hij (0 : ZMod 2)).toSpecialLinearGroup = 1
        from by
      apply Subtype.ext
      simp [Matrix.TransvectionStruct.toMatrix_mk, Matrix.transvection_zero]]
    exact Subgroup.one_mem _
  · have hword : (Matrix.TransvectionStruct.mk i j hij (1 : ZMod 2)).toSpecialLinearGroup =
        wordEval ![genA, genB] (sixteenC8H1Gens_tw i j) := by
      fin_cases i <;> fin_cases j <;>
        first
        | exact (hij rfl).elim
        | (apply Subtype.ext
           rw [Matrix.TransvectionStruct.toSpecialLinearGroup_coe,
             Matrix.TransvectionStruct.toMatrix_mk]
           decide)
    rw [hword]
    exact sixteenC8H1Gens_wordEval_mem
      (fun k => by fin_cases k <;> exact Subgroup.subset_closure (by simp)) _

private theorem sixteenC8H1Gens_closure_genA_genB :
    Subgroup.closure ({genA, genB} :
      Set (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) = ⊤ := by
  apply closure_eq_top_of_transvection
  rintro ⟨i, j, hij, c⟩
  exact sixteenC8H1Gens_transvection_mem i j hij c

private noncomputable def sixteenC8H1Gens_iota :
    Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* ↥spinH where
  toFun g := sEH 0 0 g
  map_one' := sixteenC8H1Gens_sEH_zero
  map_mul' g₁ g₂ := by
    rw [sixteenC8H1Gens_sEH_mul]
    simp [Matrix.adjugate_one]

private theorem sixteenC8H1Gens_mem_g (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    sEH 0 0 g ∈ sixteenC8H1Gens_S := by
  have htop : Subgroup.closure ({genA, genB} :
      Set (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) = ⊤ :=
    sixteenC8H1Gens_closure_genA_genB
  have hle : Subgroup.closure (sixteenC8H1Gens_iota '' ({genA, genB} :
      Set (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))) ≤ sixteenC8H1Gens_S := by
    rw [Subgroup.closure_le]
    rintro x ⟨y, hy, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · change sEH 0 0 genA ∈ sixteenC8H1Gens_S
      rw [show sEH 0 0 genA = gensP 6 from rfl]
      exact Subgroup.subset_closure (Set.mem_range_self 6)
    · change sEH 0 0 genB ∈ sixteenC8H1Gens_S
      rw [show sEH 0 0 genB = gensP 7 from rfl]
      exact Subgroup.subset_closure (Set.mem_range_self 7)
  have hx : g ∈ Subgroup.closure ({genA, genB} :
      Set (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) := by
    rw [htop]
    exact Subgroup.mem_top g
  have hmem : sixteenC8H1Gens_iota g ∈ Subgroup.closure
      (sixteenC8H1Gens_iota '' ({genA, genB} :
        Set (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))) := by
    rw [← MonoidHom.map_closure]
    exact Subgroup.mem_map_of_mem _ hx
  exact hle hmem

private theorem sixteenC8H1Gens_eq_sEH_of_fix (h : ↥spinH)
    (hh : (h : MulAut SpinW) (Multiplicative.ofAdd (frameE (ZMod 2) 0)) =
      Multiplicative.ofAdd (frameE (ZMod 2) 0)) :
    ∃ (c m : Fin 3 → ZMod 2) (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)),
      h = sEH c m g := by
  obtain ⟨g, hgS, hgg⟩ := (mem_spinH_iff (h : MulAut SpinW)).1 h.2
  have hfix : (((g : GL (Fin (2 * 4)) (ZMod 2)) :
      Matrix (Fin (2 * 4)) (Fin (2 * 4)) (ZMod 2)) *ᵥ frameE (ZMod 2) 0) =
      frameE (ZMod 2) 0 := by
    have h' : spinHom g (Multiplicative.ofAdd (frameE (ZMod 2) 0)) =
        Multiplicative.ofAdd (frameE (ZMod 2) 0) := by
      rw [hgg]
      exact hh
    rw [spinHom_apply] at h'
    exact Multiplicative.ofAdd.injective h'
  obtain ⟨c, m, gm, hgdet, hact⟩ := spinStabNormalForm_of_count (K := ZMod 2)
    (fun c m g hg => exists_mem_spinSeven_spinElt c m g hg)
    (fun b hb hQ => spinSeven_transitive (ZMod 2) b hb hQ) g hgS hfix
  refine ⟨c, m, ⟨gm, hgdet⟩, ?_⟩
  have hg_eq : g = sE c m ⟨gm, hgdet⟩ := sE_eq_of_act hact
  apply Subtype.ext
  show (h : MulAut SpinW) = spinHom (sE c m ⟨gm, hgdet⟩)
  rw [← hgg, hg_eq]

theorem matsP_eq_stabMat (j : Fin 8) :
    matsP j = stabMat (genC j) (genM j) (genG j : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  fin_cases j <;> decide +kernel

theorem spinMu_gensP (j : Fin 8) (u : Fin 8 → ZMod 2) : spinMu (gensP j) u = matsP j *ᵥ u := by
  rw [gensP, spinMu_sEH, ← matsP_eq_stabMat]

theorem wordEval_relsP (r : Fin 10) : wordEval gensP (relsP r) = 1 := by
  have key : ∀ w : List (Fin 8), ∀ u : Fin 8 → ZMod 2,
      spinMu (wordEval gensP w) u = wordEvalM matsP w *ᵥ u := by
    intro w u
    induction w with
    | nil => simp [wordEval, wordEvalM]
    | cons i w ih =>
        rw [wordEval, wordEvalM, map_mul, sixteenC8H1Gens_end_mul_apply, ih, spinMu_gensP,
          Matrix.mulVec_mulVec]
  apply spinMu_injective
  rw [map_one]
  ext u
  rw [key, relsP_spec r, Matrix.one_mulVec]
  rfl

theorem stab_le_closure (h : ↥spinH)
    (hh : (h : MulAut SpinW) (Multiplicative.ofAdd (frameE (ZMod 2) 0)) =
      Multiplicative.ofAdd (frameE (ZMod 2) 0)) :
    h ∈ Subgroup.closure (Set.range gensP) := by
  obtain ⟨c, m, g, rfl⟩ := sixteenC8H1Gens_eq_sEH_of_fix h hh
  change sEH c m g ∈ sixteenC8H1Gens_S
  rw [sixteenC8H1Gens_sEH_g, sixteenC8H1Gens_sEH_cm]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (sixteenC8H1Gens_mem_c c)
    (sixteenC8H1Gens_mem_m m)) (sixteenC8H1Gens_mem_g g)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
