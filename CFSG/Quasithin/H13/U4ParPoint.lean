module

public import CFSG.Quasithin.H13.U4ParLevi
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherParabolicData

public section

namespace CFSG.Quasithin.H13.U4Par

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

noncomputable abbrev parP : Subgroup (hypSU h 2 0) :=
  UnitaryHigher.isoStabilizer h 2 0 (hypFlag h 2 0 1)

theorem inv_apply (g : hypSU h 2 0) (a b : Ix) :
    (((g⁻¹ : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) a b =
      h.bar (((g : GL Ix K) : Matrix Ix Ix K) (hypPartner b) (hypPartner a)) := by
  have hg := (mem_gramSU.mp g.2).1
  have hleft : hypGram 2 0 K * ((((g : GL Ix K) : Matrix Ix Ix K)).map h.bar)ᵀ *
      hypGram 2 0 K * ((g : GL Ix K) : Matrix Ix Ix K) = 1 := by
    rw [Matrix.mul_assoc (hypGram 2 0 K * _), Matrix.mul_assoc (hypGram 2 0 K),
      ← Matrix.mul_assoc _ (hypGram 2 0 K), hg, hypGram_mul_self]
  have hinv : (((g⁻¹ : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) =
      hypGram 2 0 K * ((((g : GL Ix K) : Matrix Ix Ix K)).map h.bar)ᵀ * hypGram 2 0 K := by
    rw [Subgroup.coe_inv]
    exact Units.inv_eq_of_mul_eq_one_left hleft
  rw [hinv, mul_hypGram_apply, hypGram_mul_apply, transpose_apply, map_apply]

theorem row_if1_of_col (g : hypSU h 2 0)
    (hcol : ∀ a, a ≠ ie1 → ((g : GL Ix K) : Matrix Ix Ix K) a ie1 = 0) :
    (∀ b, b ≠ if1 → ((g : GL Ix K) : Matrix Ix Ix K) if1 b = 0) ∧
      h.bar (((g : GL Ix K) : Matrix Ix Ix K) ie1 ie1) *
        ((g : GL Ix K) : Matrix Ix Ix K) if1 if1 = 1 := by
  have hg := (mem_gramSU.mp g.2).1
  have h2 := hcol ie2 ie2_ne_ie1
  have h3 := hcol if1 if1_ne_ie1
  have h4 := hcol if2 if2_ne_ie1
  have key : ∀ b, h.bar (((g : GL Ix K) : Matrix Ix Ix K) ie1 ie1) *
      ((g : GL Ix K) : Matrix Ix Ix K) if1 b = hypGram 2 0 K ie1 b := by
    intro b
    have := congrFun (congrFun hg ie1) b
    rw [mul_apply, sum_ix] at this
    simp only [mul_hypGram_apply, transpose_apply, map_apply, hypPartner_ie1, hypPartner_ie2,
      hypPartner_if1, hypPartner_if2, h2, h3, h4, map_zero, zero_mul, zero_add, add_zero]
      at this
    exact this
  have hdiag : h.bar (((g : GL Ix K) : Matrix Ix Ix K) ie1 ie1) *
      ((g : GL Ix K) : Matrix Ix Ix K) if1 if1 = 1 := by
    rw [key, hypGram_apply, hypPartner_ie1]
    simp
  refine ⟨fun b hb => ?_, hdiag⟩
  have hne : h.bar (((g : GL Ix K) : Matrix Ix Ix K) ie1 ie1) ≠ 0 :=
    left_ne_zero_of_mul_eq_one hdiag
  have := key b
  rw [hypGram_apply, hypPartner_ie1] at this
  simp only [hb, ite_false] at this
  exact (mul_eq_zero.mp this).resolve_left hne

theorem col_inv (g : hypSU h 2 0)
    (hcol : ∀ a, a ≠ ie1 → ((g : GL Ix K) : Matrix Ix Ix K) a ie1 = 0) :
    ∀ a, a ≠ ie1 → (((g⁻¹ : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) a ie1 = 0 := by
  intro a ha
  rw [inv_apply, hypPartner_ie1]
  have hpa : hypPartner a ≠ if1 := by
    intro hp
    apply ha
    rw [← hypPartner_hypPartner a, hp, hypPartner_if1]
  rw [(row_if1_of_col h g hcol).1 _ hpa, map_zero]

theorem mem_parP_iff (g : hypSU h 2 0) :
    g ∈ parP h ↔ ∀ a, a ≠ ie1 → ((g : GL Ix K) : Matrix Ix Ix K) a ie1 = 0 := by
  have hF : hypFlag h 2 0 1 = posFlag 2 0 K 1 := hypFlag_eq_posFlag h (by norm_num) (by norm_num)
  have hpos' : ∀ a : Ix, 1 ≤ fullPos a → a ≠ ie1 := by
    rintro a ha rfl
    simp at ha
  have hpos : ∀ a : Ix, a ≠ ie1 → 1 ≤ fullPos a := by
    intro a ha
    rcases ix_cases a with rfl | rfl | rfl | rfl
    · exact absurd rfl ha
    all_goals simp
  have hmem : ∀ (M : Matrix Ix Ix K), (∀ a, a ≠ ie1 → M a ie1 = 0) →
      ∀ v ∈ posFlag 2 0 K 1, M *ᵥ v ∈ posFlag 2 0 K 1 := by
    intro M hM v hv a ha
    rw [mulVec, dotProduct, sum_ix]
    have h2 : v ie2 = 0 := hv ie2 (by simp)
    have h3 : v if1 = 0 := hv if1 (by simp)
    have h4 : v if2 = 0 := hv if2 (by simp)
    rw [h2, h3, h4, hM a (hpos' a ha)]
    ring
  rw [UnitaryHigher.mem_isoStabilizer, hF]
  constructor
  · intro hg a ha
    have he1 : (Pi.single ie1 1 : Ix → K) ∈ posFlag 2 0 K 1 := by
      intro b hb
      simp [hpos' b hb]
    have h1 : (g : GL Ix K) • (Pi.single ie1 1 : Ix → K) ∈ (g : GL Ix K) • posFlag 2 0 K 1 :=
      Submodule.smul_mem_pointwise_smul _ _ _ he1
    rw [← Subgroup.smul_def, hg] at h1
    have h2 := h1 a (hpos a ha)
    change (((g : GL Ix K) : Matrix Ix Ix K) *ᵥ Pi.single ie1 1) a = 0 at h2
    rwa [mulVec_single_one, col_apply] at h2
  · intro hcol
    rw [Subgroup.smul_def]
    exact smul_eq_of_mulVec_mem (hmem _ hcol) (hmem _ (col_inv h g hcol))

@[expose] noncomputable def chi (g : hypSU h 2 0) : K := ((g : GL Ix K) : Matrix Ix Ix K) ie1 ie1

@[expose] noncomputable def rho (g : hypSU h 2 0) : Matrix (Fin 2) (Fin 2) K :=
  !![((g : GL Ix K) : Matrix Ix Ix K) ie2 ie2, ((g : GL Ix K) : Matrix Ix Ix K) ie2 if2;
    ((g : GL Ix K) : Matrix Ix Ix K) if2 ie2, ((g : GL Ix K) : Matrix Ix Ix K) if2 if2]

theorem chi_mul {g g' : hypSU h 2 0} (hg' : g' ∈ parP h) :
    chi h (g * g') = chi h g * chi h g' := by
  have hc := (mem_parP_iff h g').mp hg'
  rw [chi, coe_mul_hypSU, mul_apply, sum_ix, hc ie2 ie2_ne_ie1, hc if1 if1_ne_ie1,
    hc if2 if2_ne_ie1, chi, chi]
  ring

theorem rho_mul {g g' : hypSU h 2 0} (hg : g ∈ parP h) (hg' : g' ∈ parP h) :
    rho h (g * g') = rho h g * rho h g' := by
  have hc := (mem_parP_iff h g).mp hg
  have hr := (row_if1_of_col h g' ((mem_parP_iff h g').mp hg')).1
  have c2 := hc ie2 ie2_ne_ie1
  have c4 := hc if2 if2_ne_ie1
  have r2 := hr ie2 ie2_ne_if1
  have r4 := hr if2 if2_ne_if1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [rho, coe_mul_hypSU, mul_apply, sum_ix, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, c2, c4, r2, r4, zero_mul, mul_zero, zero_add,
      add_zero, Fin.zero_eta, Fin.isValue, Fin.mk_one]

theorem chi_one : chi h 1 = 1 := by simp [chi, one_apply]

theorem rho_one : rho h 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rho, one_apply]

theorem mem_radQ_of_chi_rho {g : hypSU h 2 0} (hg : g ∈ parP h) (hchi : chi h g = 1)
    (hrho : rho h g = 1) : g ∈ radQ h := by
  have := h.charP
  have hcol := (mem_parP_iff h g).mp hg
  obtain ⟨hrow, hdiag⟩ := row_if1_of_col h g hcol
  have c2 := hcol ie2 ie2_ne_ie1
  have c3 := hcol if1 if1_ne_ie1
  have c4 := hcol if2 if2_ne_ie1
  have r1 := hrow ie1 ie1_ne_if1
  have r2 := hrow ie2 ie2_ne_if1
  have r4 := hrow if2 if2_ne_if1
  unfold chi at hchi
  have p00 := congrFun (congrFun hrho 0) 0
  have p01 := congrFun (congrFun hrho 0) 1
  have p10 := congrFun (congrFun hrho 1) 0
  have p11 := congrFun (congrFun hrho 1) 1
  simp only [rho, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at p00 p01 p10 p11
  have hgram := (mem_gramSU.mp g.2).1
  have entry : ∀ i j, ∑ k, h.bar ((((g : GL Ix K) : Matrix Ix Ix K)) (hypPartner k) i) *
      ((g : GL Ix K) : Matrix Ix Ix K) k j = hypGram 2 0 K i j := by
    intro i j
    have := congrFun (congrFun hgram i) j
    rw [mul_apply] at this
    simpa only [mul_hypGram_apply, transpose_apply, map_apply] using this
  clear hgram hrho hcol hrow
  rw [mem_radQ]
  generalize ((g : GL Ix K) : Matrix Ix Ix K) = G at *
  have hff : G if1 if1 = 1 := by
    rw [hchi, map_one, one_mul] at hdiag
    exact hdiag
  have g12 : G ie1 ie2 = h.bar (G if2 if1) := by
    have := entry ie2 if1
    rw [sum_ix, hypGram_apply] at this
    simp [r2, p10, p00, hff] at this
    have e : h.bar (G ie1 ie2) = G if2 if1 := by grind
    rw [← e, h.bar_bar]
  have g14 : G ie1 if2 = h.bar (G ie2 if1) := by
    have := entry if2 if1
    rw [sum_ix, hypGram_apply] at this
    simp [r4, p01, p11, hff] at this
    have e : h.bar (G ie1 if2) = G ie2 if1 := by grind
    rw [← e, h.bar_bar]
  have hadm : SAdm h (G ie2 if1) (G if2 if1) (G ie1 if1) := by
    have := entry if1 if1
    rw [sum_ix, hypGram_apply] at this
    simp [hff] at this
    unfold SAdm
    grind
  refine ⟨G ie2 if1, G if2 if1, G ie1 if1, hadm, ?_⟩
  ext i j
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [sMat_apply, one_apply, c2, c3, c4, r2, r4, hchi, hff, p00, p01, p10, p11, g12, g14]

theorem radQ_le_parP : radQ h ≤ parP h := by
  rintro g ⟨x, y, c, -, hg⟩
  rw [mem_parP_iff]
  intro a ha
  rw [hg, sMat_apply, one_apply_ne ha]
  rcases ix_cases a with rfl | rfl | rfl | rfl
  · exact absurd rfl ha
  all_goals simp

theorem levHom_le_parP : (levHom h).range ≤ parP h := by
  rintro _ ⟨A, rfl⟩
  rw [mem_parP_iff]
  intro a ha
  rw [coe_levHom, levMat_apply]
  rcases ix_cases a with rfl | rfl | rfl | rfl
  · exact absurd rfl ha
  all_goals simp

theorem chi_mul_inv {g : hypSU h 2 0} (hg : g ∈ parP h) : chi h g * chi h g⁻¹ = 1 := by
  rw [← chi_mul h ((parP h).inv_mem hg), mul_inv_cancel, chi_one]

theorem rho_mul_inv {g : hypSU h 2 0} (hg : g ∈ parP h) : rho h g * rho h g⁻¹ = 1 := by
  rw [← rho_mul h hg ((parP h).inv_mem hg), mul_inv_cancel, rho_one]

theorem chi_rho_of_mem_radQ {g : hypSU h 2 0} (hg : g ∈ radQ h) : chi h g = 1 ∧ rho h g = 1 := by
  obtain ⟨x, y, c, -, hgm⟩ := hg
  refine ⟨by simp [chi, hgm, sMat_apply, one_apply], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rho, hgm, sMat_apply, one_apply]

theorem parP_le_normalizer_radQ : parP h ≤ Subgroup.normalizer (radQ h : Set (hypSU h 2 0)) := by
  have key : ∀ p ∈ parP h, ∀ g ∈ radQ h, p * g * p⁻¹ ∈ radQ h := by
    intro p hp g hg
    have hgP := radQ_le_parP h hg
    have hpi := (parP h).inv_mem hp
    have hm : p * g * p⁻¹ ∈ parP h := (parP h).mul_mem ((parP h).mul_mem hp hgP) hpi
    obtain ⟨hchig, hrhog⟩ := chi_rho_of_mem_radQ h hg
    refine mem_radQ_of_chi_rho h hm ?_ ?_
    · rw [chi_mul h hpi, chi_mul h hgP, hchig, mul_one, chi_mul_inv h hp]
    · rw [rho_mul h ((parP h).mul_mem hp hgP) hpi, rho_mul h hp hgP, hrhog, mul_one,
        rho_mul_inv h hp]
  intro p hp
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · exact key p hp g
  · intro hg
    have := key p⁻¹ ((parP h).inv_mem hp) _ hg
    simpa [mul_assoc] using this

end CFSG.Quasithin.H13.U4Par
