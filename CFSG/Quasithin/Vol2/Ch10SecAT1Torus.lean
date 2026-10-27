module

public import CFSG.Quasithin.Vol2.Ch10SecA1012P5VecAux
public import CFSG.Quasithin.Vol2.Ch10SecANatCoord

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative commutatorElement

section Matrices

variable {F : Type} [Field F]

theorem diagSL_pow_apply {μ : F} (hμ : μ ≠ 0) (m : ℕ) :
    ((diagSL hμ ^ m : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 =
      μ ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, ih,
      coe_diagSL]
    simp [pow_succ]

theorem diagSL_conj_iff {μ : F} (hμ : μ ≠ 0) (X : Matrix.SpecialLinearGroup (Fin 2) F) :
    (∃ b, X = unipSL b) ↔ ∃ b, diagSL hμ * X * (diagSL hμ)⁻¹ = unipSL b := by
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨μ ^ 2 * b, diagSL_conj hμ b⟩
  · rintro ⟨b, hb⟩
    refine ⟨μ⁻¹ ^ 2 * b, ?_⟩
    have hX : X = (diagSL hμ)⁻¹ * unipSL b * diagSL hμ := by rw [← hb]; group
    rw [hX]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_unipSL, coe_diagSL, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, hμ]
    field_simp

end Matrices

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem NatCoord.mem_normalizer [IsMulCommutative ↥(fsuUL T L I)] {F : Type} [Field F]
    (c : NatCoord T L I F) {δ : Matrix.SpecialLinearGroup (Fin 2) F}
    (hδ : ∀ X, (∃ b, X = unipSL b) ↔ ∃ b, δ * X * δ⁻¹ = unipSL b) :
    ((c.eρ (c.g⁻¹ * δ * c.g) : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) ∈
      Subgroup.normalizer (autOn (T ⊓ L) (fsuUL T L I) : Set (MulAut ↥(fsuUL T L I))) := by
  set γ := c.g⁻¹ * δ * c.g with hγ
  set φ : MulAut ↥(fsuUL T L I) :=
    ((c.eρ γ : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) with hφ
  have hφL : φ ∈ autOn L (fsuUL T L I) := (c.eρ γ).2
  have hle : autOn (T ⊓ L) (fsuUL T L I) ≤ autOn L (fsuUL T L I) := A4.autOn_mono inf_le_right
  rw [Subgroup.mem_normalizer_iff]
  intro p
  by_cases hpL : p ∈ autOn L (fsuUL T L I)
  · set γp := c.eρ.symm ⟨p, hpL⟩ with hγpdef
    have hγp : ((c.eρ γp : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) = p := by
      rw [hγpdef, MulEquiv.apply_symm_apply]
    have hconj : φ * p * φ⁻¹ =
        ((c.eρ (γ * γp * γ⁻¹) : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) := by
      rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hγp]
    rw [hconj, ← hγp, c.unip, c.unip, hδ]
    have he : c.g * (γ * γp * γ⁻¹) * c.g⁻¹ = δ * (c.g * γp * c.g⁻¹) * δ⁻¹ := by
      rw [hγ]
      group
    rw [he]
  · constructor
    · intro hp
      exact absurd (hle hp) hpL
    · intro hp
      apply absurd _ hpL
      have h1 := (autOn L (fsuUL T L I)).mul_mem
        ((autOn L (fsuUL T L I)).mul_mem ((autOn L (fsuUL T L I)).inv_mem hφL) (hle hp)) hφL
      simpa [mul_assoc] using h1

theorem mem_T_of_forall_conj_eq
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Ch10.Hyp10 G T L I) {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    {y : G} (hyL : y ∈ L) (hU : ∀ u ∈ fsuUL T L I, y * u * y⁻¹ = u) : y ∈ T := by
  obtain ⟨_, -, -, ha, -⟩ := hyp.three
  have hV := (ha t ht htn).1
  have hUC := conjugate_fsuUL_le_centralizer h37 h38 hyp ht htn
  have hyL0 := le_fsuL0 T L hyL
  have hcomm : ∀ u, y * u * y⁻¹ = u → u ∈ Subgroup.centralizer ({y} : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact (mul_inv_eq_iff_eq_mul.mp hu)
  have hle : fsuVM T L I ≤ Subgroup.centralizer ({y} : Set G) := by
    rw [← hV]
    refine sup_le (sup_le (fun u hu => hcomm u (hU u hu)) (fun u hu => hcomm u ?_))
      fun c hc => hcomm c ?_
    · rw [Subgroup.mem_centralizer_iff.mp (hUC hu) y hyL, mul_inv_cancel_right]
    · rw [Subgroup.mem_centralizer_iff.mp hc.2 y hyL0, mul_inv_cancel_right]
  have hyC : y ∈ fsuL0 T L ⊓ Subgroup.centralizer (fsuVM T L I : Set G) := by
    refine ⟨hyL0, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp (hle hv) y rfl).symm
  exact (pCoreOf_fsuL0_le_T0 hyp.fsu.sylow (fsuL0_inf_centralizer_le h37 h38 hyp hyC)).1

theorem mem_normalizer_inf_conjugate (h37 : Vol2Native.A37ForSQTKCat) (hyp : Ch10.Hyp10 G T L I)
    {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) {l : G} (hl : l ∈ L) :
    l ∈ Subgroup.normalizer ((T ⊓ CFSG.conjugate L t : Subgroup G) : Set G) := by
  have hloc := hyp.fsu.maximal.1
  have hcomm := commutator_conjugate_le h37 hyp ht htn
  have hOT : pCoreOf 2 L ≤ T := fun x hx => (pCoreOf_fsuL0_le_T0 hyp.fsu.sylow
    (sup_pCoreOf_le hloc ht (Subgroup.mem_sup_left hx))).1
  have hLLt := le_normalizer_conjugate hloc (le_fsuM T L ht)
  have key : ∀ k ∈ L, ∀ s ∈ T ⊓ CFSG.conjugate L t, k * s * k⁻¹ ∈ T ⊓ CFSG.conjugate L t := by
    intro k hk s hs
    refine ⟨?_, (Subgroup.mem_normalizer_iff.mp (hLLt hk) s).mp hs.2⟩
    have h1 : ⁅k, s⁆ ∈ T := hOT (hcomm (Subgroup.commutator_mem_commutator hk hs.2)).1
    have h2 := T.mul_mem h1 hs.1
    rwa [commutatorElement_def, inv_mul_cancel_right] at h2
  rw [Subgroup.mem_normalizer_iff]
  intro s
  refine ⟨key l hl s, fun h => ?_⟩
  have := key l⁻¹ (L.inv_mem hl) _ h
  simpa [mul_assoc] using this

end CFSG.Quasithin.Vol2.Ch10.SecA
