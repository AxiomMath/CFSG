module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieSylN

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.L5

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.U5K.Hyp
  CFSG.LocalAnalysis.EvenBN.U5 CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.Universal.Spin (upperSL2 upperSL2_add upperSL2_zero)

@[expose] def sylUpperHom (k : Type) [Field k] :
    Multiplicative k →* SpecialLinearGroup (Fin 2) k where
  toFun a := upperSL2 (Multiplicative.toAdd a)
  map_one' := upperSL2_zero
  map_mul' _ _ := upperSL2_add _ _

theorem syl_upperHom_injective {k : Type} [Field k] : Function.Injective (sylUpperHom k) := by
  intro a b hab
  have := congrArg (fun A : SpecialLinearGroup (Fin 2) k => (A : Matrix (Fin 2) (Fin 2) k) 0 1) hab
  exact Multiplicative.toAdd.injective (by simpa [sylUpperHom] using this)

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

@[expose] def sylBHom : Multiplicative h.fixedField →* hypPSU h 2 1 :=
  ((hypProj h 2 1).comp (levHom h)).comp (sylUpperHom h.fixedField)

@[expose] def sylBY : Subgroup (hypPSU h 2 1) := (sylBHom h).range

variable {h}

theorem syl_bHom_injective : Function.Injective (sylBHom h) :=
  syl_proj_levHom_injective.comp syl_upperHom_injective

theorem syl_mem_bY {x : hypPSU h 2 1} :
    x ∈ sylBY h ↔ ∃ a : h.fixedField, x = hypProj h 2 1 (levHom h (upperSL2 a)) :=
  ⟨fun ⟨a, ha⟩ => ⟨Multiplicative.toAdd a, ha.symm⟩,
    fun ⟨a, ha⟩ => ⟨Multiplicative.ofAdd a, ha.symm⟩⟩

theorem syl_bY_le_lY : sylBY h ≤ lY h := by
  intro x hx
  obtain ⟨a, rfl⟩ := syl_mem_bY.1 hx
  exact ⟨levHom h (upperSL2 a), ⟨upperSL2 a, rfl⟩, rfl⟩

theorem syl_card_bY : Nat.card (sylBY h) = 2 ^ f := by
  have := h.finite
  rw [sylBY, ← Nat.card_congr (MonoidHom.ofInjective syl_bHom_injective).toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative h.fixedField ≃ h.fixedField),
    h.card_fixedField]

theorem syl_slM_upper (a : h.fixedField) : slM (upperSL2 a) = !![1, (a : K); 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [slM_apply]

theorem syl_levHom_upper_mem_U (a : h.fixedField) :
    levHom h (upperSL2 a) ∈ hypUnitriangular h 2 1 := by
  have hu : IsUnitriangular (slM (upperSL2 a) : Matrix (Fin 2) (Fin 2) K) := by
    rw [syl_slM_upper]
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · fin_cases i <;> simp
  obtain ⟨g, hg, hgm⟩ := (exists_mem_hypUnitriangular_odd_iff (h := h) (r := 2)
    (mat (levHom h (upperSL2 a)))).2 ⟨slM (upperSL2 a), 0, 0, hu, by simp, by
      rw [oddUni_zero, mul_one, levHom_eq_lev, mat_lev, det_slM, map_one, div_one]⟩
  rwa [← mat_injective hgm]

theorem syl_bY_le_U : sylBY h ≤ hypProjUnitriangular h 2 1 := by
  intro x hx
  obtain ⟨a, rfl⟩ := syl_mem_bY.1 hx
  exact ⟨levHom h (upperSL2 a), syl_levHom_upper_mem_U a, rfl⟩

theorem syl_bY_le_cent : sylBY h ≤ Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1)) :=
  syl_bY_le_lY.trans syl_lY_le_cent

theorem syl_sY_inf_bY : sylSY h ⊓ sylBY h = ⊥ :=
  eq_bot_iff.2 (syl_sY_inf_lY (h := h) ▸ inf_le_inf_left _ syl_bY_le_lY)

theorem syl_card_sup_bY : Nat.card (sylSY h ⊔ sylBY h : Subgroup (hypPSU h 2 1)) =
    (2 ^ f) ^ 8 * 2 ^ f := by
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
    (syl_bY_le_lY.trans syl_lY_le_normalizer) (disjoint_iff.2 syl_sY_inf_bY), syl_card_sY,
    syl_card_bY]

end CFSG.Quasithin.H13.F431.Un.L5
