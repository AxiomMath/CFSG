module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieD
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieFld
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieStab
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModU5

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL5

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.Quasithin.H13.Sec53F.Unit CFSG.Quasithin.H13.F431.Un
  CFSG.Quasithin CFSG.QuasithinUnique

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem U_le_u5PtP : hypProjUnitriangular h 2 1 ≤ u5PtP h :=
  Subgroup.le_normalizer.trans (u5_yamStd (h := h)).le₀

theorem Ssd5_le_autStab_Pt (F : Subgroup (K ≃+* K)) :
    Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F ≤ autStab (u5PtP h) :=
  Ssd5_le_autStab h (fStab5_Pt h) (U_le_u5PtP h) F

theorem Ssd5_le_autStab_Ln (F : Subgroup (K ≃+* K)) :
    Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F ≤ autStab (u5LnP h) :=
  Ssd5_le_autStab h (fStab5_Ln h) (U_le_u5LnP (h := h)) F

theorem Ssd5_le_autStab_U (F : Subgroup (K ≃+* K)) :
    Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F ≤
      autStab (hypProjUnitriangular h 2 1) :=
  Ssd5_le_autStab h (fStab5_U h) le_rfl F

include h in
theorem Ssd5_le_normalizer_bot (F : Subgroup (K ≃+* K)) :
    Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F ≤
      Subgroup.normalizer
        ((Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) ⊥ : Subgroup _) : Set _) := by
  have key : ∀ α ∈ autStab (hypProjUnitriangular h 2 1), ∀ β ∈ Ssd5 h
      (hypProjUnitriangular h 2 1) (fStab5_U h) ⊥, α * β * α⁻¹ ∈ Ssd5 h
      (hypProjUnitriangular h 2 1) (fStab5_U h) ⊥ := by
    rintro α hα _ ⟨y, hy, φ, hφ, rfl⟩
    rw [Subgroup.mem_bot.1 hφ, fa5_one, mul_one, aut5_mul_cj5_mul_inv]
    exact cj5_mem_Ssd5 h ((hα y).1 hy)
  intro α hα
  have hα' := Ssd5_le_autStab_U h F hα
  rw [Subgroup.mem_normalizer_iff]
  intro β
  refine ⟨key α hα' β, fun hβ => ?_⟩
  have := key α⁻¹ ((autStab _).inv_mem hα') _ hβ
  simpa [mul_assoc] using this

include h in
theorem Ssd5_cyc (F : Subgroup (K ≃+* K)) :
    ∃ t₀ ∈ Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F,
      Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F =
        Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) ⊥ ⊔ Subgroup.zpowers t₀ := by
  have := fld5_isCyclic h
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥F)
  refine ⟨fa5 h (g : K ≃+* K), fa5_mem_Ssd5 h g.2, le_antisymm ?_
    (sup_le (Ssd5_mono h le_rfl bot_le) (Subgroup.zpowers_le.2 (fa5_mem_Ssd5 h g.2)))⟩
  rintro _ ⟨s, hs, φ, hφ, rfl⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨φ, hφ⟩)
  have hφk : φ = (g : K ≃+* K) ^ k := by
    have := congrArg Subtype.val hk
    simpa using this.symm
  have hfa : fa5 h ((g : K ≃+* K) ^ k) = (fa5 h (g : K ≃+* K)) ^ k := map_zpow (fieldP h) _ _
  rw [hφk, hfa]
  exact Subgroup.mul_mem_sup (cj5_mem_Ssd5 h hs) (Subgroup.zpow_mem_zpowers _ _)

include h in
theorem F2_ne_bot_of_sylow {K₀ : Subgroup (MulAut (hypPSU h 2 1))} (hinn : Pi h ≤ K₀)
    (hev : ¬ Odd (Nat.card K₀ / Nat.card (hypPSU h 2 1))) {F₂ : Subgroup (K ≃+* K)}
    (hT : IsSylowTwoOf (Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F₂) K₀) : F₂ ≠ ⊥ := by
  have := h.finite
  have : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  have : Finite (MulAut (hypPSU h 2 1)) := finite_mulAut_hyp h
  have hZ := u5_center_eq_bot h
  rintro rfl
  have hTPi : Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) ⊥ ≤ Pi h := by
    rintro _ ⟨s, -, φ, hφ, rfl⟩
    rw [Subgroup.mem_bot.1 hφ, fa5_one, mul_one]
    exact ⟨s, rfl⟩
  have hrel : 2 ∣ (Pi h).relIndex K₀ := by
    have h1 := Subgroup.card_mul_index ((Pi h).subgroupOf K₀)
    have h2 : Nat.card ((Pi h).subgroupOf K₀) = Nat.card (hypPSU h 2 1) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hinn).toEquiv]
      exact Nat.card_congr (MonoidHom.ofInjective
        (CFSG.RankThree.PartOne.U5K.Hyp.conj_injective hZ)).toEquiv.symm
    rw [h2] at h1
    have hpos : 0 < Nat.card (hypPSU h 2 1) := Nat.card_pos
    have h3 : Nat.card K₀ / Nat.card (hypPSU h 2 1) = (Pi h).relIndex K₀ := by
      rw [← h1, Nat.mul_div_cancel_left _ hpos]
      rfl
    have := Nat.not_odd_iff_even.1 hev
    rw [h3] at this
    exact even_iff_two_dvd.1 this
  apply hT.2.2
  rw [← Subgroup.relIndex, ← Subgroup.relIndex_mul_relIndex _ (Pi h) K₀ hTPi hinn]
  exact Dvd.dvd.mul_left hrel _

include h in
theorem bar5_mem_of_sylow {K₀ : Subgroup (MulAut (hypPSU h 2 1))} (hinn : Pi h ≤ K₀)
    (hev : ¬ Odd (Nat.card K₀ / Nat.card (hypPSU h 2 1))) {F₂ : Subgroup (K ≃+* K)}
    (hT : IsSylowTwoOf (Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F₂) K₀) :
    bar5 h ∈ F₂ := by
  have := h.finite
  have : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine fld5_bar_mem h ?_
  have hne := F2_ne_bot_of_sylow h hinn hev hT
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hT.2.1
  rw [card_Ssd5 h (u5_center_eq_bot h)] at hn
  obtain ⟨j, hj, hj2⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro_left _ hn)
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hne (Subgroup.card_eq_one.1 (by simpa using hj2))
  rw [hj2]
  exact dvd_pow_self 2 hj0

end CFSG.Quasithin.H13.F431.Un.OL5
