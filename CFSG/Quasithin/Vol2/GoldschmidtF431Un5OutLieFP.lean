module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieTG
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieTH
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieWBB
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieWCC
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieNorm
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieNst
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieSyl

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL5

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.Quasithin.H13.Sec53F.Unit CFSG.LocalAnalysis.EvenBN.U5
  CFSG.Quasithin.H13.F431.Un CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem Ssd5_std (F₂ : Subgroup (K ≃+* K)) :
    Uh h ≤ Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F₂ ∧
      ∀ τ ∈ Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F₂,
        ∃ u ∈ Uh h, ∃ σ : K ≃+* K, τ = u * fieldP h σ := by
  refine ⟨?_, ?_⟩
  · rw [← Ssd5_bot_eq_Uh h]
    exact Ssd5_mono h le_rfl bot_le
  · rintro _ ⟨s, hs, φ, -, rfl⟩
    refine ⟨cj5 h s, ?_, φ, rfl⟩
    rw [← Ssd5_bot_eq_Uh h]
    exact cj5_mem_Ssd5 h hs

include h in
theorem fp5_Tf_lt_z (hf : 2 ≤ f) (F₂ : Subgroup (K ≃+* K)) (hbar : bar5 h ∈ F₂) :
    Nat.card ↥(spTf (Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F₂) (fa5 h (bar5 h))) <
      Nat.card ↥(Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F₂ ⊓
        Subgroup.centralizer ({cj5 h (z5Y h)} : Set (MulAut (hypPSU h 2 1)))) :=
  un5_Tf_lt_z h hf (Ssd5_std h F₂).1 (Ssd5_std h F₂).2 (fa5_mem_Ssd5 h hbar)

include h in
theorem fp5_Tf_lt_t (hf : 2 ≤ f) (F₂ : Subgroup (K ≃+* K)) (hbar : bar5 h ∈ F₂) :
    Nat.card ↥(spTf (Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F₂) (fa5 h (bar5 h))) <
      Nat.card ↥(Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F₂ ⊓
        Subgroup.centralizer ({cj5 h (t5Y h)} : Set (MulAut (hypPSU h 2 1)))) :=
  un5_Tf_lt_t h hf (Ssd5_std h F₂).1 (Ssd5_std h F₂).2 (fa5_mem_Ssd5 h hbar)

include h in
theorem fp5_Sylow_Tf (hf : 2 ≤ f) {K₀ : Subgroup (MulAut (hypPSU h 2 1))} (hinn : Pi h ≤ K₀)
    (F₂ : Subgroup (K ≃+* K)) (hbar : bar5 h ∈ F₂)
    (hT : IsSylowTwoOf (Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F₂) K₀) :
    IsSylowTwoOf (spTf (Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F₂) (fa5 h (bar5 h)))
      (Subgroup.centralizer ({fa5 h (bar5 h)} : Set (MulAut (hypPSU h 2 1))) ⊓
        (K₀ ⊓ autStab (u5PtP h))) :=
  un5_Sylow_Tf h hf (Ssd5_std h F₂).1 (Ssd5_std h F₂).2 (fa5_mem_Ssd5 h hbar) hinn hT
    (le_inf hT.1 (Ssd5_le_autStab_Pt h F₂)) inf_le_left

include h in
theorem fp5_W_ne (hf : 2 ≤ f) {K₀ : Subgroup (MulAut (hypPSU h 2 1))} (hinn : Pi h ≤ K₀)
    (F₂ : Subgroup (K ≃+* K)) (hbar : bar5 h ∈ F₂) :
    ∃ x ∈ spWf (Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F₂) (fa5 h (bar5 h)),
      x ∈ centerOf (perfectCore (K₀ ⊓ autStab (u5PtP h))) ∧ x ≠ 1 := by
  obtain ⟨x, hx, hxZ, hx1⟩ := un5_W_ne h hf (Ssd5_std h F₂).1 (Ssd5_std h F₂).2
    (fa5_mem_Ssd5 h hbar)
  exact ⟨x, hx, by rw [centerOf_perfectCore_N5 h hf hinn]; exact hxZ, hx1⟩

include h in
theorem fp5_W_cls (hf : 2 ≤ f) {K₀ : Subgroup (MulAut (hypPSU h 2 1))} (hinn : Pi h ≤ K₀)
    (F₂ : Subgroup (K ≃+* K)) (hbar : bar5 h ∈ F₂) {y : MulAut (hypPSU h 2 1)}
    (hy : y ∈ spWf (Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F₂) (fa5 h (bar5 h)))
    (hk : ∃ k : MulAut (hypPSU h 2 1), k * cj5 h (z5Y h) * k⁻¹ = y) :
    y ∈ centerOf (perfectCore (K₀ ⊓ autStab (u5PtP h))) := by
  rw [centerOf_perfectCore_N5 h hf hinn]
  exact un5_W_cls h hf (Ssd5_std h F₂).1 (Ssd5_std h F₂).2 (fa5_mem_Ssd5 h hbar) y hy hk

end CFSG.Quasithin.H13.F431.Un.OL5
