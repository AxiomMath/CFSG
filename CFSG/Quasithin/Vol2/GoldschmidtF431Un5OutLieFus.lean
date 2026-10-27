module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieAG
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnFusChain
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieStab

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL5

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.Quasithin.H13.Sec53F.Unit CFSG.Quasithin.H13.F431.Un
  CFSG.Quasithin CFSG.QuasithinUnique

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

include h in
theorem fusion5 (hf : 2 ≤ f) {K₀ : Subgroup (MulAut (hypPSU h 2 1))} (hinn : Pi h ≤ K₀)
    (F₂ : Subgroup (K ≃+* K)) :
    ∀ x ∈ Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) ⊥, orderOf x = 2 →
      ∃ i, (i = cj5 h (z5Y h) ∨ i = cj5 h (t5Y h)) ∧
        Relation.ReflTransGen (fun a b : MulAut (hypPSU h 2 1) =>
          a ∈ Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F₂ ∧
          b ∈ Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F₂ ∧
          ((∃ m ∈ K₀ ⊓ autStab (u5PtP h), m * a * m⁻¹ = b) ∨
           (∃ m ∈ K₀ ⊓ autStab (u5LnP h), m * a * m⁻¹ = b))) x i := by
  have := h.finite
  have : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  have hZ := u5_center_eq_bot h
  have hinj := CFSG.RankThree.PartOne.U5K.Hyp.conj_injective hZ
  rintro _ ⟨y, hy, φ, hφ, rfl⟩ hx2
  rw [Subgroup.mem_bot.1 hφ, fa5_one, mul_one] at hx2 ⊢
  have hy2 : orderOf y = 2 := by
    rw [← orderOf_injective (MulAut.conj : hypPSU h 2 1 →* MulAut (hypPSU h 2 1)) hinj y]
    exact hx2
  have key : ∀ i₀ : hypPSU h 2 1, i₀ ∈ hypProjUnitriangular h 2 1 → IsConj i₀ y →
      Relation.ReflTransGen (fun a b : MulAut (hypPSU h 2 1) =>
          a ∈ Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F₂ ∧
          b ∈ Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F₂ ∧
          ((∃ m ∈ K₀ ⊓ autStab (u5PtP h), m * a * m⁻¹ = b) ∨
           (∃ m ∈ K₀ ⊓ autStab (u5LnP h), m * a * m⁻¹ = b))) (cj5 h y) (cj5 h i₀) := by
    intro i₀ hi₀ hc
    obtain ⟨c, hc⟩ := isConj_iff.1 hc
    have hyc : c⁻¹ * y * c = i₀ := by rw [← hc]; group
    have hchain := fusion_chain_of_ag (T := hypProjUnitriangular h 2 1) (N := u5PtP h)
      (N' := u5LnP h) (u5_sylow h) (fun D hD => agY5 h hD) hy (g := c) (by rw [hyc]; exact hi₀)
    rw [hyc] at hchain
    refine Relation.ReflTransGen.lift (cj5 h) (fun a b hab => ?_) _ _ hchain
    obtain ⟨ha, hb, hm⟩ := hab
    refine ⟨cj5_mem_Ssd5 h ha, cj5_mem_Ssd5 h hb, ?_⟩
    have e : ∀ m : hypPSU h 2 1, cj5 h m * cj5 h a * (cj5 h m)⁻¹ = cj5 h (m * a * m⁻¹) := by
      intro m
      rw [cj5_mul, cj5_mul, cj5_inv]
    rcases hm with ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩
    · exact Or.inl ⟨cj5 h m, ⟨hinn ⟨m, rfl⟩, cj5_mem_autStab h hm⟩, e m⟩
    · exact Or.inr ⟨cj5 h m, ⟨hinn ⟨m, rfl⟩, cj5_mem_autStab h hm⟩, e m⟩
  rcases cls_Y hf hy2 with hc | hc
  · exact ⟨cj5 h (z5Y h), Or.inl rfl, key _ z5Y_mem_U hc⟩
  · exact ⟨cj5 h (t5Y h), Or.inr rfl, key _ t5Y_mem_U hc⟩

end CFSG.Quasithin.H13.F431.Un.OL5
