module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormCenterless
public import CFSG.LocalAnalysis.StandardType.GGNbrTableBE6Three

public section

namespace CFSG.StandardType.E6ThreeWNorm

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three

theorem ggWNormConcl_of_e6ThreeWeylModel {L' : Type} [Group L'] [Finite L']
    {Z : Subgroup L'} {A : Subgroup (MulAut L')} (hM : GGE6ThreeWeylModel Z A)
    {Λ V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥A ≃+ V) (φ : Λ → MulAut ↥A) (h : Λ → V) (α : Λ → Module.Dual (ZMod 3) V)
    (hgen : ggAutomizer (MulAut.conj : L' →* MulAut L').range A =
      Subgroup.closure (Set.range φ))
    {s : MulAut ↥A} (hs : s ∈ ggInduced (⊤ : Subgroup (MulAut L')) A) :
    GGWNormConcl ι φ h α s := by
  classical
  obtain ⟨Φ, T, w, hD⟩ := hM.exists_data
  obtain ⟨β, -, hβN, hβs⟩ := hs
  obtain ⟨c, u, hc0, hcu⟩ := hD.full β hβN
  obtain ⟨t, htW, htact⟩ : ∃ t ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A,
      ∀ a : A, Multiplicative.toAdd (Φ (t a)) = adAct .E6 3 u (Multiplicative.toAdd (Φ a)) :=
    ⟨_, hD.toActData.reflGen_le_automizer (hD.toActData.weylAut_mem u),
      hD.toActData.weylAut_act u⟩
  have htH : ggLin (p := 3) ι t ∈ ggHL ι φ h α :=
    ggLin_mem_ggHL_of_closure ι φ h α hgen htW
  have hst : ∀ a : A, Multiplicative.toAdd (Φ (s a)) = c • Multiplicative.toAdd (Φ (t a)) := by
    intro a
    rw [htact a]
    exact hcu a (s a) (hβs a)
  have hc : c = 1 ∨ c = -1 :=
    (show ∀ c : ZMod 3, c ≠ 0 → c = 1 ∨ c = -1 by decide) c hc0
  rcases hc with rfl | rfl
  ·
    have hs_eq : s = t := by
      refine MulEquiv.ext fun a => hD.injective ?_
      apply Multiplicative.toAdd.injective
      rw [hst a, one_smul]
    have hlin : ggLin (p := 3) ι s = ggLin (p := 3) ι t := by rw [hs_eq]
    refine ⟨⟨1, ggLin (p := 3) ι t, htH, fun v => ?_⟩, fun _ => ?_⟩
    · rw [hlin, Units.val_one, one_smul]
    · rw [hlin]
      exact htH
  ·
    have hs_eq : ∀ a : A, s a = (t a)⁻¹ := by
      intro a
      apply hD.injective
      apply Multiplicative.toAdd.injective
      rw [hst a, map_inv, toAdd_inv, neg_one_smul]
    have hlin : ∀ v, ggLin (p := 3) ι s v = -ggLin (p := 3) ι t v := by
      intro v
      rw [ggLin_apply (p := 3), ggLin_apply (p := 3), hs_eq, ofMul_inv, map_neg]
    refine ⟨⟨-1, ggLin (p := 3) ι t, htH, fun v => ?_⟩, fun _ => ?_⟩
    · rw [hlin, Units.val_neg, Units.val_one, neg_one_smul]
    · have heq : ggLin (p := 3) ι s = LinearEquiv.neg (ZMod 3) * ggLin (p := 3) ι t := by
        apply LinearEquiv.ext
        intro v
        rw [hlin, LinearEquiv.mul_apply]
        rfl
      rw [heq]
      exact Subgroup.mul_mem _
        (Subgroup.subset_closure (Or.inl (Or.inr (Set.mem_singleton _)))) htH

theorem ggWNormConcl_of_modelSCr {R : Type} [Group R] {I : Set (MulAut R)}
    (hM : GGE6ThreeModelSCr R I) {L' : Type} [Group L'] [Finite L'] {ψ : L' →* R}
    {A : Subgroup (MulAut L')} (hTB : GGTorusTBGroup 3 5 R I L' ψ A)
    {Λ V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥A ≃+ V) (φ : Λ → MulAut ↥A) (h : Λ → V) (α : Λ → Module.Dual (ZMod 3) V)
    (hgen : ggAutomizer (MulAut.conj : L' →* MulAut L').range A =
      Subgroup.closure (Set.range φ))
    {s : MulAut ↥A} (hs : s ∈ ggInduced (⊤ : Subgroup (MulAut L')) A) :
    GGWNormConcl ι φ h α s := by
  obtain ⟨hψ, hker, hperf, hA, hAI, h5, -, hsc⟩ := hTB
  exact ggWNormConcl_of_e6ThreeWeylModel (hM L' ψ hψ hker hperf A hA hAI h5 hsc) ι φ h α hgen hs

theorem ggWNormConcl_five_recipe_E6 {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) (h3 : 3 ∣ 2 ^ n - 1) {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* TableBExc.RecipeGroup .E6 K} {A : Subgroup (MulAut L')}
    (hTB : GGTorusTBGroup 3 5 (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K) L' ψ A)
    {Λ V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥A ≃+ V) (φ : Λ → MulAut ↥A) (h : Λ → V) (α : Λ → Module.Dual (ZMod 3) V)
    (hgen : ggAutomizer (MulAut.conj : L' →* MulAut L').range A =
      Subgroup.closure (Set.range φ))
    {s : MulAut ↥A} (hs : s ∈ ggInduced (⊤ : Subgroup (MulAut L')) A) :
    GGWNormConcl ι φ h α s :=
  ggWNormConcl_of_modelSCr (E6ThreeModel.e6ThreeModel_holds.1 K n hn hK h3) hTB ι φ h α hgen hs

end CFSG.StandardType.E6ThreeWNorm
