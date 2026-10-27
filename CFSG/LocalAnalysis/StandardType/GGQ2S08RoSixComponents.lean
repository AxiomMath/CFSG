module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoSixAut
public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoSixData
public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoCloseR4

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2s08_roPrime_six_components
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (M : GGQ2LDatum 3 Bs L x) (hShape : M.ShapeA)
    {labL : LargeEvenLabel} (hMark : LargeEvenMarking L (fun lab _ _ _ _ _ => lab = labL))
    (hLab : labL.tag = .twA ∧ labL.rank = 5 ∧ GGLabQTwo 3 labL)
    (hWeyl : GGQ2LabelWeyl labL M.coxeter) (f : Fin 6 → M.V) (hFrame : GGQ2S08ROFrame M f) :
    GGQ2S08ROComponents M f := by
  classical
  have hW : ∃ e : Fin labL.rank ≃ M.Λ, M.coxeter = (CoxeterMatrix.A labL.rank).reindex e := by
    simpa only [GGQ2LabelWeyl, hLab.1] using hWeyl
  have hW5 : ∃ e : Fin 5 ≃ M.Λ, M.coxeter = (CoxeterMatrix.A 5).reindex e := by
    have key : ∀ n : ℕ, n = 5 → (∃ e : Fin n ≃ M.Λ, M.coxeter = (CoxeterMatrix.A n).reindex e) →
        ∃ e : Fin 5 ≃ M.Λ, M.coxeter = (CoxeterMatrix.A 5).reindex e := by
      rintro n rfl h
      exact h
    exact key _ hLab.2.1 hW
  obtain ⟨e, he⟩ := hW5
  have hΛ : Fintype.card M.Λ = 5 := (Fintype.card_congr e).symm.trans (Fintype.card_fin 5)
  obtain ⟨c⟩ := ggQ2s08r6_exists_data hRig hS M hShape hΛ hMark hLab
  obtain ⟨w, hw⟩ := c.frame_cmp M hShape he f hFrame
  refine ⟨fun j => c.comp (w j), fun j => c.comp_le _, fun j => ?_,
    fun j => c.le_normalizer_comp _, fun j => c.four_dvd_card_automizer _,
    fun i j hij => c.comp_sup fun h => hij (w.injective h)⟩
  exact c.comp_pComponent (w j) (b := Additive.toMul (M.model.symm (f j))) (hw j).1 (hw j).2

theorem ggQ2s08_roPrime_six
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hCav : 4 ∣ Nat.card ↥(ggAutomizer J Bs))
    (M : GGQ2LDatum 3 Bs L x) (hShape : M.ShapeA)
    {labL : LargeEvenLabel} (hMark : LargeEvenMarking L (fun lab _ _ _ _ _ => lab = labL))
    (hLab : labL.tag = .twA ∧ labL.rank = 5 ∧ GGLabQTwo 3 labL)
    (hWeyl : GGQ2LabelWeyl labL M.coxeter) (f : Fin 6 → M.V) (hFrame : GGQ2S08ROFrame M f)
    (hD : ∀ g : M.V ≃ₗ[ZMod 3] M.V, GGQ2S08MonoEven f g →
      ∃ (k : G) (φ : MulAut ↥Bs), GGQ2Ind Bs k φ ∧
        k ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) ∧ ggLin (p := 3) M.model φ = g) :
    ∀ (g : G) (φ : MulAut ↥Bs), GGQ2Ind Bs g φ → GGQ2S08Mono f (ggLin (p := 3) M.model φ) →
      g ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) :=
  ggQ2s08_roClose_of_components hLB hP hS hCav M (by norm_num) f hFrame
    (ggQ2s08_roPrime_six_components hRig hS M hShape hMark hLab hWeyl f hFrame) hD

end CFSG.StandardType

end
