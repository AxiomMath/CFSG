module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoNInner
public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoNData
public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoCloseR4
public import CFSG.LocalAnalysis.StandardType.GGQ2S08FullCoords

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2s08rN_rootMap_surjective {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) {n : ℕ} (e : Fin n ≃ M.Λ)
    (he : M.coxeter = (CoxeterMatrix.A n).reindex e) (h3 : ¬ 3 ∣ n + 1) :
    Function.Surjective M.rootMap := by
  refine ggQ2LDatum_rootMap_surjective M
    (isUnit_cartan_det_of_reindex M e (CartanMatrix.A n) (ggQ2_cartan_A e he M.isCartan) ?_)
  rw [show (CartanMatrix.A n).map (Int.castRingHom (ZMod 3)) =
      (Int.castRingHom (ZMod 3)).mapMatrix (CartanMatrix.A n) from rfl,
    ← RingHom.map_det (Int.castRingHom (ZMod 3)) (CartanMatrix.A n), CartanMatrix.A_det,
    isUnit_iff_ne_zero]
  intro hz
  have hz' : ((n + 1 : ℤ) : ZMod 3) = 0 := by simpa using hz
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz'
  exact h3 (by exact_mod_cast hz')

theorem ggQ2s08_roN_components
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (M : GGQ2LDatum 3 Bs L x) {n : ℕ} (hn : 6 ≤ n)
    (h3 : ¬ 3 ∣ n + 1)
    {labL : LargeEvenLabel} (hMark : LargeEvenMarking L (fun lab _ _ _ _ _ => lab = labL))
    (hLab : labL.tag = .twA ∧ labL.rank = n ∧ GGLabQTwo 3 labL)
    (hWeyl : GGQ2LabelWeyl labL M.coxeter) (f : Fin (n + 1) → M.V)
    (hFrame : GGQ2S08ROFrame M f) :
    GGQ2S08ROComponents M f := by
  classical
  have hW : ∃ e : Fin labL.rank ≃ M.Λ, M.coxeter = (CoxeterMatrix.A labL.rank).reindex e := by
    simpa only [GGQ2LabelWeyl, hLab.1] using hWeyl
  have hWn : ∃ e : Fin n ≃ M.Λ, M.coxeter = (CoxeterMatrix.A n).reindex e := by
    have key : ∀ m : ℕ, m = n → (∃ e : Fin m ≃ M.Λ, M.coxeter = (CoxeterMatrix.A m).reindex e) →
        ∃ e : Fin n ≃ M.Λ, M.coxeter = (CoxeterMatrix.A n).reindex e := by
      rintro m rfl h
      exact h
    exact key _ hLab.2.1 hW
  obtain ⟨e, he⟩ := hWn
  obtain ⟨c⟩ := ggQ2s08rN_exists_data hRig hn h3 hS M hMark hLab f hFrame
  obtain ⟨w, hw⟩ := c.frame_cmp M (ggQ2s08rN_rootMap_surjective M e he h3) he f hFrame
  refine ⟨fun j => c.comp (w j), fun j => c.comp_le _, fun j => ?_,
    fun j => c.le_normalizer_comp _, fun j => c.four_dvd_card_automizer _,
    fun i j hij => c.comp_sup fun h => hij (w.injective h)⟩
  exact c.comp_pComponent (w j) (b := Additive.toMul (M.model.symm (f j))) (hw j).1 (hw j).2

theorem ggQ2s08_roN
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hCav : 4 ∣ Nat.card ↥(ggAutomizer J Bs))
    (M : GGQ2LDatum 3 Bs L x) {n : ℕ} (hn : 6 ≤ n) (h3 : ¬ 3 ∣ n + 1)
    {labL : LargeEvenLabel} (hMark : LargeEvenMarking L (fun lab _ _ _ _ _ => lab = labL))
    (hLab : labL.tag = .twA ∧ labL.rank = n ∧ GGLabQTwo 3 labL)
    (hWeyl : GGQ2LabelWeyl labL M.coxeter) (f : Fin (n + 1) → M.V)
    (hFrame : GGQ2S08ROFrame M f)
    (hD : ∀ g : M.V ≃ₗ[ZMod 3] M.V, GGQ2S08MonoEven f g →
      ∃ (k : G) (φ : MulAut ↥Bs), GGQ2Ind Bs k φ ∧
        k ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) ∧ ggLin (p := 3) M.model φ = g) :
    ∀ (g : G) (φ : MulAut ↥Bs), GGQ2Ind Bs g φ → GGQ2S08Mono f (ggLin (p := 3) M.model φ) →
      g ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) :=
  ggQ2s08_roClose_of_components hLB hP hS hCav M (by omega) f hFrame
    (ggQ2s08_roN_components hRig hS M hn h3 hMark hLab hWeyl f hFrame) hD

end CFSG.StandardType

end
