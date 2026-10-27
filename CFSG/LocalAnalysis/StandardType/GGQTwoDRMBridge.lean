module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBase
public import CFSG.LocalAnalysis.StandardType.GGTDAutomizer
public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxBasic
public import CFSG.LocalAnalysis.StandardType.GGQTwoPThree

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.ClassicalInvolution.Phan

section Unit

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L : Subgroup G}
  {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {m : ℕ} {ψ : Su F0 2 1 m →* G}
  {ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)}

theorem qtwoD_weylA_of_unitBase (h : QTwoUnitBase p B Bs x L ψ ε) (hm : 2 ≤ m) :
    GGWeylOfType p (CoxeterMatrix.A (m - 1)) (ggAutomizer L Bs) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨e0, he0⟩ := ggCoxeterA_mulEquivPerm n
  show GGWeylOfType p (CoxeterMatrix.A n) (ggAutomizer L Bs)
  refine ⟨e0.trans ε, fun i => ?_⟩
  rw [MulEquiv.trans_apply, he0]
  exact h.refl _ _ (Fin.castSucc_lt_succ (i := i)).ne

theorem qtwoD_x_mem_Bs {D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) : x ∈ Bs :=
  hcfg.1.1.2.1.1 hcfg.1.1.1.2.2.2.2.2.2.1.2.1

theorem qtwoD_AL_fixes_x {D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hx : x ∈ Bs) :
    ∀ a ∈ ggAutomizer L Bs, a ⟨x, hx⟩ = ⟨x, hx⟩ :=
  ggRM_AL_fixes_x (ggSecFiveRouteCfg'_of_routeCfg hcfg) hx

end Unit

section TypeInput

@[expose] def GGQTwoDRMBaseTypeInputOn (R : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (ι : Type) (M : CoxeterMatrix ι)
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)), GGQTwoDCfg p B Bs x L D J 𝒦 M e →
      ∀ (m : ℕ) (e' : Fin m ≃ ι), R m → M = (ggCoxeterMatrixD m).reindex e' →
        GGWeylOfType 3 (CoxeterMatrix.A (m - 1)) (ggAutomizer L Bs) ∨
          GGWeylOfType 3 (ggCoxeterMatrixD (m - 1)) (ggAutomizer L Bs)

@[expose] def GGQTwoDRMBaseTypeInput : Prop :=
  GGQTwoDRMBaseTypeInputOn fun m => 7 ≤ m

theorem ggQTwoDRMBaseInputOn_of_type {R : ℕ → Prop} (h : GGQTwoDRMBaseTypeInputOn R) :
    GGQTwoDRMBaseInputOn R := by
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM
  have hp : p = 3 := by
    obtain ⟨r, hr, hrc, h6⟩ := hcfg.2.2.2.2
    exact ggQTwo_p_eq_three hcfg.1 M e hcfg.2.2.2.1 hr hrc h6
  subst hp
  exact ⟨qtwoD_x_mem_Bs hcfg.1, h G 3 B Bs x L D J 𝒦 ι M e hcfg m e' hm hM,
    qtwoD_AL_fixes_x hcfg.1 (qtwoD_x_mem_Bs hcfg.1)⟩

theorem ggQTwoDRMBaseInput_of_type (h : GGQTwoDRMBaseTypeInput) : GGQTwoDRMBaseInput :=
  ggQTwoDRMBaseInputOn_of_type h

end TypeInput

end CFSG.StandardType.QTwo

end
