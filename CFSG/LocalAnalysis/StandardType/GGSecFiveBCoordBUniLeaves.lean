module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBDenseDefs
public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoHypSix
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted

section Inputs


@[expose] def GGSecFiveBCoordBUniFourInput : Prop :=
  GGInnerDiagMpInput → GGLabelRigidInput →
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ∀ e : (CoxeterMatrix.B 4).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B 4) e →
      ∀ (eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p))) (i0 : Fin 4),
        (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull 4 p →
        (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock 4 p i0 →
        GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel 4 p lab) p Bs L →
        B = Bs →
        (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
          ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) →
        ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K →
      ∀ (f : ℕ) (K : Subgroup G), GGSecFiveBCoordBUniCell p Bs L 𝒦 4 f K i0 →
        ∃ ψ : (ggU .POmegaPlus 5 f).K →* G,
          ψ.ker ≤ Subgroup.center (ggU .POmegaPlus 5 f).K ∧ ψ.range = L ⊔ K

@[expose] def GGSecFiveBCoordBUniLargeInput : Prop :=
  GGInnerDiagMpInput → GGLabelRigidInput →
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ∀ (n : ℕ) (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e → 5 ≤ n →
      ∀ (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n),
        (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p →
        (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0 →
        GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab) p Bs L →
        B = Bs →
        (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
          ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) →
        ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K →
      ∀ (f : ℕ) (K : Subgroup G), GGSecFiveBCoordBUniCell p Bs L 𝒦 n f K i0 →
        ∃ ψ : (ggU .POmegaPlus (n + 1) f).K →* G,
          ψ.ker ≤ Subgroup.center (ggU .POmegaPlus (n + 1) f).K ∧ ψ.range = L ⊔ K

theorem ggSecFiveBCoordBUniInput_of_leaves (hMp : GGInnerDiagMpInput) (hRig : GGLabelRigidInput)
    (h4 : GGSecFiveBCoordBUniFourInput) (h5 : GGSecFiveBCoordBUniLargeInput) :
    GGSecFiveBCoordBUniInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT n e hP hn eta i0 hJ hA hI hB hN hG f K hc
  rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | h5n
  · exact h4 hMp hRig G p B Bs x L D J 𝒦 hR hT e hP eta i0 hJ hA hI hB hN hG f K hc
  · exact h5 hMp hRig G p B Bs x L D J 𝒦 hR hT n e hP h5n eta i0 hJ hA hI hB hN hG f K hc

end Inputs

end CFSG.StandardType

end
