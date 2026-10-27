module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBOffQTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpSpDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank

section Inputs

@[expose] def GGSecFiveBCoordBOffSpSpOn (S : ℕ → ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ∀ (n : ℕ) (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e → 4 ≤ n →
      ∀ (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n),
        (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p →
        (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0 →
        GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab ∧ S n p lab) p Bs L →
        B = Bs →
        (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
          ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) →
        ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K →
        (¬ ∃ (f : ℕ) (K : Subgroup G), GGSecFiveBCoordBSpCell p Bs L 𝒦 n f K i0) →
        (¬ ∃ (f : ℕ) (K : Subgroup G), GGSecFiveBCoordBSpSpCell p Bs L 𝒦 n eta f K i0) →
          GGSecFiveData p B x L D J

@[expose] def GGSecFiveBCoordBOffSpSpLargeInput : Prop :=
  GGSecFiveBCoordBOffSpSpOn fun _ _ lab => lab.n ≠ 1

theorem GGSecFiveBCoordBOffSpOn.spSp {S : ℕ → ℕ → LargeEvenLabel → Prop}
    (h : GGSecFiveBCoordBOffSpOn S) : GGSecFiveBCoordBOffSpSpOn S := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL hLab hB hRM hG0 hdense _
  exact h G p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL hLab hB hRM hG0 hdense

theorem ggSecFiveBCoordBOffSpSpInput_of_on {S : ℕ → ℕ → LargeEvenLabel → Prop}
    (h₁ : GGSecFiveBCoordBOffSpSpOn S)
    (h₂ : GGSecFiveBCoordBOffSpSpOn fun n p lab => ¬ S n p lab) :
    GGSecFiveBCoordBOffSpSpInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL hLab hB hRM hG0 hdense hsparse
  have hLab' : GGInnerDiagOnLabel (fun p lab => (GGSecFiveBCoordBLabel n p lab ∧ S n p lab) ∨
      (GGSecFiveBCoordBLabel n p lab ∧ ¬ S n p lab)) p Bs L :=
    largeEvenMarking_mono (fun lab _ _ _ _ _ h =>
      ⟨(em (S n p lab)).imp (fun hS => ⟨h.1, hS⟩) (fun hS => ⟨h.1, hS⟩), h.2⟩) hLab
  rcases hLab'.elim_or with h | h
  · exact h₁ G p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL h hB hRM hG0 hdense hsparse
  · exact h₂ G p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL h hB hRM hG0 hdense hsparse

theorem ggSecFiveBCoordBOffSpSpInput_of_qTwo_large (h₁ : GGSecFiveBCoordBOffQTwoInput)
    (h₂ : GGSecFiveBCoordBOffSpSpLargeInput) : GGSecFiveBCoordBOffSpSpInput :=
  ggSecFiveBCoordBOffSpSpInput_of_on (GGSecFiveBCoordBOffSpOn.spSp h₁) h₂

end Inputs

end CFSG.StandardType

end
