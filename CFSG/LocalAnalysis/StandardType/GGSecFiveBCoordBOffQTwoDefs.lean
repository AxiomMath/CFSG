module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank

section Inputs

@[expose] def GGSecFiveBCoordBOffSpOn (S : ℕ → ℕ → LargeEvenLabel → Prop) : Prop :=
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
          GGSecFiveData p B x L D J

@[expose] def GGSecFiveBCoordBOffQTwoInput : Prop :=
  GGSecFiveBCoordBOffSpOn fun _ _ lab => lab.n = 1

theorem GGSecFiveBCoordBOffSpOn.or {S T : ℕ → ℕ → LargeEvenLabel → Prop}
    (h₁ : GGSecFiveBCoordBOffSpOn S) (h₂ : GGSecFiveBCoordBOffSpOn T) :
    GGSecFiveBCoordBOffSpOn fun n p lab => S n p lab ∨ T n p lab := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL hLab hB hRM hG0 hcell
  have hLab' : GGInnerDiagOnLabel (fun p lab => (GGSecFiveBCoordBLabel n p lab ∧ S n p lab) ∨
      (GGSecFiveBCoordBLabel n p lab ∧ T n p lab)) p Bs L :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h =>
      ⟨h.1.2.imp (fun hS => ⟨h.1.1, hS⟩) (fun hT => ⟨h.1.1, hT⟩), h.2⟩) hLab
  rcases hLab'.elim_or with h | h
  · exact h₁ G p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL h hB hRM hG0 hcell
  · exact h₂ G p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL h hB hRM hG0 hcell

theorem GGSecFiveBCoordBOffSpOn.mono {S T : ℕ → ℕ → LargeEvenLabel → Prop}
    (h : GGSecFiveBCoordBOffSpOn S)
    (hST : ∀ n p lab, GGSecFiveBCoordBLabel n p lab → T n p lab → S n p lab) :
    GGSecFiveBCoordBOffSpOn T := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL hLab hB hRM hG0 hcell
  exact h G p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL
    (largeEvenMarking_mono (fun lab _ _ _ _ _ h' =>
      ⟨⟨h'.1.1, hST n p lab h'.1.1 h'.1.2⟩, h'.2⟩) hLab) hB hRM hG0 hcell

@[expose] def GGSecFiveBCoordBOffQTwoSpInput : Prop :=
  GGSecFiveBCoordBOffSpOn fun _ _ lab => lab.n = 1 ∧ (lab.tag = .B ∨ lab.tag = .C)

@[expose] def GGSecFiveBCoordBOffQTwoLinInput : Prop :=
  GGSecFiveBCoordBOffSpOn fun _ _ lab => lab.n = 1 ∧ lab.tag = .A

theorem ggSecFiveBCoordBOffQTwoInput_of_families (hS : GGSecFiveBCoordBOffQTwoSpInput)
    (hO : GGSecFiveBCoordBOffSpOn fun _ _ lab => lab.n = 1 ∧ (lab.tag = .twD ∨ lab.tag =
        .D)) (hA : GGSecFiveBCoordBOffQTwoLinInput) :
    GGSecFiveBCoordBOffQTwoInput :=
  ((hS.or hO).or hA).mono fun _ _ _ hlab h1 => by
    rcases hlab with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩
    · exact Or.inl (Or.inl ⟨h1, ht⟩)
    · exact Or.inl (Or.inr ⟨h1, Or.inl ht⟩)
    · exact Or.inl (Or.inr ⟨h1, Or.inr ht⟩)
    · exact Or.inr ⟨h1, ht⟩

end Inputs

end CFSG.StandardType

end
