module

public import CFSG.RankThree.GF2n.Smith81.LinTLPosition
public import CFSG.RankThree.GF2n.Smith81.LinTLCentre
public import CFSG.RankThree.GF2n.Smith81.LinTLMixed
public import CFSG.RankThree.GF2n.Smith81.Lin31Back

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

@[expose] def LinTransvStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Ctx M Q Z B → LinSetup M Q Z B n V₁ V₂ → 3 ≤ n →
      (B ≤ V₁ ∨ B ≤ V₂) ∧ ∀ t ∈ LB M Q B, t ∉ Q →
        HasDimOn V₁ Z 1 t ∧ HasDimOn V₂ Z 1 t ∧ B ≤ ⁅Q, Subgroup.zpowers t⁆ ⊔ Z

variable {G : Type} [Group G] [Finite G]
  {M Q Z B : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G}

theorem LinSetup.transv_le_comm_of_le_V₁ (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂)
    (hn : 3 ≤ n) (hB : B ≤ V₁) {t : G} (ht : t ∈ LB M Q B) (htQ : t ∉ Q) :
    HasDimOn V₁ Z 1 t ∧ HasDimOn V₂ Z 1 t ∧ B ≤ ⁅Q, Subgroup.zpowers t⁆ ⊔ Z := by
  obtain ⟨heq, h1, h2⟩ := hS.transv_of_le_V₁ hc hn hB ht htQ
  have hV₁Q : V₁ ≤ Q := by
    obtain ⟨K, _, _, -, φ, -, -, -, hV₁Q, -⟩ := hS
    exact hV₁Q
  refine ⟨h1, h2, ?_⟩
  calc B ≤ B ⊔ Z := le_sup_left
    _ = ⁅V₁, Subgroup.zpowers t⁆ ⊔ Z := heq.symm
    _ ≤ ⁅Q, Subgroup.zpowers t⁆ ⊔ Z :=
      sup_le_sup_right (Subgroup.commutator_mono hV₁Q le_rfl) Z

theorem linTransvStatement_of_not_mixed
    (h9 : ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (n : ℕ)
      (V₁ V₂ : Subgroup G), Ctx M Q Z B → LinSetup M Q Z B n V₁ V₂ → 3 ≤ n →
        ¬ ((B ⊔ Z) ⊓ V₁ = Z ∧ (B ⊔ Z) ⊓ V₂ = Z)) :
    LinTransvStatement := by
  intro G _ _ M Q Z B n V₁ V₂ hc hS hn
  have hpos : B ≤ V₁ ∨ B ≤ V₂ := by
    rcases hS.B_position hc hn with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (h9 G M Q Z B n V₁ V₂ hc hS hn h).elim
  refine ⟨hpos, fun t ht htQ => ?_⟩
  rcases hpos with hB | hB
  · exact hS.transv_le_comm_of_le_V₁ hc hn hB ht htQ
  · obtain ⟨h2, h1, h3⟩ := hS.symm.transv_le_comm_of_le_V₁ hc hn hB ht htQ
    exact ⟨h1, h2, h3⟩

theorem linBInStatement_of_not_mixed
    (h9 : ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (n : ℕ)
      (V₁ V₂ : Subgroup G), Ctx M Q Z B → LinSetup M Q Z B n V₁ V₂ → 3 ≤ n →
        ¬ ((B ⊔ Z) ⊓ V₁ = Z ∧ (B ⊔ Z) ⊓ V₂ = Z)) :
    LinBInStatement := fun G _ _ M Q Z B n V₁ V₂ hc hS hn =>
  (linTransvStatement_of_not_mixed h9 G M Q Z B n V₁ V₂ hc hS hn).1

theorem lin31FwdStatement_of_conj_position
    (h10 : ∀ (G : Type) [Group G] [Finite G] (M Q Z B A : Subgroup G) (n : ℕ)
      (V₁ V₂ : Subgroup G), Ctx M Q Z B → LinSetup M Q Z B n V₁ V₂ → 3 ≤ n →
        Ctx M Q Z A → A ≤ V₁ ∨ A ≤ V₂) :
    Lin31FwdStatement := by
  intro G _ _ M Q Z B n V₁ V₂ hc hS hn v hvQ hv1 hvZ
  have hZV₁ : Z ≤ V₁ := by
    obtain ⟨K, _, _, -, φ, -, -, hZV₁, -⟩ := hS
    exact hZV₁
  by_cases hvz : v ∈ Z
  · exact Or.inl (hZV₁ hvz)
  obtain ⟨g', z, hz, -, rfl⟩ := hvZ
  obtain ⟨g, hgQ, hvg⟩ := stroth_2_6 hc.hyp hvQ hvz ⟨g', z, hz, rfl⟩
  have hA : Ctx M Q Z (conjSubgroup g Z) :=
    ⟨hc.hyp, ⟨g, rfl⟩, hgQ, fun h => hvz (h ▸ hvg)⟩
  rcases h10 G M Q Z B (conjSubgroup g Z) n V₁ V₂ hc hS hn hA with h | h
  · exact Or.inl (h hvg)
  · exact Or.inr (h hvg)

theorem linTransvStatement_holds : LinTransvStatement :=
  linTransvStatement_of_not_mixed fun _ _ _ _ _ _ _ _ _ _ hc hS hn => hS.not_mixed hc hn

theorem linBInStatement_holds : LinBInStatement :=
  linBInStatement_of_not_mixed fun _ _ _ _ _ _ _ _ _ _ hc hS hn => hS.not_mixed hc hn

end CFSG.RankThree.GF2n.Smith81
