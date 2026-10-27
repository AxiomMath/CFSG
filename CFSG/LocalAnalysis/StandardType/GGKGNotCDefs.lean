module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynExc

public section

namespace CFSG.StandardType.KG

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KD4T
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp

@[expose] def KGNotCLieType (ℓ : ℕ) (X : Type) [Group X] : Prop :=
  ∃ (t : StatedLieTag) (r e : ℕ), t ≠ .PSp ∧
    CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) t r ℓ e

theorem KGNotCLieType.of_mulEquiv {ℓ : ℕ} {X Y : Type} [Group X] [Group Y]
    (h : KGNotCLieType ℓ X) (e : X ≃* Y) : KGNotCLieType ℓ Y := by
  obtain ⟨t, r, f, ht, hm⟩ := h
  exact ⟨t, r, f, ht, CFSG.Blueprint.LieModel.of_mulEquiv
    (QuotientGroup.congr (Subgroup.center X) (Subgroup.center Y) e (Subgroup.map_center_eq e)) hm⟩

theorem KGNotCLieType.of_surjective {ℓ : ℕ} {X Y : Type} [Group X] [Group Y]
    (h : KGNotCLieType ℓ X) (hX : commutator X = ⊤) (f : X →* Y) (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center X) : KGNotCLieType ℓ Y := by
  obtain ⟨t, r, e, ht, hm⟩ := h
  obtain ⟨g⟩ := nonempty_centralQuotient_mulEquiv hX f hf hk
  exact ⟨t, r, e, ht, CFSG.Blueprint.LieModel.of_mulEquiv g hm⟩

theorem KGNotCLieType.map_conj {G : Type} [Group G] {ℓ : ℕ} {R : Subgroup G} (φ : G ≃* G)
    (h : KGNotCLieType ℓ ↥R) : KGNotCLieType ℓ ↥(R.map φ.toMonoidHom) :=
  h.of_mulEquiv (R.equivMapOfInjective φ.toMonoidHom φ.injective)

@[expose] def D4TrialityLayerKGNotC (τ : Tag) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ], 1 ≤ f →
    ∀ a b c : Fin τ.rank, a ≠ b → b ≠ c → a ≠ c → a.val ∈ ({1, 2, 4} : Set ℕ) →
    b.val ∈ ({1, 2, 4} : Set ℕ) → c.val ∈ ({1, 2, 4} : Set ℕ) →
    ∀ (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L), n ∈ adjointGroup τ L →
      (∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
        weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice (List.formPerm [a, b, c]) α) →
      ∀ P : Subgroup (ModGL τ L), P = rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) →
      KGNotCLieType ℓ ↥P

@[expose] def D4SwapLayerKGNotC (τ : Tag) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ], 1 ≤ f →
    ∀ i j : Fin τ.rank, i ≠ j → i.val ∈ ({1, 2, 4} : Set ℕ) → j.val ∈ ({1, 2, 4} : Set ℕ) →
    ∀ (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L), n ∈ adjointGroup τ L →
      (∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
        weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice (Equiv.swap i j) α) →
      ∀ P : Subgroup (ModGL τ L), P = rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) →
      KGNotCLieType ℓ ↥P

end CFSG.StandardType.KG
