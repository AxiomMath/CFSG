module

public import CFSG.RankThree.PartTwo.Sec21.HeringFFStatement

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.Assembly
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.Blueprint (ChevalleyExceptionalModel)

section Hypotheses

variable {G : Type} [Group G]

@[expose] def FFNotStronglyClosed (b : G) : Prop :=
  ∃ x ∈ Subgroup.zpowers b, ∃ g : G, g * x * g⁻¹ ∈ Subgroup.centralizer ({b} : Set G) ∧
    g * x * g⁻¹ ∉ Subgroup.zpowers b

@[expose] def FFCentCyclicSylow (L : Subgroup G) : Prop :=
  ∀ P : Sylow 3 ↥(Subgroup.centralizer (L : Set G)),
    IsCyclic ↥(P : Subgroup ↥(Subgroup.centralizer (L : Set G)))

@[expose] def FFHypA5 [Finite G] (b : G) : Prop :=
  ∀ B : Subgroup G, B ≤ Subgroup.centralizer ({b} : Set G) → CFSG.Open.IsElemAbelian 3 B →
    (∃ T : Subgroup G, T ≤ Subgroup.centralizer ({b} : Set G) ∧ IsPGroup 2 T ∧ T ≠ ⊥ ∧
      B ≤ Subgroup.normalizer (T : Set G)) →
    Nat.card B = 3 ^ localRank 3 ↥(Subgroup.centralizer ({b} : Set G)) →
    ∃ T : Subgroup G, T ≤ Subgroup.centralizer ({b} : Set G) ∧ IsPGroup 2 T ∧
      B ≤ Subgroup.normalizer (T : Set G) ∧ ¬ B ≤ Subgroup.centralizer (T : Set G)

@[expose] def FFStandardJ (b : G) (J : Subgroup G) : Prop :=
  J ≤ Subgroup.centralizer ({b} : Set G) ∧
    CFSG.IsComponent (J.subgroupOf (Subgroup.centralizer ({b} : Set G))) ∧
    ∀ K : Subgroup ↥(Subgroup.centralizer ({b} : Set G)), CFSG.IsComponent K →
      3 ∣ Nat.card K → K = J.subgroupOf (Subgroup.centralizer ({b} : Set G))

theorem FFNotWeaklyClosed.notStronglyClosed [Finite G] {b : G} (h : FFNotWeaklyClosed b) :
    FFNotStronglyClosed b := by
  obtain ⟨g, hle, hne⟩ := h
  refine ⟨b, Subgroup.mem_zpowers b, g⁻¹, ?_, fun hmem => hne ?_⟩
  · apply hle
    refine ⟨b, Subgroup.mem_zpowers b, ?_⟩
    simp [MulAut.conj_apply]
  · have hle' : conjugate (Subgroup.zpowers b) g ≤ Subgroup.zpowers b := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hk : (MulAut.conj g⁻¹).toMonoidHom (b ^ k) = (g⁻¹ * b * g⁻¹⁻¹) ^ k := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        simpa only [inv_inv] using (conj_zpow (a := g⁻¹) (i := k) (b := b)).symm
      rw [hk]
      exact Subgroup.zpow_mem _ hmem k
    refine Subgroup.eq_of_le_of_card_ge hle' ?_
    rw [conjugate, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]

end Hypotheses

@[expose] def FF79TheoremB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    IsCharTwoType G →
    ∀ b : G, orderOf b = 3 → ∀ J : Subgroup G,
      FFStandardJ b J →
      StatedClassicalModel (J ⧸ Subgroup.center J) .PSL 5 2 1 →
      FFCentCyclicSylow J →
      FFNotStronglyClosed b →
      localRank 3 G = CFSG.Open.pRank 3 (Subgroup.centralizer ({b} : Set G)) →
        StatedClassicalModel G .PSL 7 2 1

@[expose] def FF81TheoremA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    IsCharTwoType G →
    ∀ b : G, orderOf b = 3 → ∀ L : Subgroup G,
      L ≤ Subgroup.centralizer ({b} : Set G) →
      Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (L : Set G) →
      CFSG.IsQuasisimple L →
      FFCentCyclicSylow L →
      localRank 3 G = localRank 3 ↥(Subgroup.centralizer ({b} : Set G)) →
      FFNotWeaklyClosed b →
      FFHypA5 b →
      StatedClassicalModel L .PSp 3 2 1 →
        StatedClassicalModel G .PSp 4 2 1 ∨ ChevalleyExceptionalModel G .F4 2 1

@[expose] def FF84TheoremA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    IsCharTwoType G →
    ∀ b : G, orderOf b = 3 → ∀ L : Subgroup G,
      L ≤ Subgroup.centralizer ({b} : Set G) →
      Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (L : Set G) →
      CFSG.IsQuasisimple L →
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 1 →
      FFCentCyclicSylow L →
      FFNotStronglyClosed b →
      localRank 3 G = localRank 3 ↥(Subgroup.centralizer ({b} : Set G)) →
      (∀ p : ℕ, p.Prime → 3 < p → localRank p G ≤ 2) →
      FFSylowCommutatorOdd b → FFSylowHyperplaneOdd b →
      KProper InCatalog G →
        StatedClassicalModel G .PSL 6 2 1 ∨ StatedClassicalModel G .POmegaMinus 4 2 1

end CFSG.RankThree.PartTwo.Sec21
