module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGFFLinearProp2Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (K B₁ : Subgroup G), orderOf b = 3 →
    K ≤ Subgroup.centralizer ({b} : Set G) →
    (K.subgroupOf (Subgroup.centralizer ({b} : Set G))).Normal →
    (GGHasLabel ⟨.A, 5, 1⟩ K ∨ GGHasLabel ⟨.A, 6, 1⟩ K) →
    B₁ ≤ K → IsElemAbelian 3 B₁ → Nat.card B₁ = 3 ^ 3 →
    (∀ P : Subgroup G, P ≤ Subgroup.centralizer (K : Set G) → IsPGroup 3 P → IsCyclic P) →
    (∃ g : G, g * b * g⁻¹ ∈ K) → IsCharTwoType G →
    Nat.card (ggAutomizer ⊤ (Subgroup.closure {b} ⊔ B₁)) = 384 ∨
      Nat.card (ggAutomizer ⊤ (Subgroup.closure {b} ⊔ B₁)) = 1152

@[expose] def GGO2aCentreKnown : Prop :=
  ∀ lab : LargeEvenLabel, (lab = ⟨.A, 5, 1⟩ ∨ lab = ⟨.A, 6, 1⟩) →
    LargeEvenLabelAll lab fun R _ _ _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → Subgroup.center L' = ⊥

theorem ggO2a_center_eq_bot (hZ : GGO2aCentreKnown) {K : Type} [Group K] [Finite K]
    (hperf : commutator K = ⊤) {lab : LargeEvenLabel} (hlab : lab = ⟨.A, 5, 1⟩ ∨ lab = ⟨.A, 6, 1⟩)
    (hhas : GGHasLabel lab (K ⧸ Subgroup.center K)) : Subgroup.center K = ⊥ := by
  obtain ⟨R, _, I, F, ⟨e⟩, hP⟩ := largeEvenRawDatum_exists (hZ lab hlab _ hhas)
  refine hP K (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) (fun k hk => ?_) hperf
  have h1 : e (QuotientGroup.mk' (Subgroup.center K) k) = 1 := hk
  rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem ggO2a_hasLabel_of_centre (hZ : GGO2aCentreKnown) {K : Type} [Group K] [Finite K]
    (hperf : commutator K = ⊤) {lab : LargeEvenLabel} (hlab : lab = ⟨.A, 5, 1⟩ ∨ lab = ⟨.A, 6, 1⟩)
    (hhas : GGHasLabel lab (K ⧸ Subgroup.center K)) : GGHasLabel lab K :=
  ggHasLabel_of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq
    (ggO2a_center_eq_bot hZ hperf hlab hhas)).trans QuotientGroup.quotientBot) hhas

end CFSG.StandardType
