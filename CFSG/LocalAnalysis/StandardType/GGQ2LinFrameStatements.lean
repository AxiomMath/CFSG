module

public import CFSG.LocalAnalysis.StandardType.GGQ2LinStatements

public section

namespace CFSG.StandardType.GGQ2Frame.LinPlacement

open CFSG CFSG.Assembly CFSG.StandardType Matrix
open CFSG.Open (IsElemAbelian)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def LinCardEEq : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H E : Subgroup G} {r t : ℕ} {ε : Fin 2} {K : Type} [Field K]
    [Finite K] [CharP K 2]
    (θ : ↥H ⧸ Subgroup.center ↥H ≃* LargeEvenProj (LargeEvenSLGroup (Fin (r + 1)) K)),
    2 * t + ε.val = r + 1 → Nat.card K = 2 → commutator H = ⊤ → IsElemAbelian 3 E →
    ∀ (hEN : E ≤ Subgroup.normalizer (H : Set G)),
    (∀ (b : G) (hb : b ∈ E), ggLAut H θ ⟨b, hEN hb⟩ ∈
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin (r + 1)) K)) Set.univ) →
    (∀ g ∈ Subgroup.centralizer (E : Set G), g ^ 3 = 1 → g ∈ E) →
    ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G)) → 3 ^ 3 ≤ Nat.card E →
    Nat.card E = 3 ^ t

end CFSG.StandardType.GGQ2Frame.LinPlacement
