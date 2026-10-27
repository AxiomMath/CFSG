module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBBridge

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem card_eq_pow_mul_card_of_lift_and_bound {p r : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {I : Set (MulAut R)} (hL : GGTorusLift p r R)
    (hU : ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
      ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
        (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) → Nat.card A ≤ p ^ r)
    {M : Type} [Group M] [Finite M] {L' E : Subgroup M} {θ : L' ⧸ Subgroup.center L' ≃* R}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)} (hP : GGTableBPosition p L' E I θ hE) :
    Nat.card E = p ^ r * Nat.card (E ⊓ Subgroup.centralizer (L' : Set M) : Subgroup M) := by
  have hlow : p ^ r ≤ Nat.card (ggGamma L' hE).range :=
    TableBBridge.pow_le_card_range_of_torusLift hP hp hL
  have hup : Nat.card (ggGamma L' hE).range ≤ p ^ r :=
    hU ↥L' (ggQuotHom θ) (ggQuotHom_surjective θ) (ker_ggQuotHom θ).le hP.1
      (ggGamma L' hE).range (TableBBridge.isElemAbelian_range_gamma hP)
      (TableBBridge.induces_range_gamma hP)
  rw [TableBBridge.card_eq_card_range_mul hE, le_antisymm hup hlow]

end CFSG.StandardType
