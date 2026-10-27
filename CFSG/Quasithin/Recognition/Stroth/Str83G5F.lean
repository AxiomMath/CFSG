module

public import CFSG.Quasithin.Recognition.Stroth.Str83G5FCountN

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.GH74.Uniqueness.Bender CFSG.Blueprint CFSG.LieType.Ree

theorem str83G5FactF_holds :
    ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (a : ℕ),
      Hyp111 L1 L2 S → 1 ≤ a → Nonempty (oTwoQuot ↥L1 ≃* Sz a) →
      bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G) →
      Nat.card (Q1 L1 L2 S) < 2 ^ (16 * (2 * a + 1)) →
      ∀ D1 N1 : Subgroup G, D1 ≤ borelOf L1 S → Odd (Nat.card D1) →
        N1 ≤ P1 L1 L2 S → Odd (Nat.card N1) →
        (∀ x ∈ N1, ∀ l ∈ L1, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L1) →
        D1 ≤ Subgroup.normalizer (N1 : Set G) →
        (∀ δ ∈ D1, δ ≠ 1 → Q1 L1 L2 S ⊓ Subgroup.centralizer ({δ} : Set G) =
            Q1 L1 L2 S ⊓ Subgroup.centralizer (D1 : Set G)) ∧
        (∃ k : ℕ, (Q1 L1 L2 S ⊓ Subgroup.centralizer (D1 : Set G)).relIndex (Q1 L1 L2 S) =
            2 ^ (4 * (2 * a + 1) * k)) ∧
        (∃ k : ℕ, (Q1 L1 L2 S ⊓ Subgroup.centralizer ((D1 ⊔ N1 : Subgroup G) : Set G)).relIndex
            (Q1 L1 L2 S ⊓ Subgroup.centralizer (N1 : Set G)) = 2 ^ (4 * (2 * a + 1) * k)) := by
  intro G _ _ L1 L2 S a hF ha hSz hB hQ D1 N1 hD1 hD1odd hN1P hN1odd hN1L hD1N1
  have hLS : L1 ⊔ S ≤ P1 L1 L2 S :=
    sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
  have hnorm : ∀ g ∈ P1 L1 L2 S, ∀ x ∈ Q1 L1 L2 S, g * x * g⁻¹ ∈ Q1 L1 L2 S := fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (P1 L1 L2 S) hg) x).mp hx
  have hQ1 : IsNormalIn (L1 ⊔ S) (Q1 L1 L2 S) (Q1 L1 L2 S) :=
    ⟨le_rfl, fun g hg => hnorm g (hLS hg)⟩
  have hQ1X : IsNormalIn (L1 ⊔ S ⊔ N1) (Q1 L1 L2 S) (Q1 L1 L2 S) :=
    ⟨le_rfl, fun g hg => hnorm g (sup_le hLS hN1P hg)⟩
  obtain ⟨hb, ha'⟩ := G5F.d1_claim hF hB ha hSz hQ hD1 hD1odd hQ1
  exact ⟨ha', hb, G5F.n1_claim hF hB ha hSz hQ hD1 hD1odd hN1P hN1odd hN1L hD1N1 hQ1X⟩

end CFSG.Quasithin.Stroth

end
