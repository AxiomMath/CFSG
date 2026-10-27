module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08UseS
import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

namespace F08

@[expose] def R869NS5 (D : Data G) : Prop :=
  ∀ L : Subgroup G, L ≤ D.M → D.M ≤ normalizer (L : Set G) → IsProdOfCalC D.M L →
    (∃ p ∈ D.sig, 2 ≤ CFSG.Open.pRank p L ∧ (p = 5 → 2 ^ 12 ∣ Nat.card (Bar2 L))) →
    ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ A : Subgroup G, A ≤ D.M → Nat.card A = r →
      (L ⊓ centralizer (A : Set G)) ⊔ pCoreOf 2 L = L → normalizer (A : Set G) ≤ D.M

theorem R869NS5_of_R869NS (D : Data G) (h : R869NS D) : R869NS5 D := by
  rintro L hLM hML hprod ⟨p, hp, h2, -⟩
  exact h L hLM hML hprod ⟨p, hp, h2⟩

end F08

theorem uc22p2214_faith_of_R869NS5 (D : Data G) (Ch : Choice2011 G) (h869 : F08.R869NS5 D)
    (hV : S22_V D Ch) (h1930 : H1930 D) (c : Ctx22b D Ch) {K : Subgroup G} (hK : K ∈ calC D.M)
    (hKV : ¬ K ≤ centralizer (c.V : Set G))
    (hpX : ∃ p ∈ D.sig, 2 ≤ CFSG.Open.pRank p (conjClosure D.M K) ∧
      (p = 5 → 2 ^ 12 ∣ Nat.card (Bar2 (conjClosure D.M K))))
    (hfix : ∀ K' ∈ conjSetOf D.M K, c.B0 ≤ normalizer (K' : Set G)) {a : G} (ha : a ∈ c.B0)
    (ha1 : a ≠ 1) :
    ∃ K' ∈ conjSetOf D.M K, ∃ k ∈ K', a * k * a⁻¹ * k⁻¹ ∉ centralizer (c.V : Set G) := by
  obtain ⟨hXM, hMX, hprod⟩ := uc22p22u_conjClosure_isProd le_rfl Subgroup.le_normalizer hK
  exact uc22p2214_faith_of_normalizer_le D Ch hV h1930 c hK hKV
    (h869 _ hXM hMX hprod hpX) hfix ha ha1

end CFSG.LocalAnalysis.UniquenessCase.UC22
