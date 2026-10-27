module

public import CFSG.Quasithin.Background.RonanE111MemE1

public section

namespace CFSG.Quasithin.RonanE111

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.Vol2.Ch11.SecB
  CFSG.Quasithin.E2.E22N CFSG.Quasithin.E2.E22N.E111R

variable {G : Type} [Group G] [Finite G]

theorem P_le_cov {X T J : Subgroup G} (hR : E111Reduced G X T) (hJ : IsComp X J) {n : ℕ}
    (hn : 1 ≤ n) {G₁ : Subgroup G} (hTG : T ≤ G₁) {A : Subgroup G} (hAT : A ≤ T)
    (hAab : IsElemAbelian 2 A) (hmem : ∀ K : Subgroup G, E1.IsE n ⊤ T A K → K ≤ G₁)
    {P : Subgroup G}
    (hP : E1.IsE n (J ⊔ (T ⊓ Subgroup.normalizer (J : Set G))) (T ⊓ Subgroup.normalizer (J : Set G))
      (A ⊓ Subgroup.normalizer (J : Set G)) P) : P ≤ Cov G₁ J := by
  obtain ⟨hPH, htau, hSyl, hcase⟩ := hP
  rcases hcase with ⟨hE1, -⟩ | ⟨hE2, hbar⟩
  · exact P_le_cov_E1 hR hJ hn hTG hAT hAab hmem hPH htau hSyl hE1
  · exact P_le_cov_E2 hR hJ hn hTG hAT hAab hmem hPH htau hSyl hE2 hbar

end CFSG.Quasithin.RonanE111
