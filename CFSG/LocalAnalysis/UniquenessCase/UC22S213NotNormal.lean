module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21d
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.UC22S213PrimeRank
import CFSG.LocalAnalysis.UniquenessCase.UC22S213Inner
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ConjSetCard

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22s213_dvd_card_center_of_not_normal {D : Data G} (hσ : UC6S846.SigmaStd D)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hMN : ¬ D.M ≤ normalizer (L : Set G)) {a : G}
    (hodd : Odd (orderOf a)) (hpr : (orderOf a).Prime) (haL : CentralizesBar a L)
    (hN : ∀ p ∈ D.sig,
      CFSG.Open.pRank p (normalizer ((zpowers a : Subgroup G) : Set G) ⊓ D.M) ≤ 1)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (h2 : 2 ≤ CFSG.Open.pRank q L) :
    q ∣ Nat.card (center (Bar2 L)) := by
  by_contra hZ
  have hqσ : q ∉ D.sig := fun hqs => by
    have := uc22s213_pRank_le_one_of_centralizesBar hL.1.le hodd hpr haL hq hq2 (hN q hqs)
    omega
  obtain ⟨g, hg, hgN⟩ : ∃ g ∈ D.M, g ∉ normalizer (L : Set G) := by
    by_contra hc
    push Not at hc
    exact hMN hc
  have hne : L ≠ L.map (MulAut.conj g).toMonoidHom := fun he =>
    hgN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr he.symm)
  exact hqσ (hσ.four_mem q hq hq2 (uc22s213_four_le_pRank_of_two_conj hL
    (PartOne.Section8.mem_conjSetOf_self D.M L) ⟨g, hg, rfl⟩ hne hq hq2 h2 hZ))

end CFSG.LocalAnalysis.UniquenessCase.UC22
