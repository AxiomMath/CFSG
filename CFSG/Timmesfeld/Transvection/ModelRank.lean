module

public import CFSG.Timmesfeld.Transvection.ModelRankSp
public import CFSG.Timmesfeld.Transvection.ModelRankSU

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank

theorem transvectionConclusionRank_of_isSmallFrame {H : Type} [Group H] {Δ : Set (Subgroup H)}
    {f : ℕ} {hf : 1 ≤ f} (h : TransvectionConclusion H Δ f hf) {r : ℕ} (hr : 2 ≤ r)
    {P Q : Fin r → Subgroup H} {k : Fin r} (hfr : IsSmallFrame Δ P Q k) :
    TransvectionConclusionRank H Δ f hf r hr := by
  rcases h with ⟨n, hn, Φ, hΦ, hmem⟩ | ⟨m, hm, Φ, hΦ, hker, hmem⟩
  · have e := rank_eq_of_isSmallFrame_sp (by omega) hΦ.1 hmem hfr
    subst e
    exact Or.inl ⟨Φ, hΦ, hmem⟩
  · have e := two_mul_rank_eq_of_isSmallFrame_su (card_galoisField_two_mul hf) hm hker.le hmem hfr
    subst e
    exact Or.inr ⟨Φ, hΦ, hker, hmem⟩

end CFSG.Timmesfeld.Transvection
