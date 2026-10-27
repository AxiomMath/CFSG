module

public import CFSG.LocalAnalysis.UniquenessCase.UC9R96Cent
public import CFSG.LocalAnalysis.UniquenessCase.UC9R96Rep
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddFrob
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC9R96

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9 (xbar9 wbar9 GenSeven)

variable {G : Type} [Group G] [Finite G]

namespace Core

variable {D : Data G} {Y H : Subgroup G} {q : ℕ}

theorem I9_le_M_of_odd_dvd (S : Core D Y H q)
    (hN : ∀ A : Subgroup G, A ≤ Opp 3 Y → (Nat.card A).Prime → Odd (Nat.card A) →
      normalizer (A : Set G) ≤ D.M)
    {E : Subgroup G} (hyp : F09.Hyp91 D Y H E) (hr : ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ q - 1)
    (hK461 : UCK.K461) (hK462 : UCK.K462) (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) :
    F09.I9 H ≤ D.M := by
  by_contra hIM
  obtain ⟨p, hp, F, hF, hFt, V, hV, hVm, hVf, σ, hcard, -, hpq, hσ, -, hfpf⟩ :=
    S.exists_sl2_rep_of_not_le hN hyp hK461 hK462 hSch hIM
  obtain ⟨r, hrp, hr2, hrq⟩ := hr
  haveI : Fact r.Prime := ⟨hrp⟩
  obtain ⟨μ, hμ⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) r (by
    rw [Nat.card_units, Nat.card_eq_fintype_card, hcard]
    exact hrq)
  have hqp : (Fintype.card F : ZMod p) ≠ 0 := by
    rw [hcard, Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp.out S.prime).mp h)
  obtain ⟨v, hv0, hv⟩ := PartOne.Section9.exists_fixed_diag σ hσ hqp (μ := μ)
    (by rw [hμ]; exact hrp.odd_of_ne_two hr2)
  have hdo : orderOf (CFSG.PSL2Table.diag μ) = r := by
    rw [PartOne.Section9.orderOf_diag, hμ]
  exact hv0 (hfpf _ (by rw [hdo]; exact hrp) (by rw [hdo]; exact hr2) v hv)

theorem false_of_shape92 (S : Core D Y H 7)
    (hN : ∀ A : Subgroup G, A ≤ Opp 3 Y → (Nat.card A).Prime → Odd (Nat.card A) →
      normalizer (A : Set G) ≤ D.M)
    {E : Subgroup G} (hyp : F09.Hyp91 D Y H E) (hK461 : UCK.K461) (hK462 : UCK.K462)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (h92L : H = F09.L9 Y H ⊔ (H ⊓ D.M)) (h92S : F09.Shape92 (F09.Lbar9 Y H)) : False :=
  S.false_of_genSeven hN h92L
    (S.I9_le_M_of_odd_dvd hN hyp ⟨3, Nat.prime_three, by norm_num, by norm_num⟩ hK461 hK462 hSch)
    (PartOne.Section9.genSeven_of_shape92 h92S S.isL2Odd_bar2_xbar9
      (PartOne.Section9.isCyclic_of_isPGroup_lbar9 hyp))

end Core

end CFSG.LocalAnalysis.UniquenessCase.UC9R96
