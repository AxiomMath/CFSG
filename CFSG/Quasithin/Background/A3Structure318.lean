module

public import CFSG.Quasithin.Background.A3Structure318Transfer
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure318Star

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.SectionRank

theorem a318 (hF : A318Facts) {H : Type} [Group H] [Finite H] (hH : SQTKGroup H)
    (h36 : A36Statement (H ⧸ CFSG.pCore 2 H)) (h38 : A38Part3 (H ⧸ CFSG.pCore 2 H))
    {L : Subgroup H} (hL : L ∈ cComp (⊤ : Subgroup H))
    (hQ : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hrank : 1 < CFSG.Open.pRank p L) : A318Conclusion p L := by
  have : Fact p.Prime := ⟨hp⟩
  have hLn : L.Normal := A318.normal_of_pRank_gt_one hH h38 hL hp hp2 hrank
  obtain ⟨hS, h2S, hZ1, hZ2, hsolv⟩ := A318.star_structure hF.list hH h36 hL hQ hp2 hrank
  have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hL
  have hGrank : CFSG.Open.pRank p (⊤ : Subgroup (PStar p H)) ≤ 2 := by
    rw [pRank_quotient_eq (CFSG.pPrimeCore p H)
      ((Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card)]
    exact (hH.1 p hp hp2)
  have hSn : (starImage p L).Normal :=
    Subgroup.Normal.map hLn _ (QuotientGroup.mk'_surjective _)
  have hred := A318.a318_reduced hF (G := PStar p H) hp2
    (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot p) hGrank hS h2S hZ1 hZ2
  rcases hred with h1 | h2 | ⟨hp3, h3g, h3⟩
  · exact Or.inl (A318.eq_oPrimeResidual_of_star hperf hsolv h1)
  · exact Or.inr (Or.inl h2)
  · refine Or.inr (Or.inr ⟨hp3, h3g, ?_⟩)
    rcases h3 with h | h
    · subst hp3
      exact Or.inl (A318.eq_thetaOf_of_star hperf hsolv h)
    · exact Or.inr h

end CFSG.Quasithin
