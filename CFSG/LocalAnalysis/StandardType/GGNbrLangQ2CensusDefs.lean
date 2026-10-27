module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2Rows
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2Cover

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def Q2CensusRLevel (S : LargeEvenLabel → Prop) (C : Q2RowKind → Prop) : Prop :=
  ∀ (p d m : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
    LargeEvenSplit p lab → S lab → 3 ≤ d → 2 ≤ m → p ∣ d → p ∣ 2 ^ m - 1 →
    LargeEvenLabelAll lab (fun R _ I _ =>
      ∀ A : Subgroup (MulAut R), IsElemAbelian p A → (∀ a ∈ A, a ∈ I) →
      (∀ r : ℕ, GGTorusLift p r R → p ^ r ≤ Nat.card A) →
      p ^ 3 ≤ Nat.card A → p ^ (d - 1) ≤ Nat.card A → Nat.card A ≤ p ^ d →
      ∀ u ∈ A, orderOf u = p →
      ∀ J : Subgroup R, CFSG.Open.IsComponentOf J (ggAutFixedSubgroup u) →
        (∀ J' : Subgroup R, CFSG.Open.IsComponentOf J' (ggAutFixedSubgroup u) → J' = J) →
        (∀ a ∈ A, ∀ j ∈ J, a j ∈ J) →
        ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ m →
          Nonempty (↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K)) →
          ∃ kind : Q2RowKind, C kind ∧ q2RowFits kind p d (2 ^ m) lab)

theorem Q2CensusRLevel.mono {S S' : LargeEvenLabel → Prop} {C C' : Q2RowKind → Prop}
    (hS : ∀ lab, LargeEvenInLambda2 lab → S' lab → S lab) (hC : ∀ kind, C kind → C' kind)
    (h : Q2CensusRLevel S C) : Q2CensusRLevel S' C' := by
  intro p d m lab hp hp2 hΛ hsplit hS' hd hm hpd hpm Q hQ
  refine largeEvenRawDatum_mono ?_ (h p d m lab hp hp2 hΛ hsplit (hS lab hΛ hS') hd hm hpd hpm Q hQ)
  rintro R _ I F ⟨hq, hP⟩
  refine ⟨hq, fun A hA hAI hbig h3 hlo hup u hu huo J hJ huniq hAJ K _ _ hK he => ?_⟩
  obtain ⟨kind, hkC, hfit⟩ := hP A hA hAI hbig h3 hlo hup u hu huo J hJ huniq hAJ K hK he
  exact ⟨kind, hC kind hkC, hfit⟩

theorem Q2CensusRLevel.or {S T : LargeEvenLabel → Prop} {C C' : Q2RowKind → Prop}
    (hS : Q2CensusRLevel S C) (hT : Q2CensusRLevel T C') :
    Q2CensusRLevel (fun lab => S lab ∨ T lab) (fun kind => C kind ∨ C' kind) := by
  intro p d m lab hp hp2 hΛ hsplit hST hd hm hpd hpm Q hQ
  rcases hST with hS' | hT'
  · refine largeEvenRawDatum_mono ?_ (hS p d m lab hp hp2 hΛ hsplit hS' hd hm hpd hpm Q hQ)
    rintro R _ I F ⟨hq, hP⟩
    refine ⟨hq, fun A hA hAI hbig h3 hlo hup u hu huo J hJ huniq hAJ K _ _ hK he => ?_⟩
    obtain ⟨kind, hkC, hfit⟩ := hP A hA hAI hbig h3 hlo hup u hu huo J hJ huniq hAJ K hK he
    exact ⟨kind, Or.inl hkC, hfit⟩
  · refine largeEvenRawDatum_mono ?_ (hT p d m lab hp hp2 hΛ hsplit hT' hd hm hpd hpm Q hQ)
    rintro R _ I F ⟨hq, hP⟩
    refine ⟨hq, fun A hA hAI hbig h3 hlo hup u hu huo J hJ huniq hAJ K _ _ hK he => ?_⟩
    obtain ⟨kind, hkC, hfit⟩ := hP A hA hAI hbig h3 hlo hup u hu huo J hJ huniq hAJ K hK he
    exact ⟨kind, Or.inr hkC, hfit⟩

end CFSG.StandardType
