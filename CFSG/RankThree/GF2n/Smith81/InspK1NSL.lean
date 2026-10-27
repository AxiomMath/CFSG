module

public import CFSG.RankThree.GF2n.Smith81.InspKFacts
import CFSG.Timmesfeld.ARS.NSLFrameOrder

public section

namespace CFSG.RankThree.GF2n.Smith81.Insp

open CFSG CFSG.Blueprint CFSG.Open CFSG.Timmesfeld

theorem k1NSL_holds : K1NSLStatement := by
  intro G _ D hH hl _ hd
  obtain ⟨hc, hs, hm⟩ := largeClosures hH hl
  have h := arsHyp_rootClass hH hc hs hm
  have hcard : ∀ {f : ℕ}, (∀ E ∈ rootClass D, Nat.card E = 2 ^ f) →
      ∀ d ∈ D, Nat.card (rootGroup D d) = 2 ^ f := fun hE d hd => hE _ ⟨d, hd, rfl⟩
  have key : ARS.NSLOrderOutcome G (rootClass D) → RootOutcome G D ∨ LieModel G .PSU 3 3 1 := by
    rintro (⟨f, hf, hE, ⟨n, hn, hL⟩ | ⟨n, hn, hL⟩ | ⟨hf2, hL⟩ | hL | hL | hL⟩ | hU)
    · exact Or.inl ⟨.PSp, n, f, hf, Or.inr (Or.inl ⟨rfl, hn⟩), hL, hcard hE⟩
    · exact Or.inl ⟨.POmegaMinus, n, f, hf, Or.inr (Or.inr (Or.inl ⟨Or.inr rfl, hn⟩)), hL,
        hcard hE⟩
    · exact Or.inl ⟨.G2, 0, f, hf, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hf2⟩))), hL,
        hcard hE⟩
    · exact Or.inl ⟨.trialityD4, 0, f, hf, Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inl rfl⟩))),
        hL, hcard hE⟩
    · exact Or.inl ⟨.F4, 0, f, hf,
        Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inl rfl)⟩))), hL, hcard hE⟩
    · exact Or.inl ⟨.twistedE6, 0, f, hf,
        Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩))), hL,
        hcard hE⟩
    · exact Or.inr hU
  rcases hd with hσ | hF
  · rcases ARS.orderOutcome_of_sigmaEqLambda h hσ with ⟨f, hf, hE, n, hn, hL⟩ | hO
    · exact Or.inl ⟨.PSL, n, f, hf, Or.inl ⟨rfl, hn⟩, hL, hcard hE⟩
    · exact key hO
  · obtain ⟨F⟩ : Nonempty (ARS.NSLFrameData G (rootClass D)) := hF
    exact key (F.nslOrderOutcome h)

end CFSG.RankThree.GF2n.Smith81.Insp
