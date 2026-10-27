module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Gap1920b
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.GapsNineteenTwenty
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTenJFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

variable {G : Type} [Group G] [Finite G]

theorem ctx19_10_atPair {D : Data G} {V₀ V V₀' V' : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} (h125 : Hyp125 D V₀ V) (hbig : 1 < mSub V₀)
    (h : Ctx19_10 D V₀' V' p L A t B r) : Ctx19_10 D V₀ V p L A t B r :=
  { h with hyp := ⟨h125, h.hyp.hp, h.hyp.hL, h.hyp.hX, hbig⟩ }

section CertificatesJFour


theorem gap19_20b_guarded_of (D : Data G)
    (h3 : ∀ V₀ V : Subgroup G, Hyp125 D V₀ V → (Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) →
      S17.R17_3At D V₀ V)
    (h42 : ∀ V₀ V : Subgroup G, Hyp125 D V₀ V → (Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) →
      S17.R17_42At D V₀ V)
    (h1 : ∀ (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G) (h : Hyp19 D V₀ V p L),
      (Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) → R19_1At D V₀ V p L h)
    (h641 : ∀ V₀ V : Subgroup G, Hyp125 D V₀ V → (Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) →
      S17.R17_64_1At D V₀ V)
    (h642 : ∀ V₀ V : Subgroup G, Hyp125 D V₀ V → (Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) →
      S17.R17_64_2At D V₀ V)
    (h643 : ∀ V₀ V : Subgroup G, Hyp125 D V₀ V → (Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) →
      S17.R17_64_3At D V₀ V) :
    ∀ V₀ V : Subgroup G, Hyp125 D V₀ V → 1 < mSub V₀ →
      (Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) → Gap19_20b D := by
  intro V₀ V h125 hbig hg _ _ p L A t B r h heven
  have h' := ctx19_10_atPair h125 hbig h
  refine gap19_20b_at D h' (h3 V₀ V h125 hg) (h42 V₀ V h125 hg) ?_ heven
  intro hj
  obtain ⟨K₁, K₂, hK₁, hK₂, hne, hI, hL1, hL2, hpow, hgt, -, -⟩ :=
    jM_four_structure D h'.hyp (h1 V₀ V p L h'.hyp hg) (h42 V₀ V h125 hg)
      (h641 V₀ V h125 hg) (h642 V₀ V h125 hg) (h643 V₀ V h125 hg) hj
  exact ⟨K₁, K₂, hK₁, hK₂, hne, hI, hL1, hL2, hpow, hgt⟩

end CertificatesJFour

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
