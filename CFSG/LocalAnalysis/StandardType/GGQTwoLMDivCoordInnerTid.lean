module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerTidRange
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerTidSplit

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary Matrix

variable {G : Type} [Group G] [Finite G]

theorem qTwoLMDivCoordInner_tident {B Bs L : Subgroup G} {x : G} (hG : GGThmIHyp 3 B x L)
    (hBs : GGBstar 3 B Bs) (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {m : ℕ} (hm : 6 ≤ m)
    (h3 : 3 ∣ m)
    {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {L0 : Type} [Group L0]
    {c : ↥L →* L0} {π : Su F0 2 1 m →* L0} {ρ : ↥Bs →* MulAut L0}
    (hU : QTwoDivInnerFrame m Bs L hN F0 L0 c π ρ) {δ : ↥(sumZero m 3) →* Su F0 2 1 m}
    (hδ : QTwoDivTorus h3 δ) {τ : ↥(sumZero m 3) →* ↥L} (hτ : QTwoDivLift Bs L c π δ τ)
    (hcard : Nat.card Bs = 3 ^ (m - 1)) :
    (∀ t : ↥L, (t : G) ∈ Bs → ∃ f, τ f = t) ∧
      ∀ b ∈ Bs, ∃ t : ↥L, (t : G) ∈ Bs ∧ ∃ k : ℕ, b = (t : G) * x ^ k :=
  ⟨qTwoLMDivCoordInner_tid_range hBs hN (by omega) h3 hU hδ hτ,
    qTwoLMDivCoordInner_tid_split hG hBs hN hm h3 hU hδ hτ hcard⟩

end CFSG.StandardType.QTwo

end
