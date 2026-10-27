module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerTclNorm
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerTclInd

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary Matrix

variable {G : Type} [Group G] [Finite G]

theorem qTwoLMDivCoordInner_tclauses {B Bs L : Subgroup G} {x : G} (hG : GGThmIHyp 3 B x L)
    (hBs : GGBstar 3 B Bs) (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {m : ℕ} (hm : 6 ≤ m)
    (h3 : 3 ∣ m)
    {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {L0 : Type} [Group L0]
    {c : ↥L →* L0} {π : Su F0 2 1 m →* L0} {ρ : ↥Bs →* MulAut L0}
    (hU : QTwoDivInnerFrame m Bs L hN F0 L0 c π ρ) {δ : ↥(sumZero m 3) →* Su F0 2 1 m}
    (hδ : QTwoDivTorus h3 δ) {τ : ↥(sumZero m 3) →* ↥L} (hτ : QTwoDivLift Bs L c π δ τ)
    (hrange : ∀ t : ↥L, (t : G) ∈ Bs → ∃ f, τ f = t)
    (hsplit : ∀ b ∈ Bs, ∃ t : ↥L, (t : G) ∈ Bs ∧ ∃ k : ℕ, b = (t : G) * x ^ k) :
    (∀ n : ↥L, (n : G) ∈ Subgroup.normalizer (Bs : Set G) →
      ∃ π' : Equiv.Perm (Fin m), ∀ f,
        (n : G) * ((τ f : ↥L) : G) * (n : G)⁻¹ = ((τ (permAutV π' f) : ↥L) : G)) ∧
    ∀ σ : Equiv.Perm (Fin m), ∃ n : ↥L, (n : G) ∈ Subgroup.normalizer (Bs : Set G) ∧
      ∀ f, (n : G) * ((τ f : ↥L) : G) * (n : G)⁻¹ = ((τ (permAutV σ f) : ↥L) : G) :=
  ⟨qTwoLMDivCoordInner_tcl_norm hBs hN (by omega) h3 hU hδ hτ hrange,
    qTwoLMDivCoordInner_tcl_ind hG hBs hN h3 hU hδ hτ hrange hsplit⟩

end CFSG.StandardType.QTwo

end
