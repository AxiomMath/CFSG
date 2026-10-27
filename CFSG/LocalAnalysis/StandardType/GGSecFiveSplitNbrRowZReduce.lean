module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeakNbr
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowZKSide
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggRowZ_absurd_of_detElt (hRig : GGLabelRigidInput) {S : ℕ → LargeEvenLabel → Prop}
    (hF : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
      S p lab → GGDetAt p lab) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {K : Subgroup G} (hK : GGSecFiveWeakNbr p B Bs x L D J 𝒦 K)
    (hrow : GGInnerDiagOnLabel S p Bs K) : False := by
  obtain ⟨hp, hodd⟩ := ggRouteCfg_prime hcfg
  obtain ⟨y, hnb⟩ := hK.1
  have hInnK : GGInnerDiagOn Bs K := hcfg.1.2.2.1.2 y K hnb
  obtain ⟨lab, hΛ, hhas, R, _, I, _, θ, hS, -⟩ := largeEvenMarking_exists_hasLabel hrow
  obtain ⟨c, hc, hP, hcomm, hexp, hdet⟩ :=
    ggNbr_exists_detElt hRig hcfg.1.1 hnb hInnK hΛ hhas (hF p hp hodd lab hΛ hS)
  exact hdet (ggDet_sq_eq_one_of_reflGen hP hcomm hexp (hcfg.2.1 y K hnb) hc)

end CFSG.StandardType

end
