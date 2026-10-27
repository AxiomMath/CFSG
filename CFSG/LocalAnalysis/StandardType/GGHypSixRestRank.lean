module

public import CFSG.LocalAnalysis.StandardType.GGHypSixRest

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin

section Inputs

@[expose] def GGD4TrialityCentRankInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (ψ : (ggU .POmegaPlus 4 f).K →* G), 1 ≤ f →
    ψ.ker ≤ Subgroup.center (ggU .POmegaPlus 4 f).K →
    ∀ c ∈ Subgroup.normalizer (ψ.range : Set G),
      c ^ 3 ∈ Subgroup.centralizer (ψ.range : Set G) →
      ¬ GGSpinSemilinear (quadPlus 4 (GaloisField 2 f)) ψ c →
      ∀ E : Subgroup G, E ≤ ψ.range → E ≤ Subgroup.centralizer ({c} : Set G) →
        IsElemAbelian 3 E → Nat.card E ≤ 9

@[expose] def GGHypSixD4BstarRankInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig 3 B Bs x L D J → GGOpAutTrivial 3 Bs → GGInnerDiagAll 3 B Bs x L D J →
      ∀ (f : ℕ) (ψ : (ggU .POmegaPlus 4 f).K →* G),
        GGPresentsG0 (ggG0 3 B x L D J) (ggU .POmegaPlus 4 f).D .POmegaPlus 4 f ψ →
        Bs ≤ Subgroup.normalizer (ggG0 3 B x L D J : Set G) →
          27 ≤ Nat.card ↥(Bs ⊓ ggG0 3 B x L D J)

end Inputs

section Reduction

theorem ggHypSixD4SemilinearInput_of_rank (hK : GGD4TrialityCentRankInput)
    (hR : GGHypSixD4BstarRankInput) : GGHypSixD4SemilinearInput := by
  intro G _ _ B Bs x L D J hcfg hOp hInn f ψ hpres hBsN b hb
  by_contra hns
  have hBs : IsElemAbelian 3 Bs := hcfg.2.1.2.1
  have hcomm : ∀ a ∈ Bs, ∀ a' ∈ Bs, a * a' = a' * a := fun a ha a' ha' =>
    congrArg Subtype.val (hBs.1.is_comm.comm ⟨a, ha⟩ ⟨a', ha'⟩)
  have hE : IsElemAbelian 3 (Bs ⊓ ggG0 3 B x L D J) :=
    ⟨⟨⟨fun a a' => Subtype.ext (hcomm _ a.2.1 _ a'.2.1)⟩⟩, fun a ha => hBs.2 a ha.1⟩
  have hEc : Bs ⊓ ggG0 3 B x L D J ≤ Subgroup.centralizer ({b} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm a ha.1 b hb
  have hEψ : Bs ⊓ ggG0 3 B x L D J ≤ ψ.range := by
    rw [hpres.2.1.1]
    exact inf_le_right
  have h9 := hK G f ψ hpres.1.1.2.1 hpres.2.1.2 b
    (mem_normalizer_range_of_bstar hpres.2.1.1 hBsN hb)
    (pow_mem_centralizer_range_of_bstar hcfg ψ hb) hns _ hEψ hEc hE
  have h27 := hR G B Bs x L D J hcfg hOp hInn f ψ hpres hBsN
  omega

end Reduction

end CFSG.StandardType
