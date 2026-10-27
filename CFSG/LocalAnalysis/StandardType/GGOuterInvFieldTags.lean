module

public import CFSG.LocalAnalysis.StandardType.GGOTwoStarFrame
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerMinus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

@[expose] def GGO2CentralizerG0At
    (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      ∀ b ∈ Bs, b ≠ 1 → pCoreOf 2 (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}) = ⊥

@[expose] def GGFieldOuterInvAt
    (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      ∀ (b : G) (L₁ : Subgroup G), b ∈ Bs → b ≠ 1 →
        IsComponentOf L₁ (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}) →
        ∀ r ∈ ggM p B x L D J, orderOf r = 2 → r ∈ Subgroup.centralizer {b} →
          r ∉ ggG0 p B x L D J →
            ¬ ggG0 p B x L D J ⊓ Subgroup.centralizer {b} ≤ Subgroup.centralizer {r}

theorem ggOuterInvAt_of_fieldOuter
    {t : StatedLieTag} (hd : GGPsiDiagInnerAt t) (h2 : GGO2CentralizerG0At t)
    (h5 : GGFieldOuterInvAt t) : GGOuterInvAt t := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 b L₁ hb hb1 hL₁ m hm hEC r hr hr2
  exfalso
  have hO2 : pCoreOf 2 (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}) = ⊥ :=
    h2 G p B Bs x L D J n f ψ hctx s1 b hb hb1
  have hR := ggR_inf_ggG0_eq_bot_of_diagInner hd hctx s1 hO2
  have hrM : r ∈ ggM p B x L D J :=
    (pCoreOf_le' 2 (ggM p B x L D J ⊓ Subgroup.centralizer {b}) hr).1
  have hrb : r ∈ Subgroup.centralizer {b} :=
    (pCoreOf_le' 2 (ggM p B x L D J ⊓ Subgroup.centralizer {b}) hr).2
  have hrnotG0 : r ∉ ggG0 p B x L D J := by
    intro hrG0
    have hmem : r ∈ pCoreOf 2 (ggM p B x L D J ⊓ Subgroup.centralizer {b}) ⊓
        ggG0 p B x L D J := Subgroup.mem_inf.mpr ⟨hr, hrG0⟩
    rw [hR.1, Subgroup.mem_bot] at hmem
    rw [hmem, orderOf_one] at hr2
    exact absurd hr2 (by norm_num)
  have hle : ggG0 p B x L D J ⊓ Subgroup.centralizer {b} ≤
      Subgroup.centralizer {r} := by
    intro c hc
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (hR.2 hr) c hc
  exact (h5 G p B Bs x L D J n f ψ hctx s1 b L₁ hb hb1 hL₁ r hrM hr2 hrb
    hrnotG0) hle

theorem ggOuterInvAt_of_fieldTags
    {t : StatedLieTag} (ht : t = .PSp ∨ t = .F4 ∨ t = .E7 ∨ t = .E8)
    (h2 : GGO2CentralizerG0At t) (h5 : GGFieldOuterInvAt t) : GGOuterInvAt t := by
  have hd : GGPsiDiagInnerAt t :=
    ggPsiDiagInnerAt_of_ggInnerTag t (by
      rcases ht with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  exact ggOuterInvAt_of_fieldOuter hd h2 h5

end CFSG.StandardType
