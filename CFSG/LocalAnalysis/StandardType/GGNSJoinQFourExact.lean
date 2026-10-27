module

public import CFSG.LocalAnalysis.StandardType.GGMemberRowsDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveL1PhanLocal
public import CFSG.LocalAnalysis.StandardType.GGNSJoinQFourRows
public import CFSG.LocalAnalysis.StandardType.GGNSJoinQFourUniOrd

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Defs

variable {G : Type} [Group G] [Finite G]

@[expose] def GGRk1ConclEx (p : ℕ) (Bs X : Subgroup G) (r : MulAut ↥Bs) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F)
    (θ : Matrix.SpecialLinearGroup (Fin 2) F →* G), CharP F 2 ∧
    Function.Injective θ ∧ θ.range = ggRankOneIn X Bs r ∧
    (∃ n ∈ ggRankOneIn X Bs r, n ∈ Subgroup.normalizer (Bs : Set G) ∧
      ∀ b : ↥Bs, ((r b : ↥Bs) : G) = n * b * n⁻¹) ∧
    (GGSplitLie p X → p ∣ Nat.card F - 1) ∧
    (¬ GGSplitLie p X → p ∣ Nat.card F + 1) ∧
    (∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
      GGHasLabel lab (↥X ⧸ Subgroup.center ↥X) → 2 ^ lab.n ≤ Nat.card F) ∧
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧
      GGHasLabel lab (↥X ⧸ Subgroup.center ↥X) ∧ Nat.card F = 2 ^ lab.n

theorem GGRk1ConclEx.toConcl {p : ℕ} {Bs X : Subgroup G} {r : MulAut ↥Bs}
    (h : GGRk1ConclEx p Bs X r) : GGRk1Concl p Bs X r := by
  obtain ⟨F, hF, hFin, θ, hchar, hinj, hrange, hrep, hs, hns, hlab, -⟩ := h
  exact ⟨F, hF, hFin, θ, hchar, hinj, hrange, hrep, hs, hns, hlab⟩

end Defs

@[expose] def GGRk1ResidualMemberInputEx : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (∀ i j : ι, i ≠ j → M.M i j ≤ 3) →
        ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) → ¬ GGSplitLie p X → ¬ GGMemberUnitary p Bs X →
          ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e → GGRk1ConclEx p Bs X r

theorem GGRk1ResidualMemberInputEx.toResidual (h : GGRk1ResidualMemberInputEx) :
    GGRk1ResidualMemberInput :=
  fun G _ _ p B Bs x L D J 𝒦 hcfg hns ι M e hpres h3 X hX hXns hU r hrA hrC =>
    (h G p B Bs x L D J 𝒦 hcfg hns ι M e hpres h3 X hX hXns hU r hrA hrC).toConcl

namespace NSJoin

theorem nsQFourInputOf_mono {T T' : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (h : ∀ {ι : Type} {M : CoxeterMatrix ι}, T' M → T M) (hq : NSQFourInputOf T) :
    NSQFourInputOf T' :=
  fun G _ _ p B Bs x L D J 𝒦 hreg =>
    hq G p B Bs x L D J 𝒦 ⟨hreg.1, hreg.2.1, NSJoinGuardOf.mono h hreg.2.2⟩

theorem nsQFourInputOf_of_exactRk1 {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hT : ∀ {ι : Type} {M : CoxeterMatrix ι}, T M → ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hRig : GGLabelRigidInput) (hRk1 : GGRk1ResidualMemberInputEx)
    (hGenR : GGGenResidualMemberInput) : NSQFourInputOf T := by
  intro G _ _ p B Bs x L D J 𝒦 hreg
  by_cases hU : GGMemberUnitary p Bs L
  · exact nsQFourRow_uniOrd hT hRig G p B Bs x L D J 𝒦 hreg hU
  · obtain ⟨hcfg, hns, ι, M, e, hpres, hTM, hbig⟩ := hreg
    have h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := hT hTM
    obtain ⟨r₀, hA, hC⟩ :=
      ggSecFiveBaseReflInput_of_rows hGenR G p B Bs x L D J 𝒦 hcfg hns ι M e hpres h3 hbig
    obtain ⟨F, hFfield, hFfin, θ, hchar, hinj, hrange, -, -, -, -, lab, hΛ, hhas, hFcard⟩ :=
      hRk1 G p B Bs x L D J 𝒦 hcfg hns ι M e hpres h3 L (Or.inl rfl) hns hU r₀ hA hC
    letI : Field F := hFfield
    letI : Finite F := hFfin
    have hcard : Nat.card ↥(ggRankOneIn L Bs r₀) = Nat.card F * (Nat.card F ^ 2 - 1) := by
      rw [← hrange, ← ggSL2_card F]
      exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
    have hguard := hbig r₀ hA hC
    rw [hcard, hFcard] at hguard
    have hn1 : 1 ≤ lab.n := hΛ.1
    have hn2 : 2 ≤ lab.n := by
      by_contra hlt
      have : lab.n = 1 := by omega
      rw [this] at hguard
      exact hguard (by norm_num)
    exact largeEvenMarking_mono (fun lab' _ _ _ _ _ ⟨he, hP⟩ => ⟨by
        unfold GGLabQFour; rw [he]; exact hn2, hP⟩)
      (ggInnerDiagOn_relabel hRig hcfg.1.2.2.1.1 hΛ hhas)

end NSJoin

end CFSG.StandardType

end
