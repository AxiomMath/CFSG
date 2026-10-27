module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinContracts

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem

namespace NSJoin


@[expose] def NSNbrLocalGenInputOf (T : ∀ {ι : Type}, CoxeterMatrix ι → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      NSJoinGuardOf T p L Bs 𝒦 →
      ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
        ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦 →
        ∃ r₀ : MulAut ↥Bs, r₀ ∈ ggAutomizer J Bs ∧ r₀ ^ 2 = 1 ∧ r₀ ≠ 1 ∧ J ≤ K ∧
          (K ≤ ⨆ r : MulAut ↥Bs, ⨆ (_ : r ∈ ggAutomizer K Bs),
            ⨆ (_ : GGIsReflection p r), ggRankOneIn K Bs r) ∧
          (∀ N : Subgroup G, N ≤ ggRankOneIn K Bs r₀ → N ≠ ⊥ →
            (∀ a ∈ ggRankOneIn K Bs r₀, ∀ b ∈ N, a * b * a⁻¹ ∈ N) → ggRankOneIn K Bs r₀ ≤ N) ∧
          (∀ r ∈ ggAutomizer K Bs, GGIsReflection p r →
            ∃ a ∈ ggAutomizer K Bs, a * r₀ * a⁻¹ = r)

@[expose] def NSNbrLocalGenInput : Prop :=
  NSNbrLocalGenInputOf NSTypeAD

theorem nsNbrGenKNInputOf_of_local {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hT3 : ∀ {ι : Type} {M : CoxeterMatrix ι}, T M → ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hGenP : GGSecFiveGenPhanInput) (hPair : GGSecFivePhanPairInput)
    (hLoc : NSNbrLocalGenInputOf T) : NSNbrGenKNInputOf T := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hns hguard y K hK hKA
  obtain ⟨r₀, hr₀J, hr₀2, hr₀1, hJK, hgen, hsimp, horbit⟩ :=
    hLoc G p B Bs x L D J 𝒦 hcfg hns hguard y K hK hKA
  have hC : GGConfig p B Bs x L D J := hcfg.1.1
  have hDB : D ≤ Bs := (hC.2.2.1.1).trans hC.2.1.1
  have hJD : J ≤ Subgroup.centralizer (D : Set G) :=
    (hC.2.2.1.2.2.2.2.2.1.1).trans inf_le_right
  obtain ⟨ι, M, e, hpres, hT, hbig⟩ := hguard
  have hnorm := jnormD_of_phan_gen_pair hGenP hPair hcfg hns hpres (hT3 hT) hbig
  exact genN_of_anchor_simple hgen hr₀J hr₀2 hr₀1 hJK hDB hJD hnorm hsimp horbit

theorem nsNbrGenKNInput_of_local (hGenP : GGSecFiveGenPhanInput) (hPair : GGSecFivePhanPairInput)
    (hLoc : NSNbrLocalGenInput) : NSNbrGenKNInput :=
  nsNbrGenKNInputOf_of_local (T := NSTypeAD) NSTypeAD.le_three hGenP hPair hLoc

end NSJoin

end CFSG.StandardType

end
