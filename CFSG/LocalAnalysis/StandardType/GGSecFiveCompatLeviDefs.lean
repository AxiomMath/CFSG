module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1WeylE

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.ClassicalInvolution.WeakCT

section Inputs

@[expose] def GGLeviPresented {G : Type} [Group G] [Finite G] (H : Subgroup G) {ι : Type}
    (R : ι → Subgroup G) : Prop :=
  ∃ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    (t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) ∧ 3 ≤ bnRank t n ∧
    GGPresentsG0 H (ggU t n f).D t n f ψ ∧
      ∃ σ : Fin (ggU t n f).D.rank ≃ ι, ∀ k,
        (CFSG.LieType.CurtisTits.rankOne (ggU t n f).D.rootGroup k).map ψ = R (σ k)

@[expose] def GGSecFiveCompatLeviInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (GGIsWeylMatrixAD M ∨ GGIsWeylMatrixE M) →
        ∀ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
          (t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) →
          GGPresentsG0 (L ⊔ ⨆ K ∈ 𝒦, K) (ggU t n f).D t n f ψ →
          ∀ σ : Fin (ggU t n f).D.rank ≃ ι,
            (∀ k, (CFSG.LieType.CurtisTits.rankOne (ggU t n f).D.rootGroup k).map ψ =
              ggRankOnePerf Bs ((e (M.simple (σ k)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) →
          GGCompatPresented (ggU t n f).D ψ L

@[expose] def GGSecFiveIdentCompatADInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → GGIsWeylMatrixAD M →
          ∃ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G), 3 ≤ bnRank t n ∧
            GGPresentsG0 (L ⊔ ⨆ K ∈ 𝒦, K) (ggU t n f).D t n f ψ ∧
              GGCompatPresented (ggU t n f).D ψ L

@[expose] def GGSecFiveIdentCompatEInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → GGIsWeylMatrixE M →
          ∃ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G), 3 ≤ bnRank t n ∧
            GGPresentsG0 (L ⊔ ⨆ K ∈ 𝒦, K) (ggU t n f).D t n f ψ ∧
              GGCompatPresented (ggU t n f).D ψ L

theorem GGLeviPresented.ident {G : Type} [Group G] [Finite G] {H : Subgroup G} {ι : Type}
    {R : ι → Subgroup G} (h : GGLeviPresented H R) :
    ∃ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G), 3 ≤ bnRank t n ∧
      GGPresentsG0 H (ggU t n f).D t n f ψ := by
  obtain ⟨t, n, f, ψ, -, h3, hP, -⟩ := h
  exact ⟨t, n, f, ψ, h3, hP⟩

theorem GGLeviPresented.compat (hC : GGSecFiveCompatLeviInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hsplit : GGSplitLie p L) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hM : GGIsWeylMatrixAD M ∨ GGIsWeylMatrixE M)
    (h : GGLeviPresented (L ⊔ ⨆ K ∈ 𝒦, K)
      (fun i : ι => ggRankOnePerf Bs ((e (M.simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs))) :
    ∃ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G), 3 ≤ bnRank t n ∧
      GGPresentsG0 (L ⊔ ⨆ K ∈ 𝒦, K) (ggU t n f).D t n f ψ ∧
        GGCompatPresented (ggU t n f).D ψ L := by
  obtain ⟨t, n, f, ψ, ht, h3, hP, σ, hσ⟩ := h
  exact ⟨t, n, f, ψ, h3, hP,
    hC G p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hM t n f ψ ht hP σ hσ⟩

end Inputs

end CFSG.StandardType

end
