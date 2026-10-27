module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenAltProof

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Ctx

variable {G : Type} [Group G] [Finite G] {U : Type} [Group U] {p : ℕ} {B Bs : Subgroup G}
  {x : G} {L D J : Subgroup G} {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ}
  {ψ : U →* G}

theorem GGSixCtxV2.centralizer_le_ggM_of_lieData (hctx : GGSixCtxV2 p B Bs x L D J Δ t n f ψ)
    (hodd : Odd (Nat.card (Subgroup.centralizer (ggG0 p B x L D J : Set G))))
    (hZ : ∀ d ∈ D, d ≠ 1 → Odd (Nat.card (Subgroup.center ↥(ggKd p B x L D J d))))
    {R J₀ : Subgroup G} (hRJ : R ≤ J) (hR1 : R ≠ ⊥) (hR2 : IsPGroup 2 R) (hJ₀J : J₀ ≤ J)
    (hgen : ggQR p B x L D J R ⊔ J₀ = ggG0 p B x L D J)
    (hper : ∀ d ∈ D, d ≠ 1 →
      ggSR p B x L D J R ⊓ Subgroup.centralizer {d} ≤
        ggKd p B x L D J d ⊔ Subgroup.centralizer (ggKd p B x L D J d : Set G) ∧
      ∀ A B' : Subgroup G, R ≤ A → A ≤ B' →
        B' ≤ pCoreOf 2 (ggKd p B x L D J d ⊓ Subgroup.normalizer (R : Set G)) →
        ggKd p B x L D J d ⊓ Subgroup.normalizer (R : Set G) ≤
          Subgroup.normalizer (A : Set G) →
        ggKd p B x L D J d ⊓ Subgroup.normalizer (R : Set G) ≤
          Subgroup.normalizer (B' : Set G) →
        ⁅B', ggKd p B x L D J d ⊓ Subgroup.normalizer (R : Set G)⁆ ≤ A → B' ≤ A)
    (h3 : ggSR p B x L D J R ≤ ggM p B x L D J →
      ⁅ggSR p B x L D J R, ggG0 p B x L D J ⊓ Subgroup.normalizer (R : Set G)⁆ ≤
        ggQR p B x L D J R →
      ggSR p B x L D J R ≤
        ggG0 p B x L D J ⊔ Subgroup.centralizer (ggG0 p B x L D J : Set G))
    (h4 : (⁅ggQR p B x L D J R, ggQR p B x L D J R⁆ ≤ R ∧
        ggQR p B x L D J R ≤ Subgroup.centralizer (R : Set G)) ∨
      ∀ U : Subgroup G, ggCenterOf (ggQR p B x L D J R) ≤ U → U ≤ ggQR p B x L D J R →
        U ≠ ggCenterOf (ggQR p B x L D J R) → U ≠ ggQR p B x L D J R →
        ggG0 p B x L D J ⊓ Subgroup.normalizer (R : Set G) ≤
          Subgroup.normalizer (U : Set G) →
        J ⊔ U = ggG0 p B x L D J) :
    Subgroup.centralizer (J : Set G) ≤ ggM p B x L D J :=
  hctx.centralizer_le_ggM_of_data hodd hRJ hR1 hR2 hJ₀J hgen
    (hctx.ggSR_le_of_perD hRJ fun d hd hd1 => hctx.perD_of_inner hRJ hR2 hd
      (hctx.perD_pOne_of_inner hRJ hd (hZ d hd hd1) (hper d hd hd1).1) (hper d hd hd1).2)
    (fun hSM hSN => hctx.sQC_of_inner hRJ hodd (h3 hSM hSN))
    (ggSixLSevenItemFour_of_alt p B x L D J R h4)

end Ctx

section Inputs

@[expose] def GGSixLSixSevenCentJE6Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    Subgroup.centralizer (D : Set G) ≤ ggM p B x L D J →
    Odd (Nat.card (Subgroup.centralizer (ggG0 p B x L D J : Set G))) →
    (∀ d ∈ D, d ≠ 1 → IsComponentOf (ggKd p B x L D J d) (Subgroup.centralizer {d})) →
    GGSixLSevenE6Case p L J t f →
      Subgroup.centralizer (J : Set G) ≤ ggM p B x L D J

@[expose] def GGSixLSixSevenConjA3At (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    Subgroup.centralizer (D : Set G) ≤ ggM p B x L D J →
    Odd (Nat.card (Subgroup.centralizer (ggG0 p B x L D J : Set G))) →
    (∀ d ∈ D, d ≠ 1 → IsComponentOf (ggKd p B x L D J d) (Subgroup.centralizer {d})) →
    GGSixLSevenA3Case J →
      ∃ g ∈ ggG0 p B x L D J, D.map (MulAut.conj g).toMonoidHom ≤ J

theorem ggSixLSixSevenConjA3Input_of_tags (h : ∀ t, GGSixLSixSevenConjA3At t) :
    GGSixLSixSevenConjA3Input :=
  fun G _ _ p B Bs x L D J t n f ψ => h t G p B Bs x L D J n f ψ

end Inputs

end CFSG.StandardType
