module

public import CFSG.LocalAnalysis.StandardType.GGExcStdForm
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank

section KnownGroups

@[expose] def GGKnownSetting {G : Type} [Group G] (t : StatedLieTag) (n f : ℕ)
    (ψ : (ggU t n f).K →* G) : Prop :=
  (StatedLieAdmissible t n 2 f ∧ 2 ≤ (ggU t n f).D.rank) ∧
    ψ.ker ≤ Subgroup.center (ggU t n f).K ∧
    (commutator ↥ψ.range = ⊤ ∧ LieModel (↥ψ.range ⧸ Subgroup.center ↥ψ.range) t n 2 f) ∧
    Subgroup.centralizer (ψ.range : Set G) = ⊥

@[expose] def GGExcKGRank : Prop :=
  ∀ (t : StatedLieTag) (n f : ℕ), GGExcFive t → ∀ (G : Type) [Group G] [Finite G]
    (ψ : (ggU t n f).K →* G), GGKnownSetting t n f ψ →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ GGExcRegime p f →
      ¬ (t = .E8 ∧ orderOf ((2 : ZMod p) ^ f) ∈ ({3, 4, 6} : Set ℕ)) →
      ∀ E : Subgroup G, E ≤ Subgroup.normalizer (ψ.range : Set G) → IsElemAbelian p E →
        (∀ b ∈ E, GGPsiInnerDiag (ggU t n f).D ψ b) → Nat.card E ≤ p ^ 3

@[expose] def GGExcKGRankTwE6 : Prop :=
  ∀ (n f : ℕ) (G : Type) [Group G] [Finite G]
    (ψ : (ggU .twistedE6 n f).K →* G), GGKnownSetting .twistedE6 n f ψ →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ GGExcRegime p f →
      ∀ E : Subgroup G, E ≤ Subgroup.normalizer (ψ.range : Set G) → IsElemAbelian p E →
        (∀ b ∈ E, GGPsiInnerDiag (ggU .twistedE6 n f).D ψ b) → Nat.card E ≤ p ^ 3

@[expose] def GGExcKGBorelTits : Prop :=
  ∀ (n f : ℕ) (G : Type) [Group G] [Finite G] (ψ : (ggU .E8 n f).K →* G),
    GGKnownSetting .E8 n f ψ → ∀ p : ℕ, p.Prime → p ≠ 2 →
      orderOf ((2 : ZMod p) ^ f) ∈ ({3, 4, 6} : Set ℕ) →
      ∀ E : Subgroup G, E ≤ Subgroup.normalizer (ψ.range : Set G) → IsElemAbelian p E →
        p ^ 4 ≤ Nat.card E → (∀ b ∈ E, GGPsiInnerDiag (ggU .E8 n f).D ψ b) →
        ∀ T : Subgroup G, T ≤ Subgroup.normalizer (ψ.range : Set G) → IsPGroup 2 T →
          E ≤ Subgroup.normalizer (T : Set G) → E ≤ Subgroup.centralizer (T : Set G)

@[expose] def GGExcKGStdForm : Prop :=
  ∀ (t : StatedLieTag) (n f : ℕ), GGExcFive t → ∀ (G : Type) [Group G] [Finite G]
    (ψ : (ggU t n f).K →* G), GGKnownSetting t n f ψ →
    ∀ p : ℕ, p.Prime → p ≠ 2 → GGExcRegime p f →
    ∀ Bs : Subgroup G, IsElemAbelian p Bs → p ^ 4 ≤ Nat.card Bs →
      Bs ≤ Subgroup.normalizer (ψ.range : Set G) →
      (∀ b ∈ Bs, GGPsiInnerDiag (ggU t n f).D ψ b) →
      (∃ P : Sylow p (Subgroup.normalizer (ψ.range : Set G)),
        Bs ≤ (P : Subgroup (Subgroup.normalizer (ψ.range : Set G))).map
          (Subgroup.normalizer (ψ.range : Set G)).subtype ∧
        ∀ E : Subgroup G, E ≤ (P : Subgroup (Subgroup.normalizer (ψ.range : Set G))).map
          (Subgroup.normalizer (ψ.range : Set G)).subtype →
          IsElemAbelian p E → Nat.card E = Nat.card Bs → E = Bs) →
      ∃ (S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ)
        (π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank))
        (F : GGStdForm p Bs ψ.range (ggU (absTag t) 6 f).D S π f),
        IsRootGram (ggU (absTag t) 6 f).D S ∧ IsDiagAut (ggU (absTag t) 6 f).D π ∧
        (t = .F4 ∨ t = .E7 ∨ t = .E8 → π = 1) ∧
        (t = .E6 → (π = 1 ↔ p ∣ 2 ^ f - 1)) ∧
        (t = .twistedE6 → (π = 1 ↔ p ∣ 2 ^ f + 1)) ∧
        (∀ α ∈ (ggU (absTag t) 6 f).D.roots, latPerm π α = α →
          ∃ (γ : Fin (ggU t n f).D.rank → ℤ) (u : (ggU t n f).K),
            GGRootClass (ggU t n f).D t γ ∧
            (∀ b : Bs, latChar p (Multiplicative.toAdd (F.coord b)) α = 0 →
              (b : G) ∈ Subgroup.centralizer (ggRootSub (ggU t n f).D ψ γ u : Set G)) ∧
            ∃ r ∈ ggRootSub (ggU t n f).D ψ γ u, orderOf r = 2) ∧
        (∀ α ∈ (ggU t n f).D.roots, GGRootClass (ggU t n f).D t α →
          (∃ x' ∈ ggRankOneSub (ggU t n f).D ψ α, orderOf x' = p) ∧
          ∀ x' ∈ ggRankOneSub (ggU t n f).D ψ α, orderOf x' = p →
            ∃ h ∈ ψ.range, ∃ αB ∈ (ggU (absTag t) 6 f).D.roots, latPerm π αB = αB ∧
              ∃ k : ZMod p, k ≠ 0 ∧ ∃ b : Bs, (b : G) = h * x' * h⁻¹ ∧
                Multiplicative.toAdd (F.coord b) = k • corootCoord p S αB)

@[expose] def GGExcKGInvolutions
    (ASClass : ∀ (t : StatedLieTag) (n f : ℕ), Set (Fin (ggU t n f).D.rank → ℤ) → Prop) : Prop :=
  ∀ (t : StatedLieTag) (n f : ℕ), GGExcFive t → ∀ (G : Type) [Group G] [Finite G]
    (ψ : (ggU t n f).K →* G), GGKnownSetting t n f ψ →
    ∀ s ∈ ψ.range, orderOf s = 2 →
      ∃ g ∈ ψ.range, ∃ Z : Set (Fin (ggU t n f).D.rank → ℤ), ASClass t n f Z ∧
        g * s * g⁻¹ ∈ ⨆ β ∈ Z, ((ggU t n f).D.rootGroup β).map ψ

private theorem pow_four_le_card_of_ctx {G : Type} [Group G] [Finite G] {U : Type} [Group U]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {Δ : UniversalRootDatum U}
    {t : StatedLieTag} {n f : ℕ} {ψ : U →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) : p ^ 4 ≤ Nat.card B := by
  have hB : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hctx.sstar.1.2.1
  have h4 : 4 ≤ LargeEvenTwoLocalRank p G := hctx.beta.2.2.2
  rw [hB]
  exact Nat.pow_le_pow_right hctx.prime.pos h4

theorem ggKnownSetting_of_ctx {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) : GGKnownSetting t n f ψ := by
  obtain ⟨-, -, ⟨hadm, hrank⟩, ⟨hrange, hker⟩, ⟨hperf, hmodel⟩, -, -, -⟩ := hctx.2
  refine ⟨⟨hadm, hrank⟩, hker, ⟨?_, ?_⟩, ?_⟩
  · rw [hrange]; exact hperf
  · exact LieModel.of_mulEquiv
      (QuotientGroup.congr (Subgroup.center ↥(ggG0 p B x L D J))
        (Subgroup.center ↥ψ.range) (MulEquiv.subgroupCongr hrange.symm)
        (Subgroup.map_center_eq (MulEquiv.subgroupCongr hrange.symm))) hmodel
  · rw [hrange]; exact s1.1

theorem ggExcRegimeInput_of_known (hrank : GGExcKGRank) (hbt : GGExcKGBorelTits) :
    GGExcRegimeInput := by
  intro G _ _ p B Bs x L D J t n f ψ ht hctx s1
  by_contra hreg
  have hp : p.Prime := hctx.prime
  have hp2 : p ≠ 2 := hctx.ne_two
  have hks : GGKnownSetting t n f ψ := ggKnownSetting_of_ctx hctx s1
  have hBcard4 : p ^ 4 ≤ Nat.card B := pow_four_le_card_of_ctx hctx
  have hBsN : Bs ≤ Subgroup.normalizer (ψ.range : Set G) := by
    rw [hctx.range_eq]; exact hctx.bstar_le_normalizer
  have hBN : B ≤ Subgroup.normalizer (ψ.range : Set G) := hctx.bstar.1.trans hBsN
  have hBelem : IsElemAbelian p B := hctx.sstar.1.1
  have hBinn : ∀ b ∈ (B : Subgroup G), GGPsiInnerDiag (ggU t n f).D ψ b :=
    fun b hb => hctx.2.2.2.2.2.2.1.2 b (hctx.bstar.1 hb)
  by_cases hcase : t = .E8 ∧ orderOf ((2 : ZMod p) ^ f) ∈ ({3, 4, 6} : Set ℕ)
  ·
    obtain ⟨htE8, hord⟩ := hcase
    subst htE8
    obtain ⟨T, -, hT2, hBT, hTne⟩ := hctx.stdType.2.1
    have hDT : D ≤ Subgroup.normalizer (T : Set G) := hctx.stdSub.1.1.trans hBT
    have hcop : Nat.Coprime p (Nat.card T) := by
      obtain ⟨k, hk⟩ := hT2.exists_card_eq
      rw [hk]
      exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    have hTN : T ≤ Subgroup.normalizer (ψ.range : Set G) := by
      have h : T ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) := s1.2.2.1 T hDT hcop
      rw [← hctx.range_eq] at h
      exact h
    have hcent := hbt n f G ψ hks p hp hp2 hord B hBN hBelem hBcard4 hBinn T hTN hT2 hBT
    exact hTne (by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcent)
  ·
    have hle := hrank t n f ht G ψ hks p hp hp2 hreg hcase B hBN hBelem hBinn
    have hlt : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    exact absurd (hBcard4.trans hle) (not_le.mpr hlt)

theorem ggSixExcStandardFormInput_of_known (hstd : GGExcKGStdForm) :
    GGSixExcStandardFormInput := by
  intro G _ _ p B Bs x L D J t n f ψ ht hctx s1 hreg
  have hks : GGKnownSetting t n f ψ := ggKnownSetting_of_ctx hctx s1
  have hcard : p ^ 4 ≤ Nat.card Bs :=
    (pow_four_le_card_of_ctx hctx).trans (Subgroup.card_le_of_le hctx.bstar.1)
  have hBsN : Bs ≤ Subgroup.normalizer (ψ.range : Set G) := by
    rw [hctx.range_eq]; exact hctx.bstar_le_normalizer
  have hinn : ∀ b ∈ (Bs : Subgroup G), GGPsiInnerDiag (ggU t n f).D ψ b :=
    hctx.2.2.2.2.2.2.1.2
  have hsyl : ∃ P : Sylow p (Subgroup.normalizer (ψ.range : Set G)),
      Bs ≤ (P : Subgroup (Subgroup.normalizer (ψ.range : Set G))).map
        (Subgroup.normalizer (ψ.range : Set G)).subtype ∧
      ∀ E : Subgroup G, E ≤ (P : Subgroup (Subgroup.normalizer (ψ.range : Set G))).map
        (Subgroup.normalizer (ψ.range : Set G)).subtype →
        IsElemAbelian p E → Nat.card E = Nat.card Bs → E = Bs := by
    have hnorm : Subgroup.normalizer (ψ.range : Set G) =
        Subgroup.normalizer (ggG0 p B x L D J : Set G) := by rw [hctx.range_eq]
    exact hnorm.symm ▸ s1.2.2.2.1
  rw [← hctx.range_eq]
  exact hstd t n f ht G ψ hks p hctx.prime hctx.ne_two hreg Bs hctx.bstar.2.1 hcard hBsN hinn hsyl

end KnownGroups

end CFSG.StandardType
