module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutDefs
public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSLRank
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionRank

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Reduction

theorem ggU_PSU_rank (n f : ℕ) (hf : 1 ≤ f) : (ggU .PSU n f).D.rank = n / 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e : lieUniversal .PSU n 2 f Nat.prime_two =
      ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
        Unitary.rootDatum (card_galoisField_two_mul 2 f hf) n⟩ := by
    simp only [lieUniversal, hf, ↓reduceDIte]
  change (lieUniversal .PSU n 2 f Nat.prime_two).D.rank = n / 2
  rw [e]
  rfl

theorem GGSixFusionSetting.linearCase_of_config {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs G₀ : Subgroup G} {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (hS : GGSixFusionSetting p Bs G₀ (ggU t n f).D t n f ψ)
    (h24 : GGTwoLocalRankFour p (Subgroup.normalizer (G₀ : Set G)))
    (hcfg : GGOutdiagPrimeConfig p t n f) (hnp : n = p) : GGSixLinearCase p t n f := by
  have hp := hS.prime
  have hp2 := hS.ne_two
  obtain ⟨⟨hadm, hrank⟩, ⟨hrange, hker⟩, -, -⟩ := hS.presents
  have hf : 1 ≤ f := hadm.2.1
  have hp4 : p ≠ 4 := by
    rintro rfl
    exact absurd hp (by norm_num)
  have h5 : p ≠ 3 → 5 ≤ p := fun h3 => by have := hp.two_le; omega
  rcases hcfg with ⟨rfl, -, hq⟩ | ⟨rfl, -, hq⟩ | ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩
  · refine ⟨h5 fun h3 => ?_, hnp, Or.inl ⟨rfl, hq⟩⟩
    subst h3
    subst hnp
    have hC' : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
      rw [hrange]
      exact hS.centralizer_eq_bot
    have hBsN : Bs ≤ Subgroup.normalizer (ψ.range : Set G) := by
      rw [hrange]
      exact hS.bstar_le
    exact AutPSL.pslThreeRankInput_holds G f ψ hf hker hC' 3 Bs hp hp2 hS.elem
      (hS.pow_four_le h24) hBsN hS.innerDiag
  · refine ⟨h5 fun h3 => ?_, hnp, Or.inr ⟨rfl, hq⟩⟩
    subst h3
    subst hnp
    rw [ggU_PSU_rank 3 f hf] at hrank
    omega
  · exact absurd (hnp.symm.trans hadm.2.2) (by omega)
  · exact absurd (hnp.symm.trans hadm.2.2) (by omega)

theorem ggSixLSixElevenKGInput_of_kinds (h1 : ∀ t, GGOrdPInnerConjAt t)
    (h2 : ∀ t, GGOrdPFieldConjAt t) (h3 : ∀ t, GGOrdPOutdiagAt t) (h4 : ∀ t, GGOrdPGraphAt t)
    (h5 : GGOrdPTrialityInput) : GGSixLSixElevenKGInput := by
  intro G _ _ p Bs G₀ t n f ψ hS h24 b hb y hyM hyo hnc hemb
  have hyp : y ^ p = 1 := by
    rw [← hyo]
    exact pow_orderOf_eq_one y
  by_cases hDF : GGPsiDiagField (ggU t n f).D ψ y
  · left
    by_cases hID : GGPsiInnerDiag (ggU t n f).D ψ y
    · by_cases hcfg : GGOutdiagPrimeConfig p t n f
      · exact hS.linearCase_of_config h24 hcfg
          (h3 t G p Bs G₀ n f ψ hS h24 hcfg b hb y hyM hyo hID hnc hemb)
      · obtain ⟨m, hm, hmc⟩ := h1 t G p Bs G₀ n f ψ hS h24 hcfg y hyM hyo hID
        exact absurd hmc (hS.not_conj_mem_centralizer hyp hnc hm)
    · obtain ⟨m, hm, hmc⟩ := h2 t G p Bs G₀ n f ψ hS h24 y hyM hyo hDF hID
      exact absurd hmc (hS.not_conj_mem_centralizer hyp hnc hm)
  · right
    obtain ⟨rfl, rfl, rfl⟩ := h4 t G n f ψ G₀ hS.presents hS.centralizer_eq_bot p hS.prime
      hS.ne_two y hyM hyp hDF
    obtain ⟨hq, hL⟩ := h5 G Bs G₀ f ψ hS h24 b hb y hyM hyo hDF hemb
    exact ⟨rfl, rfl, rfl, hq, fun hI => hDF hI.diagField, hL⟩

@[expose] def GGOrdPSmallTag (t : StatedLieTag) : Prop :=
  t = .G2 ∨ t = .trialityD4 ∨ t = .twistedB2 ∨ t = .twistedG2 ∨ t = .twistedF4 ∨ t = .Tits ∨
    t = .POmegaOdd

theorem not_ggPresentsG0_of_small {t : StatedLieTag} (ht : GGOrdPSmallTag t) {G : Type} [Group G]
    {n f : ℕ} {ψ : (ggU t n f).K →* G} {G₀ : Subgroup G} :
    ¬ GGPresentsG0 G₀ (ggU t n f).D t n f ψ := by
  rintro ⟨⟨hadm, hrank⟩, -⟩
  rcases ht with ht | ht | ht | ht | ht | ht | rfl
  · have h0 : (ggU t n f).D.rank = 0 := lieUniversal_rank_eq_zero t n 2 f Nat.prime_two (Or.inl ht)
    omega
  · have h0 : (ggU t n f).D.rank = 0 :=
      lieUniversal_rank_eq_zero t n 2 f Nat.prime_two (Or.inr (Or.inl ht))
    omega
  · have h0 : (ggU t n f).D.rank = 0 :=
      lieUniversal_rank_eq_zero t n 2 f Nat.prime_two (Or.inr (Or.inr (Or.inl ht)))
    omega
  · have h0 : (ggU t n f).D.rank = 0 :=
      lieUniversal_rank_eq_zero t n 2 f Nat.prime_two (Or.inr (Or.inr (Or.inr (Or.inl ht))))
    omega
  · have h0 : (ggU t n f).D.rank = 0 := lieUniversal_rank_eq_zero t n 2 f Nat.prime_two
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ht)))))
    omega
  · have h0 : (ggU t n f).D.rank = 0 := lieUniversal_rank_eq_zero t n 2 f Nat.prime_two
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ht)))))
    omega
  · exact hadm.2.2.2 rfl

theorem ggOrdPInnerConjAt_of_small {t : StatedLieTag} (ht : GGOrdPSmallTag t) :
    GGOrdPInnerConjAt t := by
  intro G _ _ p Bs G₀ n f ψ hS
  exact absurd hS.presents (not_ggPresentsG0_of_small ht)

theorem ggOrdPFieldConjAt_of_small {t : StatedLieTag} (ht : GGOrdPSmallTag t) :
    GGOrdPFieldConjAt t := by
  intro G _ _ p Bs G₀ n f ψ hS
  exact absurd hS.presents (not_ggPresentsG0_of_small ht)

theorem ggOrdPOutdiagAt_of_small {t : StatedLieTag} (ht : GGOrdPSmallTag t) :
    GGOrdPOutdiagAt t := by
  intro G _ _ p Bs G₀ n f ψ hS
  exact absurd hS.presents (not_ggPresentsG0_of_small ht)

theorem ggOrdPGraphAt_of_small {t : StatedLieTag} (ht : GGOrdPSmallTag t) : GGOrdPGraphAt t := by
  intro G _ _ n f ψ G₀ hpres
  exact absurd hpres (not_ggPresentsG0_of_small ht)

theorem ggOrdPOutdiagAt_of_not {t : StatedLieTag}
    (ht : t ≠ .PSL ∧ t ≠ .PSU ∧ t ≠ .E6 ∧ t ≠ .twistedE6) : GGOrdPOutdiagAt t := by
  intro G _ _ p Bs G₀ n f ψ _ _ hcfg
  rcases hcfg with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact absurd h ht.1
  · exact absurd h ht.2.1
  · exact absurd h ht.2.2.1
  · exact absurd h ht.2.2.2

end Reduction

end CFSG.StandardType
