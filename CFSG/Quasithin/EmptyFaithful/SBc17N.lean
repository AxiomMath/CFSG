module

public import CFSG.Quasithin.EmptyFaithful.SBc17Call
public import CFSG.Quasithin.EmptyFaithful.SBc17J1
public import CFSG.Quasithin.EmptyFaithful.SBc17Norm
public import CFSG.Quasithin.EmptyFaithful.SBc17Mix
public import CFSG.Quasithin.Background.C2Seven

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

namespace SBc17

variable {G : Type} [Group G]

theorem not_le_pCoreOf_of_quasisimple {J : Subgroup G}
    (hJq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J)) : ¬ J ≤ pCoreOf 2 J := by
  intro h
  have hnt : Nontrivial (↥J ⧸ CFSG.pCore 2 ↥J) := CFSG.LocalCores.isQuasisimple_nontrivial hJq
  obtain ⟨u, hu⟩ := exists_ne (1 : ↥J ⧸ CFSG.pCore 2 ↥J)
  induction u using QuotientGroup.induction_on with | H x => ?_
  apply hu
  rw [QuotientGroup.eq_one_iff, ← SBc13.pCoreOf_subgroupOf_eq_pCore_J1 J]
  exact h x.2

@[expose] def Input14615ContraOuterN : Prop :=
  ∀ (G : Type) [Group G] [Finite G], ASC27Statement G →
    ∀ (T M : Subgroup G), Setting146 G T M →
      ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p →
        ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDecP T M H p H₀ H₁ H₂ t → Ctx15 T M H p H₁ →
          ∀ (K₁ K₂ : Subgroup G) (s : G), Setup14615 T M H H₁ H₂ K₁ K₂ s →
            ¬ g2_14615 K₂ ≤ mcOf T → Gap3Fix T K₁ K₂ →
              HypC23 (g2_14615 K₂) (pCoreOf 2 (mcOf T)) (g12_14615 T K₂) →
                CharTwo (g2_14615 K₂) → pCoreOf 2 (g2_14615 K₂) ≤ g12_14615 T K₂ →
                  ∀ J : Subgroup G, J ∈ cComp (g2_14615 K₂) →
                    CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J) → ¬ J ≤ g12_14615 T K₂ →
                      ⁅J, K₁⁆ = J → pRank 5 J ≤ 1 →
                        K₁ ≤ Subgroup.normalizer (J : Set G) → K₂ ≤ Subgroup.normalizer (J : Set G) →
                          ⁅J, K₂⁆ ≤ pCoreOf 2 J → pCoreOf 2 J ≤ mcOf T →
                            (∃ k ∈ K₁ ⊔ K₂, orderOf k = 5 ∧ k ∉ innerSub J) → False

@[expose] def Input14615ContraInnerN : Prop :=
  ∀ (G : Type) [Group G] [Finite G], ASC27Statement G →
    ∀ (T M : Subgroup G), Setting146 G T M →
      ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p →
        ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDecP T M H p H₀ H₁ H₂ t → Ctx15 T M H p H₁ →
          ∀ (K₁ K₂ : Subgroup G) (s : G), Setup14615 T M H H₁ H₂ K₁ K₂ s →
            ¬ g2_14615 K₂ ≤ mcOf T → Gap3Fix T K₁ K₂ →
              HypC23 (g2_14615 K₂) (pCoreOf 2 (mcOf T)) (g12_14615 T K₂) →
                CharTwo (g2_14615 K₂) → pCoreOf 2 (g2_14615 K₂) ≤ g12_14615 T K₂ →
                  ∀ J : Subgroup G, J ∈ cComp (g2_14615 K₂) →
                    CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J) → ¬ J ≤ g12_14615 T K₂ →
                      ⁅J, K₁⁆ = J → pRank 5 J ≤ 1 →
                        K₁ ≤ Subgroup.normalizer (J : Set G) → K₂ ≤ Subgroup.normalizer (J : Set G) →
                          ⁅J, K₂⁆ ≤ pCoreOf 2 J → pCoreOf 2 J ≤ mcOf T →
                            K₁ ⊔ K₂ ≤ innerSub J → g2_14615 K₂ ≤ Subgroup.normalizer (J : Set G) →
                              (∃ a ∈ J, orderOf a = 5) →
                                (K₁ = oTwoUpper H₁ → K₂ = oTwoUpper H₂ → K₁ ≤ J) →
                                  (K₁ ≤ J → quasithinOmegaOneCenter T ≤ J ⊓ g12_14615 T K₂) → False

theorem input14615ContraFix_of_N (h5 : Stage1461Five) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (iO : Input14615ContraOuterN) (iI : Input14615ContraInnerN) :
    Input14615ContraOuterFix ∧ Input14615ContraInnerFix := by
  have core : ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
      ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p →
        ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDecP T M H p H₀ H₁ H₂ t → Ctx15 T M H p H₁ →
          ∀ (K₁ K₂ : Subgroup G) (s : G), Setup14615 T M H H₁ H₂ K₁ K₂ s →
            ¬ g2_14615 K₂ ≤ mcOf T → Gap3Fix T K₁ K₂ →
              HypC23 (g2_14615 K₂) (pCoreOf 2 (mcOf T)) (g12_14615 T K₂) →
                CharTwo (g2_14615 K₂) → pCoreOf 2 (g2_14615 K₂) ≤ g12_14615 T K₂ →
                  ∀ J : Subgroup G, J ∈ cComp (g2_14615 K₂) →
                    CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J) → ¬ J ≤ g12_14615 T K₂ →
                      ⁅J, K₁⁆ = J → pRank 5 J ≤ 1 → False := by
    intro G _ _ T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx K₁ K₂ s hset hG₂ hfix hHyp hchar hPcore
      J hJc hJq hJle hJK hJ5
    obtain ⟨hK₁N, hK₂N, hK₂c, hWG, k₂, hk₂K, hk₂5⟩ :=
      jFacts h5 h38 S hred hmax hdec hctx hset hG₂ hJc hJq hJle
    have hp5 : p = 5 := hctx.1
    have hgen : K₁ ⊔ K₂ ≤ Subgroup.closure {x | x ∈ K₁ ⊔ K₂ ∧ orderOf x = 5} := by
      have := kz_le_closure_five_14615 S hdec hp5 hset
      rwa [hset.kz] at this
    have hKzN : K₁ ⊔ K₂ ≤ Subgroup.normalizer (J : Set G) := sup_le hK₁N hK₂N
    by_cases hin : K₁ ⊔ K₂ ≤ innerSub J
    · have hnc : ¬ ⁅J, K₁ ⊔ K₂⁆ ≤ pCoreOf 2 J := by
        intro h
        have h1 : ⁅J, K₁⁆ ≤ pCoreOf 2 J := (Subgroup.commutator_mono le_rfl le_sup_left).trans h
        rw [hJK] at h1
        exact not_le_pCoreOf_of_quasisimple hJq h1
      obtain ⟨a, haJ, ha5⟩ := exists_five_of_le_innerSub hgen hin hnc
      have hK₂G₁ : K₂ ≤ mcOf T := hset.le_mcOf S hred
      have hK₂X : K₂ ≤ g2_14615 K₂ := Subgroup.le_normalizer
      have hJK₂ : ¬ J ≤ K₂ := fun h => hJle (h.trans (le_inf hK₂G₁ hK₂X))
      have hJn : g2_14615 K₂ ≤ Subgroup.normalizer (J : Set G) :=
        normal_of_five_dvd h36 hHyp.sqtk hJc hJq hK₂X le_rfl hJK₂ hk₂K hk₂5 haJ ha5
      have hmix : K₁ = oTwoUpper H₁ → K₂ = oTwoUpper H₂ → K₁ ≤ J := by
        intro hK₁e hK₂e
        subst hK₁e hK₂e
        have hCz : conjClosure (oTwoUpper H) (mcOf T) = oTwoUpper H := by
          rw [hset.kz]
          exact (hdec.oTwoUpper_eq S hred).symm
        have hKJ : oTwoUpper H ≤ Subgroup.normalizer (J : Set G) := by
          rw [hdec.oTwoUpper_eq S hred]
          exact hKzN
        exact oTwoUpper_le_of_innerSub h36 S hp5 hred hdec hCz hHyp.sqtk hJc hJq hK₂N hK₂c hKJ hJn
          hin (fun h => by rw [hJK] at h; exact not_le_pCoreOf_of_quasisimple hJq h)
      refine iI G (hC27 G) T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx K₁ K₂ s hset hG₂ hfix hHyp
        hchar hPcore J hJc hJq hJle hJK hJ5 hK₁N hK₂N hK₂c hWG hin hJn ⟨a, haJ, ha5⟩ hmix ?_
      intro hK₁J
      exact Z_le_B_P19 S h5 hred hdec hset (SBc14.pCoreOf_mcOf_le_g2 S hred hdec hset)
        (le_of_mem_cComp hJc)
        (fun g hg x hx => (Subgroup.mem_normalizer_iff.mp (hJn hg) x).mp hx) hK₁J
    · obtain ⟨k, hkK, hk5, hkn⟩ := exists_five_not_mem_innerSub hgen hin
      exact iO G (hC27 G) T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx K₁ K₂ s hset hG₂ hfix hHyp
        hchar hPcore J hJc hJq hJle hJK hJ5 hK₁N hK₂N hK₂c hWG ⟨k, hkK, hk5, hkn⟩
  exact ⟨fun G _ _ T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx K₁ K₂ s hset hG₂ hfix hHyp hchar
      hPcore J hJc hJq hJle hJK hJ5 _ =>
        core G T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx K₁ K₂ s hset hG₂ hfix hHyp hchar hPcore
          J hJc hJq hJle hJK hJ5,
    fun G _ _ T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx K₁ K₂ s hset hG₂ hfix hHyp hchar
      hPcore J hJc hJq hJle hJK hJ5 _ =>
        core G T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx K₁ K₂ s hset hG₂ hfix hHyp hchar hPcore
          J hJc hJq hJle hJK hJ5⟩

end SBc17

theorem stages14613_to_14617_of_SBc17N_noUK_solDec
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (h2 : Stage1461Two) (h5 : Stage1461Five) (h12 : Stage14612PartP) (h4 : Stage1463Four)
    (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (iA : Input14613AP) (iB1 : Input14613B1P) (iB2 : Input14613B2P)
    (i14b : Input14614SolDec) (i14c : Input14614Shape)
    (iSF : Input14615SetupFourP) (iFix : SBc17.Input14615FixR)
    (iON : SBc17.Input14615ContraOuterN) (iIN : SBc17.Input14615ContraInnerN)
    (iWeak : Input14616Weak) (iF : Input14617FstarK) :
    Stage14613LabP ∧ Stage14614 ∧ Stage14615 ∧ Stage14616 ∧ Stage14617 :=
  stages14613_to_14617_of_SBc17_noUK_solDec h2 h5 h12 h4 h36 h38 iA iB1 iB2 i14b i14c iSF iFix
    (SBc17.input14615ContraFix_of_N h5 h36 h38 hC27 iON iIN).1
    (SBc17.input14615ContraFix_of_N h5 h36 h38 hC27 iON iIN).2 iWeak iF

end CFSG.Quasithin
