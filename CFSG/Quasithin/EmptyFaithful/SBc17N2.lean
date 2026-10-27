module

public import CFSG.Quasithin.EmptyFaithful.SBc17Glue
public import CFSG.Quasithin.EmptyFaithful.SBc17MixOne
public import CFSG.Quasithin.EmptyFaithful.SBc17N

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

namespace SBc17

@[expose] def IsL2BorelBlock {G : Type} [Group G] (J B : Subgroup G) : Prop :=
  IsShort2 J ∧ (∃ n : ℕ, 1 < n ∧ IsLin2Type J n) ∧ IsBorelOfBlock J B

@[expose] def Input14615ContraOuterB : Prop :=
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
                            (∃ k ∈ K₁ ⊔ K₂, orderOf k = 5 ∧ k ∉ innerSub J) →
                              ¬ (K₁ = oTwoUpper H₁ ∧ K₂ = oTwoUpper H₂ ∧
                                IsL2BorelBlock J (J ⊓ g12_14615 T K₂)) → False

@[expose] def Input14615ContraInnerB : Prop :=
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
                              (∃ a ∈ J, orderOf a = 5) → K₁ ≤ J →
                                quasithinOmegaOneCenter T ≤ J ⊓ g12_14615 T K₂ →
                                  ¬ IsL2BorelBlock J (J ⊓ g12_14615 T K₂) → False

theorem input14615ContraN_of_B (h36 : A36ForSQTK) (iOB : Input14615ContraOuterB)
    (iIB : Input14615ContraInnerB) : Input14615ContraOuterN ∧ Input14615ContraInnerN := by
  refine ⟨?_, ?_⟩
  · intro G _ _ hC27 T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx K₁ K₂ s hset hG₂ hfix hHyp hchar
      hPcore J hJc hJq hJle hJK hJ5 hK₁N hK₂N hK₂c hWG hout
    by_cases hcase : K₁ = oTwoUpper H₁ ∧ K₂ = oTwoUpper H₂ ∧
        IsL2BorelBlock J (J ⊓ g12_14615 T K₂)
    · obtain ⟨hK₁e, hK₂e, hshort, ⟨n, hn, hlin⟩, hB⟩ := hcase
      subst hK₁e hK₂e
      have hp5 : p = 5 := hctx.1
      have hCz : conjClosure (oTwoUpper H) (mcOf T) = oTwoUpper H := by
        rw [hset.kz]
        exact (hdec.oTwoUpper_eq S hred).symm
      have hKJ : oTwoUpper H ≤ Subgroup.normalizer (J : Set G) := by
        rw [hdec.oTwoUpper_eq S hred]
        exact sup_le hK₁N hK₂N
      exact false_of_outer_l2_block h36 S hp5 hred hdec hCz hHyp.sqtk hJc hJq hK₂N hK₂c hKJ hn
        hlin hB hout
    · exact iOB G hC27 T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx K₁ K₂ s hset hG₂ hfix hHyp hchar
        hPcore J hJc hJq hJle hJK hJ5 hK₁N hK₂N hK₂c hWG hout hcase
  · intro G _ _ hC27 T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx K₁ K₂ s hset hG₂ hfix hHyp hchar
      hPcore J hJc hJq hJle hJK hJ5 hK₁N hK₂N hK₂c hWG hin hJn ha hmix hZ
    have hK₁J : K₁ ≤ J := by
      rcases hset.shape with ⟨hc₁, hc₂, -, hφ⟩ | ⟨hK₁e, hK₂e⟩
      · exact le_of_innerSub_shapeOne h36 S hctx.1 hred hdec hset hc₁ hc₂ hφ hHyp.sqtk hJc hJq hK₂N
          hK₂c (sup_le hK₁N hK₂N) hJn hin
          (fun h => by rw [hJK] at h; exact not_le_pCoreOf_of_quasisimple hJq h)
      · exact hmix hK₁e hK₂e
    have hZB := hZ hK₁J
    by_cases hL : IsL2BorelBlock J (J ⊓ g12_14615 T K₂)
    · obtain ⟨hshort, ⟨n, hn, hlin⟩, hB⟩ := hL
      exact false_of_inner_l2_block S hn hshort hlin hB hZB (le_of_mem_cComp hJc) hJle
    · exact iIB G hC27 T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx K₁ K₂ s hset hG₂ hfix hHyp hchar
        hPcore J hJc hJq hJle hJK hJ5 hK₁N hK₂N hK₂c hWG hin hJn ha hK₁J hZB hL

end SBc17

theorem stages14613_to_14617_of_SBc17B_noUK_solDec
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (h2 : Stage1461Two) (h5 : Stage1461Five) (h12 : Stage14612PartP) (h4 : Stage1463Four)
    (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (iA : Input14613AP) (iB1 : Input14613B1P) (iB2 : Input14613B2P)
    (i14b : Input14614SolDec) (i14c : Input14614Shape)
    (iSF : Input14615SetupFourP) (iFix : SBc17.Input14615FixR)
    (iOB : SBc17.Input14615ContraOuterB) (iIB : SBc17.Input14615ContraInnerB)
    (iWeak : Input14616Weak) (iF : Input14617FstarK) :
    Stage14613LabP ∧ Stage14614 ∧ Stage14615 ∧ Stage14616 ∧ Stage14617 :=
  stages14613_to_14617_of_SBc17N_noUK_solDec hC27 h2 h5 h12 h4 h36 h38 iA iB1 iB2 i14b i14c iSF iFix
    (SBc17.input14615ContraN_of_B h36 iOB iIB).1 (SBc17.input14615ContraN_of_B h36 iOB iIB).2 iWeak
    iF

end CFSG.Quasithin
