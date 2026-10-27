module

public import CFSG.Quasithin.EmptyFaithful.S146zVA
public import CFSG.Quasithin.EmptyFaithful.S146zVC
public import CFSG.Quasithin.EmptyFaithful.S153QPB4

public section

namespace CFSG.Quasithin.S146zW

open CFSG.Open hiding StatedSL
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.C2Push CFSG.Quasithin.S146zV CFSG.Quasithin.SBc17
open scoped commutatorElement

@[expose] def Input14615OuterSylowOut : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDecP T M H p H₀ H₁ H₂ t → Ctx15 T M H p H₁ →
        ∀ (K₁ K₂ : Subgroup G) (s : G), Setup14615 T M H H₁ H₂ K₁ K₂ s →
          ¬ g2_14615 K₂ ≤ mcOf T → Gap3Fix T K₁ K₂ →
            HypC23 (g2_14615 K₂) (pCoreOf 2 (mcOf T)) (g12_14615 T K₂) →
              CharTwo (g2_14615 K₂) → pCoreOf 2 (g2_14615 K₂) ≤ g12_14615 T K₂ →
                ∀ J : Subgroup G, J ∈ cComp (g2_14615 K₂) →
                  CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J) → ¬ J ≤ g12_14615 T K₂ →
                    ⁅J, K₁⁆ = J → pRank 5 J ≤ 1 →
                      K₁ ≤ Subgroup.normalizer (J : Set G) →
                        K₂ ≤ Subgroup.normalizer (J : Set G) →
                          ⁅J, K₂⁆ ≤ pCoreOf 2 J → pCoreOf 2 J ≤ mcOf T →
                            (∃ k ∈ K₁ ⊔ K₂, orderOf k = 5 ∧ k ∉ innerSub J) →
                              ¬ pCoreOf 2 (mcOf T) ≤ Subgroup.normalizer (J : Set G) →
                                (∀ T' : Subgroup G, IsSylowTwoOf T' (g2_14615 K₂) →
                                  ¬ T' ≤ Subgroup.normalizer (pCoreOf 2 (mcOf T) : Set G)) →
                                  IsSylowTwoOf (pCoreOf 2 (mcOf T) ⊓ J) J

theorem input14615ContraOuterE_of_sylowOut
    (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G)
    (iSyl : Input14615OuterSylowOut) : Input14615ContraOuterE := by
  intro G _ _ _ T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx K₁ K₂ s hset hG₂ hfix hHyp hchar
    hPcore J hJc hJq hJle hJK hJ5 hK₁N hK₂N hK₂c hWG hout hL hR
  have hsyl : IsSylowTwoOf (pCoreOf 2 (mcOf T) ⊓ J) J := by
    by_cases hex : ∃ T' : Subgroup G, IsSylowTwoOf T' (g2_14615 K₂) ∧
        T' ≤ Subgroup.normalizer (pCoreOf 2 (mcOf T) : Set G)
    · obtain ⟨T', hT', hT'R⟩ := hex
      exact C2Push.isSylowTwoOf_inf_of_not_le_normalizer hHyp.radical hT' hT'R hJc hJq hR
    · push Not at hex
      exact iSyl G T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx K₁ K₂ s hset hG₂ hfix hHyp hchar
        hPcore J hJc hJq hJle hJK hJ5 hK₁N hK₂N hK₂c hWG hout hR hex
  obtain ⟨hshort, htype, hBor⟩ := exists_block_data_of_asc129 (hC129 G) hchar hHyp.sqtk
    hHyp.radical hHyp.cgs hJc hJq hsyl hJle
  obtain ⟨k, hkK, hk5, hkn⟩ := hout
  rcases htype with ⟨n, hn, hlin⟩ | h5
  · exact hL ⟨hshort, ⟨n, hn, hlin⟩, hBor⟩
  · have hkJ : k ∈ Subgroup.normalizer (J : Set G) := sup_le hK₁N hK₂N hkK
    have hk5' : k ^ 5 = 1 := by
      rw [← hk5]
      exact pow_orderOf_eq_one k
    exact hkn (mem_innerSub_of_isAltType_five h5 hkJ hk5')

end CFSG.Quasithin.S146zW
