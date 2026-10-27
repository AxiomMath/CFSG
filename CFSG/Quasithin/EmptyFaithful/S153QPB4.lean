module

public import CFSG.Quasithin.EmptyFaithful.SBc17Ent2
public import CFSG.Quasithin.EmptyFaithful.S153QPB3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

namespace SBc17

variable {G : Type} [Group G]

variable [Finite G]

theorem mem_innerSub_of_c27SL3 (hC27 : ASC27Statement G) {H R M J Kz : Subgroup G} {k : G}
    (hyp : HypC23 H R M) (hJc : J ∈ cComp H) (hq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J))
    (hH : CharTwo H) (hJM : ¬ J ≤ M) (hR : R ≤ Subgroup.normalizer (J : Set G))
    (hk : k ∈ Subgroup.normalizer (J : Set G)) (hkR : k ∈ Subgroup.normalizer (R : Set G))
    (hk5 : k ^ 5 = 1) (hkK : k ∈ Kz) (hW : IsPGroup 2 ↥(Kz ⊓ J))
    (hKG : M ≤ Subgroup.normalizer (Kz : Set G))
    (hg : C27SL3 H R M J (omegaOneCenterOf (pCoreOf 2 (J ⊔ R)))) : k ∈ innerSub J := by
  set V := omegaOneCenterOf (pCoreOf 2 (J ⊔ R)) with hV
  have hcJ : CharTwo J := charTwo_of_mem_cComp hH hJc
  have h1 := (hC27 H R M J V hyp hJc hq hcJ hJM hR rfl).1
  have hkV : k ∈ Subgroup.normalizer (V : Set G) := mem_normalizer_V hk hkR
  have hJV : J ≤ Subgroup.normalizer (V : Set G) := le_normalizer_V J R
  have hD : J ⊓ Subgroup.centralizer (V : Set G) ≤ oTwoZIn J := inf_centralizer_le_oTwoZIn h1.2.1
  obtain ⟨⟨n, F, _, _, -, hcard, ⟨e⟩⟩, hmax, -⟩ := hg
  have : CharP F 2 := charP_two_of_card_eq_pow hcard
  have : Finite F := Finite.of_fintype F
  have e' : ↥(autOn J V) ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
    e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm
  refine mem_innerSub_of_autOn_sl3 (B := M ⊓ J) (W := Kz ⊓ J) hJV hq hD hk hkV hk5 e' hmax hW ?_ ?_
  · intro b hb w hw
    have hbN : b ∈ Subgroup.normalizer ((Kz ⊓ J : Subgroup G) : Set G) :=
      SBc14.mem_normalizer_inf (hKG hb.1) (Subgroup.le_normalizer hb.2)
    exact (Subgroup.mem_normalizer_iff.mp hbN w).mp hw
  · intro b hb
    have hbN : b ∈ Subgroup.normalizer (Kz : Set G) := hKG hb.1
    refine ⟨?_, ?_⟩
    · have h1 : b * k * b⁻¹ ∈ Kz := (Subgroup.mem_normalizer_iff.mp hbN k).mp hkK
      exact Kz.mul_mem h1 (Kz.inv_mem hkK)
    · have h2 : k * b⁻¹ * k⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp hk b⁻¹).mp (J.inv_mem hb.2)
      have e : ⁅b, k⁆ = b * (k * b⁻¹ * k⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact J.mul_mem hb.2 h2

@[expose] def Input14615ContraOuterE : Prop :=
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
                        K₁ ≤ Subgroup.normalizer (J : Set G) →
                          K₂ ≤ Subgroup.normalizer (J : Set G) →
                            ⁅J, K₂⁆ ≤ pCoreOf 2 J → pCoreOf 2 J ≤ mcOf T →
                              (∃ k ∈ K₁ ⊔ K₂, orderOf k = 5 ∧ k ∉ innerSub J) →
                                ¬ IsL2BorelBlock J (J ⊓ g12_14615 T K₂) →
                                  ¬ pCoreOf 2 (mcOf T) ≤ Subgroup.normalizer (J : Set G) → False

theorem input14615ContraOuterD_of_E (h36 : A36ForSQTK) (iOE : Input14615ContraOuterE) :
    Input14615ContraOuterD := by
  intro G _ _ hC27 T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx K₁ K₂ s hset hG₂ hfix hHyp hchar
    hPcore J hJc hJq hJle hJK hJ5 hK₁N hK₂N hK₂c hWG hout hL hcase
  by_cases hR : pCoreOf 2 (mcOf T) ≤ Subgroup.normalizer (J : Set G)
  · exfalso
    rcases hcase with hnR | hg
    · exact hnR hR
    · obtain ⟨k, hkK, hk5, hkn⟩ := hout
      have hkJ : k ∈ Subgroup.normalizer (J : Set G) := sup_le hK₁N hK₂N hkK
      have hkG : k ∈ mcOf T := sup_le_mcOf_14615 S hred hset hkK
      have hkR : k ∈ Subgroup.normalizer (pCoreOf 2 (mcOf T) : Set G) :=
        le_normalizer_pCoreOf 2 (mcOf T) hkG
      have hk5' : k ^ 5 = 1 := by rw [← hk5]; exact pow_orderOf_eq_one k
      rcases hset.shape with ⟨hc₁, hc₂, -, hφ⟩ | ⟨hK₁e, hK₂e⟩
      · have hKG : mcOf T ≤ Subgroup.normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) :=
          SBc14.mcOf_le_normalizer_kz hset
        have hW := isPGroup_inf_of_not_innerSub_shapeOne h36 S hctx.1 hred hdec hset hc₁ hc₂ hφ
          hHyp.sqtk hJc hJq hK₂N hK₂c (sup_le hK₁N hK₂N) (fun h => hkn (h hkK))
        exact hkn (mem_innerSub_of_c27SL3 hC27 hHyp hJc hJq hchar hJle hR hkJ hkR hk5' hkK hW
          (inf_le_left.trans hKG) hg)
      · subst hK₁e hK₂e
        have hCz : conjClosure (oTwoUpper H) (mcOf T) = oTwoUpper H := by
          rw [hset.kz]
          exact (hdec.oTwoUpper_eq S hred).symm
        have hKX : oTwoUpper H = oTwoUpper H₁ ⊔ oTwoUpper H₂ := hdec.oTwoUpper_eq S hred
        have hKJ : oTwoUpper H ≤ Subgroup.normalizer (J : Set G) := by
          rw [hKX]
          exact sup_le hK₁N hK₂N
        have hW := isPGroup_oTwoUpper_inf_of_not_innerSub h36 S hctx.1 hred hdec hCz hHyp.sqtk hJc
          hJq hK₂N hK₂c hKJ (fun h => hkn (h hkK))
        have hKG := mcOf_le_normalizer_oTwoUpper hCz
        exact hkn (mem_innerSub_of_c27SL3 hC27 hHyp hJc hJq hchar hJle hR hkJ hkR hk5' (hKX ▸ hkK) hW
          (inf_le_left.trans hKG) hg)
  · exact iOE G hC27 T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx K₁ K₂ s hset hG₂ hfix hHyp hchar
      hPcore J hJc hJq hJle hJK hJ5 hK₁N hK₂N hK₂c hWG hout hL hR

end SBc17

end CFSG.Quasithin
