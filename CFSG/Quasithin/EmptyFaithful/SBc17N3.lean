module

public import CFSG.Quasithin.EmptyFaithful.SBc17N2
public import CFSG.Quasithin.EmptyFaithful.SBc17WOne

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

namespace SBc17

section OuterOne

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem false_of_outer_l2_block_shapeOne (h36 : A36ForSQTK) (S : Setting146 G T M) {PQ : Subgroup G}
    (hp5 : p = 5) (hred : IsRedCE T M H PQ p) (hdec : IsDecP T M H p H₀ H₁ H₂ t)
    {K₁ K₂ : Subgroup G} {s : G} (hset : Setup14615 T M H H₁ H₂ K₁ K₂ s)
    (hc₁ : K₁ ∈ cComp (mcOf T)) (hc₂ : K₂ ∈ cComp (mcOf T))
    (hφ : Nonempty (OTwoQuot K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)))
    {J : Subgroup G} (hX : SQTKGroup ↥(g2_14615 K₂)) (hJc : J ∈ cComp (g2_14615 K₂))
    (hJq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J))
    (hK₂N : K₂ ≤ Subgroup.normalizer (J : Set G)) (hK₂c : ⁅J, K₂⁆ ≤ pCoreOf 2 J)
    (hKJ : K₁ ⊔ K₂ ≤ Subgroup.normalizer (J : Set G)) {n : ℕ} (hn : 1 < n)
    (hlin : IsLin2Type J n) (hB : IsBorelOfBlock J (J ⊓ g12_14615 T K₂))
    (hout : ∃ k ∈ K₁ ⊔ K₂, orderOf k = 5 ∧ k ∉ innerSub J) : False := by
  obtain ⟨k, hkK, hk5, hkn⟩ := hout
  have hW := isPGroup_inf_of_not_innerSub_shapeOne h36 S hp5 hred hdec hset hc₁ hc₂ hφ hX hJc hJq
    hK₂N hK₂c hKJ (fun h => hkn (h hkK))
  have hKG : mcOf T ≤ Subgroup.normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) :=
    SBc14.mcOf_le_normalizer_kz hset
  have hkJ : k ∈ Subgroup.normalizer (J : Set G) := hKJ hkK
  refine hkn (mem_innerSub_of_commutator_two_proved hn hlin hB hkJ hW ?_ ?_)
  · intro b hb
    exact SBc14.mem_normalizer_inf (hKG hb.2.1) (Subgroup.le_normalizer hb.1)
  · intro b hb
    have hbN : b ∈ Subgroup.normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) := hKG hb.2.1
    refine ⟨?_, ?_⟩
    · have h1 : b * k * b⁻¹ ∈ K₁ ⊔ K₂ := (Subgroup.mem_normalizer_iff.mp hbN k).mp hkK
      exact (K₁ ⊔ K₂).mul_mem h1 ((K₁ ⊔ K₂).inv_mem hkK)
    · have h2 : k * b⁻¹ * k⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp hkJ b⁻¹).mp (J.inv_mem hb.1)
      have e : ⁅b, k⁆ = b * (k * b⁻¹ * k⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact J.mul_mem hb.1 h2

end OuterOne

@[expose] def Input14615ContraOuterC : Prop :=
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
                              ¬ IsL2BorelBlock J (J ⊓ g12_14615 T K₂) → False

theorem input14615ContraOuterB_of_C (h36 : A36ForSQTK) (iOC : Input14615ContraOuterC) :
    Input14615ContraOuterB := by
  intro G _ _ hC27 T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx K₁ K₂ s hset hG₂ hfix hHyp hchar
    hPcore J hJc hJq hJle hJK hJ5 hK₁N hK₂N hK₂c hWG hout hcase
  by_cases hL : IsL2BorelBlock J (J ⊓ g12_14615 T K₂)
  · exfalso
    obtain ⟨hshort, ⟨n, hn, hlin⟩, hB⟩ := hL
    rcases hset.shape with ⟨hc₁, hc₂, -, hφ⟩ | ⟨hK₁e, hK₂e⟩
    · exact false_of_outer_l2_block_shapeOne h36 S hctx.1 hred hdec hset hc₁ hc₂ hφ hHyp.sqtk hJc
        hJq hK₂N hK₂c (sup_le hK₁N hK₂N) hn hlin hB hout
    · exact hcase ⟨hK₁e, hK₂e, hshort, ⟨n, hn, hlin⟩, hB⟩
  · exact iOC G hC27 T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx K₁ K₂ s hset hG₂ hfix hHyp hchar
      hPcore J hJc hJq hJle hJK hJ5 hK₁N hK₂N hK₂c hWG hout hL

end SBc17

theorem stages14613_to_14617_of_SBc17C_noUK_solDec
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (h2 : Stage1461Two) (h5 : Stage1461Five) (h12 : Stage14612PartP) (h4 : Stage1463Four)
    (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (iA : Input14613AP) (iB1 : Input14613B1P) (iB2 : Input14613B2P)
    (i14b : Input14614SolDec) (i14c : Input14614Shape)
    (iSF : Input14615SetupFourP) (iFix : SBc17.Input14615FixR)
    (iOC : SBc17.Input14615ContraOuterC) (iIB : SBc17.Input14615ContraInnerB)
    (iWeak : Input14616Weak) (iF : Input14617FstarK) :
    Stage14613LabP ∧ Stage14614 ∧ Stage14615 ∧ Stage14616 ∧ Stage14617 :=
  stages14613_to_14617_of_SBc17B_noUK_solDec hC27 h2 h5 h12 h4 h36 h38 iA iB1 iB2 i14b i14c iSF iFix
    (SBc17.input14615ContraOuterB_of_C h36 iOC) iIB iWeak iF

end CFSG.Quasithin
