module

public import CFSG.Quasithin.EmptyFaithful.SBc17Inn3
public import CFSG.Quasithin.EmptyFaithful.SBc17InnB
public import CFSG.Quasithin.EmptyFaithful.SBc17K1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped Pointwise commutatorElement

namespace SBc17

variable {G : Type} [Group G] [Finite G]

theorem inner_facts (hC27 : ASC27Statement G) {H R M J : Subgroup G} (hyp : HypC23 H R M)
    (hJc : J ∈ cComp H) (hq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J)) (hH : CharTwo H)
    (hJM : ¬ J ≤ M) (hR : R ≤ Subgroup.normalizer (J : Set G)) :
    J ≤ Subgroup.normalizer (omegaOneCenterOf (pCoreOf 2 (J ⊔ R)) : Set G) ∧
      J ⊓ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 (J ⊔ R)) : Set G) ≤ oTwoZIn J ∧
        pCoreOf 2 J ≤ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 (J ⊔ R)) : Set G) := by
  have hcJ : CharTwo J := charTwo_of_mem_cComp hH hJc
  have h1 := (hC27 H R M J (omegaOneCenterOf (pCoreOf 2 (J ⊔ R))) hyp hJc hq hcJ hJM hR rfl).1
  exact ⟨le_normalizer_V J R, inf_centralizer_le_oTwoZIn h1.2.1, fun x hx =>
    (h1.1 (pCoreOf_le_pCoreOf_sup hR hx)).2⟩

theorem false_of_c27AltBig (hC27 : ASC27Statement G) {H R M J K₁ : Subgroup G}
    (hyp : HypC23 H R M) (hJc : J ∈ cComp H)
    (hq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J)) (hH : CharTwo H) (hJM : ¬ J ≤ M)
    (hR : R ≤ Subgroup.normalizer (J : Set G)) (hK₁ : K₁ ≤ M ⊓ J)
    (hK₁N : M ⊓ J ≤ Subgroup.normalizer (K₁ : Set G))
    (hK₁d : IsPGroup 2 ↥⁅K₁, K₁⁆ ∨ 17 ∣ Nat.card ↥K₁) {a : G} (haK : a ∈ K₁)
    (ha5 : orderOf a = 5)
    (h : C27AltBig H R M J (omegaOneCenterOf (pCoreOf 2 (J ⊔ R)))) : False := by
  obtain ⟨hJV, hD, hOC⟩ := inner_facts hC27 hyp hJc hq hH hJM hR
  obtain ⟨⟨n, α, hn7, hn8, -, hαdata, t, htR, htV, hRt, -, σ, hσ, hrel⟩, hMK⟩ := h
  exact false_of_alt_big hR hJV (hD.trans (oTwoZIn_le_pCoreOf_of_center_bot hαdata.1 hαdata.2.1
    (center_alt_bot (by omega)))) hOC hn7 hn8 hαdata.1 hαdata.2.1 htR htV hRt hσ hrel hMK hK₁ hK₁N
    hK₁d haK ha5

@[expose] def C27InnerRemE (H R M K V : Subgroup G) : Prop :=
  C27SL3 H R M K V ∨ C27L45 H R M K V

@[expose] def Input14615ContraInnerE : Prop :=
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
                              K₁ ⊔ K₂ ≤ innerSub J → g2_14615 K₂ ≤ Subgroup.normalizer (J : Set G) →
                                (∃ a ∈ J, orderOf a = 5) → K₁ ≤ J →
                                  quasithinOmegaOneCenter T ≤ J ⊓ g12_14615 T K₂ →
                                    ¬ IsL2BorelBlock J (J ⊓ g12_14615 T K₂) →
                                      C27InnerRemE (g2_14615 K₂) (pCoreOf 2 (mcOf T))
                                        (g12_14615 T K₂) J
                                        (omegaOneCenterOf (pCoreOf 2 (J ⊔ pCoreOf 2 (mcOf T)))) →
                                        False

theorem input14615ContraInnerD_of_E (iIE : Input14615ContraInnerE) : Input14615ContraInnerD := by
  intro G _ _ hC27 T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx K₁ K₂ s hset hG₂ hfix hHyp hchar
    hPcore J hJc hJq hJle hJK hJ5 hK₁N hK₂N hK₂c hWG hin hJn ha hK₁J hZB hL hrem
  rcases hrem with hAlt | hrem'
  · exfalso
    obtain ⟨a, haO, ha5⟩ := hdec.exists_order_p_P14 hred.prime hred.odd
    have haK₁ : a ∈ K₁ := hset.oTwo₁ haO
    have ha5' : orderOf a = 5 := by rw [ha5, hctx.1]
    have hK₁M : K₁ ≤ g12_14615 T K₂ ⊓ J := fun x hx =>
      ⟨⟨sup_le_mcOf_14615 S hred hset (Subgroup.mem_sup_left hx),
        le_of_mem_cComp hJc (hK₁J hx)⟩, hK₁J hx⟩
    have hK₁Nm : g12_14615 T K₂ ⊓ J ≤ Subgroup.normalizer (K₁ : Set G) := fun x hx =>
      hfix x hx.1.1 hx.1.2
    have hR : pCoreOf 2 (mcOf T) ≤ Subgroup.normalizer (J : Set G) := hHyp.radical.1.trans hJn
    exact false_of_c27AltBig hC27 hHyp hJc hJq hchar hJle hR hK₁M hK₁Nm
      (kOne_dichotomy hctx.1 hdec hset) haK₁ ha5' hAlt
  · exact iIE G hC27 T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx K₁ K₂ s hset hG₂ hfix hHyp hchar
      hPcore J hJc hJq hJle hJK hJ5 hK₁N hK₂N hK₂c hWG hin hJn ha hK₁J hZB hL hrem'

end SBc17

theorem stages14613_to_14617_of_SBc17F_cert_noUK_solDec
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (h2 : Stage1461Two) (h5 : Stage1461Five) (h12 : Stage14612PartP) (h4 : Stage1463Four)
    (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (iA : Input14613AP) (iB1 : Input14613B1P) (iB2 : Input14613B2P)
    (i14b : Input14614SolDec) (i14c : Input14614Shape)
    (iSF : Input14615SetupFourP) (iFix : SBc17.Input14615FixR)
    (iOD : SBc17.Input14615ContraOuterD) (iIE : SBc17.Input14615ContraInnerE)
    (iWeak : Input14616Weak) (iF : Input14617FstarK) :
    Stage14613LabP ∧ Stage14614 ∧ Stage14615 ∧ Stage14616 ∧ Stage14617 :=
  stages14613_to_14617_of_SBc17E_cert_noUK_solDec hC27 h2 h5 h12 h4 h36 h38 iA iB1 iB2 i14b i14c iSF
    iFix iOD (SBc17.input14615ContraInnerD_of_E iIE) iWeak iF

end CFSG.Quasithin
