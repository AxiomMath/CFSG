module

public import CFSG.Quasithin.EmptyFaithful.SBc17Inn2
public import CFSG.Quasithin.EmptyFaithful.SBc17Ent3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped Pointwise commutatorElement

namespace SBc17

variable {G : Type} [Group G] [Finite G]

@[expose] def C27AltBig (_H R M K V : Subgroup G) : Prop :=
  (∃ (n : ℕ) (α : ↥K →* alternatingGroup (Fin n)), 7 ≤ n ∧ n ≤ 8 ∧ IsShort2 K ∧
      IsAltBlockTypeWith K n α ∧
      ∃ t : G, t ∈ R ∧ ∃ htV : t ∈ Subgroup.normalizer (V : Set G),
        autOn R V = Subgroup.zpowers (conjAct V ⟨t, htV⟩) ∧
        orderOf (conjAct V ⟨t, htV⟩) = 2 ∧
        ∃ σ : Equiv.Perm (Fin n), σ.IsSwap ∧
          ∀ (k : G) (hk : k ∈ K) (hk' : t * k * t⁻¹ ∈ K),
            ((α ⟨t * k * t⁻¹, hk'⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) =
              σ * (α ⟨k, hk⟩ : Equiv.Perm (Fin n)) * σ⁻¹) ∧
    autOn (M ⊓ K) V = autOn K V ⊓ Subgroup.centralizer (autOn R V : Set (MulAut ↥V))

@[expose] def C27InnerRem (H R M K V : Subgroup G) : Prop :=
  C27AltBig H R M K V ∨ C27SL3 H R M K V ∨ C27L45 H R M K V

theorem false_of_inner_cases (hC27 : ASC27Statement G) {H R M J : Subgroup G} (hyp : HypC23 H R M)
    (hJc : J ∈ cComp H) (hq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J)) (hH : CharTwo H)
    (hJM : ¬ J ≤ M) (hR : R ≤ Subgroup.normalizer (J : Set G)) {a : G} (haM : a ∈ M ⊓ J)
    (ha5 : orderOf a = 5) (hrank : pRank 5 J ≤ 1) (hL : ¬ IsL2BorelBlock J (J ⊓ M)) :
    C27InnerRem H R M J (omegaOneCenterOf (pCoreOf 2 (J ⊔ R))) := by
  set V := omegaOneCenterOf (pCoreOf 2 (J ⊔ R)) with hV
  have hcJ : CharTwo J := charTwo_of_mem_cComp hH hJc
  have h1 := (hC27 H R M J V hyp hJc hq hcJ hJM hR rfl).1
  have hJV : J ≤ Subgroup.normalizer (V : Set G) := le_normalizer_V J R
  have hD : J ⊓ Subgroup.centralizer (V : Set G) ≤ oTwoZIn J := inf_centralizer_le_oTwoZIn h1.2.1
  have hOC : pCoreOf 2 J ≤ Subgroup.centralizer (V : Set G) := fun x hx =>
    (h1.1 (pCoreOf_le_pCoreOf_sup hR hx)).2
  rcases asc27_cases hC27 hyp hJc hq hcJ hJM hR rfl with
    h | h | h | h | h | h | h | h | h | h | h
  · exact absurd (isL2BorelBlock_of_C27L2 hR hq h1.1 h1.2.1 h) hL
  · exfalso
    obtain ⟨-, ⟨α, hα, hker, -⟩, -, -, hB⟩ := h
    exact false_of_a5 hJV hOC hD hα hker hB haM ha5
  · exfalso
    obtain ⟨-, ⟨α, hα, hker, -⟩, -, e, P, hP, hmap⟩ := h
    exact false_of_a7_43 hJV (hD.trans (oTwoZIn_le_pCoreOf_of_center_bot hα hker
      (center_alt_bot (by norm_num)))) ⟨e, P, hP, hmap⟩ haM ha5
  · exfalso
    obtain ⟨-, ⟨α, hα, hker, -⟩, -, e, P, hP, hmap⟩ := h
    exact false_of_a7_2221 hJV (hD.trans (oTwoZIn_le_pCoreOf_of_center_bot hα hker
      (center_alt_bot (by norm_num)))) ⟨e, P, hP, hmap⟩ haM ha5
  · obtain ⟨⟨n, α, hn5, hn8, hshort, hαdata, t, htR, htV, hRt, hord, σ, hσ, hrel⟩, hMK⟩ := h
    by_cases hn : n ≤ 6
    · exfalso
      exact false_of_alt_small hR hJV (hD.trans (oTwoZIn_le_pCoreOf_of_center_bot hαdata.1
        hαdata.2.1 (center_alt_bot (by omega)))) hn hαdata.2.1 htR htV hσ hrel hMK haM ha5
    · exact Or.inl ⟨⟨n, α, by omega, hn8, hshort, hαdata, t, htR, htV, hRt, hord, σ, hσ, hrel⟩, hMK⟩
  · exact (false_of_hat6 ⟨h.1, h.2.1⟩ haM ha5).elim
  · exact (false_of_excA7 h haM ha5).elim
  · rcases h.1 with hA | hS
    · exfalso
      obtain ⟨-, α, hα, hker, -⟩ := hA
      exact false_of_a6 hJV hOC hD hα hker h.2 haM ha5
    · exact (false_of_sp4_block hS hrank).elim
  · exact (false_of_g2 h.1 haM.2 ha5).elim
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)


@[expose] def Input14615ContraInnerD : Prop :=
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
                                      C27InnerRem (g2_14615 K₂) (pCoreOf 2 (mcOf T))
                                        (g12_14615 T K₂) J
                                        (omegaOneCenterOf (pCoreOf 2 (J ⊔ pCoreOf 2 (mcOf T)))) →
                                        False

theorem input14615ContraInnerB_of_D (iID : Input14615ContraInnerD) : Input14615ContraInnerB := by
  intro G _ _ hC27 T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx K₁ K₂ s hset hG₂ hfix hHyp hchar
    hPcore J hJc hJq hJle hJK hJ5 hK₁N hK₂N hK₂c hWG hin hJn ha hK₁J hZB hL
  refine iID G hC27 T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx K₁ K₂ s hset hG₂ hfix hHyp hchar
    hPcore J hJc hJq hJle hJK hJ5 hK₁N hK₂N hK₂c hWG hin hJn ha hK₁J hZB hL ?_
  obtain ⟨a, haO, ha5⟩ := hdec.exists_order_p_P14 hred.prime hred.odd
  have haK₁ : a ∈ K₁ := hset.oTwo₁ haO
  have ha5' : orderOf a = 5 := by rw [ha5, hctx.1]
  have haM : a ∈ g12_14615 T K₂ ⊓ J :=
    ⟨⟨sup_le_mcOf_14615 S hred hset (Subgroup.mem_sup_left haK₁),
      le_of_mem_cComp hJc (hK₁J haK₁)⟩, hK₁J haK₁⟩
  have hR : pCoreOf 2 (mcOf T) ≤ Subgroup.normalizer (J : Set G) := hHyp.radical.1.trans hJn
  exact false_of_inner_cases hC27 hHyp hJc hJq hchar hJle hR haM ha5' hJ5 hL

end SBc17

theorem stages14613_to_14617_of_SBc17E_cert_noUK_solDec
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (h2 : Stage1461Two) (h5 : Stage1461Five) (h12 : Stage14612PartP) (h4 : Stage1463Four)
    (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (iA : Input14613AP) (iB1 : Input14613B1P) (iB2 : Input14613B2P)
    (i14b : Input14614SolDec) (i14c : Input14614Shape)
    (iSF : Input14615SetupFourP) (iFix : SBc17.Input14615FixR)
    (iOD : SBc17.Input14615ContraOuterD) (iID : SBc17.Input14615ContraInnerD)
    (iWeak : Input14616Weak) (iF : Input14617FstarK) :
    Stage14613LabP ∧ Stage14614 ∧ Stage14615 ∧ Stage14616 ∧ Stage14617 :=
  stages14613_to_14617_of_SBc17D_cert_noUK_solDec hC27 h2 h5 h12 h4 h36 h38 iA iB1 iB2 i14b i14c iSF
    iFix iOD (SBc17.input14615ContraInnerB_of_D iID) iWeak iF

end CFSG.Quasithin
