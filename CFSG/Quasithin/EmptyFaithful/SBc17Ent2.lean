module

public import CFSG.Quasithin.EmptyFaithful.SBc17Ent1
public import CFSG.Quasithin.EmptyFaithful.SBc17Sp4B
public import CFSG.Quasithin.EmptyFaithful.SBc17N3
public import CFSG.Quasithin.EmptyFaithful.SBc17Out5L

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

namespace SBc17

variable {G : Type} [Group G] [Finite G]

@[expose] def FactOut5U33 : Prop :=
  ∀ (X : Type) [Group X], IsPSU 3 3 1 X → Out5Inner X

omit [Finite G] in
theorem mem_innerSub_of_out5_quot {J : Subgroup G} (hS : Out5Inner (↥J ⧸ CFSG.pCore 2 ↥J)) {k : G}
    (hk : k ∈ Subgroup.normalizer (J : Set G)) (hk5 : k ^ 5 = 1) : k ∈ innerSub J :=
  mem_innerSub_of_out5 (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hS hk hk5

theorem false_of_outer_cases (hU33 : FactOut5U33) (hC27 : ASC27Statement G)
    {H R M J : Subgroup G} (hyp : HypC23 H R M) (hJc : J ∈ cComp H)
    (hq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J)) (hH : CharTwo H) (hJM : ¬ J ≤ M)
    (hR : R ≤ Subgroup.normalizer (J : Set G)) {k : G}
    (hk : k ∈ Subgroup.normalizer (J : Set G)) (hkR : k ∈ Subgroup.normalizer (R : Set G))
    (hk5 : k ^ 5 = 1) (hkn : k ∉ innerSub J) (hrank : pRank 5 J ≤ 1)
    (hL : ¬ IsL2BorelBlock J (J ⊓ M)) :
    C27SL3 H R M J (omegaOneCenterOf (pCoreOf 2 (J ⊔ R))) := by
  set V := omegaOneCenterOf (pCoreOf 2 (J ⊔ R)) with hV
  have hcJ : CharTwo J := charTwo_of_mem_cComp hH hJc
  have h1 := (hC27 H R M J V hyp hJc hq hcJ hJM hR rfl).1
  have hkV : k ∈ Subgroup.normalizer (V : Set G) := mem_normalizer_V hk hkR
  have hJV : J ≤ Subgroup.normalizer (V : Set G) := le_normalizer_V J R
  have hD : J ⊓ Subgroup.centralizer (V : Set G) ≤ oTwoZIn J := inf_centralizer_le_oTwoZIn h1.2.1
  rcases asc27_cases hC27 hyp hJc hq hcJ hJM hR rfl with
    h | h | h | h | h | h | h | h | h | h | h
  · exact absurd (isL2BorelBlock_of_C27L2 hR hq h1.1 h1.2.1 h) hL
  · exfalso
    obtain ⟨α, hα, hker, -⟩ := h.2.1
    exact hkn (mem_innerSub_of_out5 hα hker (out5Inner_alternating (by norm_num)) hk hk5)
  · exfalso
    obtain ⟨α, hα, hker, -⟩ := h.2.1
    exact hkn (mem_innerSub_of_out5 hα hker (out5Inner_alternating (by norm_num)) hk hk5)
  · exfalso
    obtain ⟨α, hα, hker, -⟩ := h.2.1
    exact hkn (mem_innerSub_of_out5 hα hker (out5Inner_alternating (by norm_num)) hk hk5)
  · exfalso
    obtain ⟨⟨n, α, hn5, -, -, ⟨hα, hker, -⟩, -⟩, -⟩ := h
    exact hkn (mem_innerSub_of_out5 hα hker (out5Inner_alternating hn5) hk hk5)
  · exfalso
    exact hkn (mem_innerSub_of_out5_quot (out5Inner_isHat_alternating_six h.1.2.1) hk hk5)
  · exfalso
    obtain ⟨α, hα, hker⟩ := h.1.2.1
    exact hkn (mem_innerSub_of_out5 hα hker (out5Inner_alternating (by norm_num)) hk hk5)
  · rcases h.1 with hA | hS
    · exfalso
      obtain ⟨-, α, hα, hker, -⟩ := hA
      exact hkn (mem_innerSub_of_out5 hα hker (out5Inner_alternating (by norm_num)) hk hk5)
    · exact (false_of_sp4_block hS hrank).elim
  · exfalso
    exact hkn (mem_innerSub_of_out5_quot (hU33 _ h.1.2.1) hk hk5)
  · exact h
  · exfalso
    rcases h.1 with h1 | h1
    · obtain ⟨e⟩ := h1
      exact hkn (mem_innerSub_of_autOn_out5 hJV hq hD
        (out5Inner_statedSL_four.of_mulEquiv e.symm) hk hkV hk5)
    · obtain ⟨e⟩ := h1
      exact hkn (mem_innerSub_of_autOn_out5 hJV hq hD
        (out5Inner_statedSL_five.of_mulEquiv e.symm) hk hkV hk5)

section Residue

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem sup_le_mcOf_14615 (S : Setting146 G T M) {PQ : Subgroup G} {K₁ K₂ : Subgroup G} {s : G}
    (hred : IsRedCE T M H PQ p) (hset : Setup14615 T M H H₁ H₂ K₁ K₂ s) : K₁ ⊔ K₂ ≤ mcOf T := by
  have h := SBc13.kz_le_mcOf S hred
  rwa [hset.kz] at h

end Residue

@[expose] def Input14615ContraOuterD : Prop :=
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
                                  (¬ pCoreOf 2 (mcOf T) ≤ Subgroup.normalizer (J : Set G) ∨
                                    C27SL3 (g2_14615 K₂) (pCoreOf 2 (mcOf T)) (g12_14615 T K₂) J
                                      (omegaOneCenterOf (pCoreOf 2 (J ⊔ pCoreOf 2 (mcOf T))))) →
                                    False

theorem input14615ContraOuterC_of_D (hU33 : FactOut5U33) (iOD : Input14615ContraOuterD) :
    Input14615ContraOuterC := by
  intro G _ _ hC27 T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx K₁ K₂ s hset hG₂ hfix hHyp hchar
    hPcore J hJc hJq hJle hJK hJ5 hK₁N hK₂N hK₂c hWG hout hL
  refine iOD G hC27 T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx K₁ K₂ s hset hG₂ hfix hHyp hchar
    hPcore J hJc hJq hJle hJK hJ5 hK₁N hK₂N hK₂c hWG hout hL ?_
  by_cases hR : pCoreOf 2 (mcOf T) ≤ Subgroup.normalizer (J : Set G)
  · right
    obtain ⟨k, hkK, hk5, hkn⟩ := hout
    have hkJ : k ∈ Subgroup.normalizer (J : Set G) := sup_le hK₁N hK₂N hkK
    have hkG : k ∈ mcOf T := sup_le_mcOf_14615 S hred hset hkK
    have hkR : k ∈ Subgroup.normalizer (pCoreOf 2 (mcOf T) : Set G) :=
      le_normalizer_pCoreOf 2 (mcOf T) hkG
    have hk5' : k ^ 5 = 1 := by rw [← hk5]; exact pow_orderOf_eq_one k
    exact false_of_outer_cases hU33 hC27 hHyp hJc hJq hchar hJle hR hkJ hkR hk5' hkn hJ5 hL
  · exact Or.inl hR

end SBc17

theorem stages14613_to_14617_of_SBc17D_noUK_solDec (hU33 : SBc17.FactOut5U33)
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (h2 : Stage1461Two) (h5 : Stage1461Five) (h12 : Stage14612PartP) (h4 : Stage1463Four)
    (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (iA : Input14613AP) (iB1 : Input14613B1P) (iB2 : Input14613B2P)
    (i14b : Input14614SolDec) (i14c : Input14614Shape)
    (iSF : Input14615SetupFourP) (iFix : SBc17.Input14615FixR)
    (iOD : SBc17.Input14615ContraOuterD) (iIB : SBc17.Input14615ContraInnerB)
    (iWeak : Input14616Weak) (iF : Input14617FstarK) :
    Stage14613LabP ∧ Stage14614 ∧ Stage14615 ∧ Stage14616 ∧ Stage14617 :=
  stages14613_to_14617_of_SBc17C_noUK_solDec hC27 h2 h5 h12 h4 h36 h38 iA iB1 iB2 i14b i14c iSF iFix
    (SBc17.input14615ContraOuterC_of_D hU33 iOD) iIB iWeak iF

end CFSG.Quasithin
