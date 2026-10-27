module

public import CFSG.Quasithin.Vol2.Ch11SecSRole4
public import CFSG.Quasithin.Vol2.Ch11SecSShape2
public import CFSG.Quasithin.Vol2.Ch11SecSSym6
public import CFSG.Quasithin.Vol2.Ch11SecSZL2
public import CFSG.Quasithin.Vol2.Ch11SecSMain
public import CFSG.Quasithin.Vol2.Ch11SecSRole2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

@[expose] def Obl11_1_2StarSymRole' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I V₁ V₂ X K K₀ I' U₁ U₂ : Subgroup G),
    StarHyp G T L I V₁ V₂ X K → IsK0 T L V₁ K K₀ → ¬ KindSL3 L (fsuV T I) 2 →
    pCoreOf 2 (K₀ ⊔ LOf L V₂ ⊔ X ⊔ T) ≠ ⊥ →
    quasithinIsCComponent (K₀ ⊔ LOf L V₂) (K₀ ⊔ LOf L V₂ ⊔ X ⊔ T) →
    T ≤ Subgroup.normalizer ((K₀ ⊔ LOf L V₂ : Subgroup G) : Set G) →
    X ≤ K₀ ⊔ LOf L V₂ → Shape11 (K₀ ⊔ LOf L V₂) 2 →
    ¬ IsPSL 3 2 2 (↥(K₀ ⊔ LOf L V₂) ⧸ CFSG.pCore 2 ↥(K₀ ⊔ LOf L V₂)) →
    Hyp11 G T (K₀ ⊔ LOf L V₂) I' 2 →
    IsVi T (K₀ ⊔ LOf L V₂) I' 2 1 U₁ → IsVi T (K₀ ⊔ LOf L V₂) I' 2 2 U₂ →
    ⁅quasithinOmegaOneCenter T, K⁆ = ⊥ →
    fsuV T I' ⊓ Subgroup.centralizer ((K₀ ⊔ LOf L V₂ : Subgroup G) : Set G) = ⊥ →
    LOf (K₀ ⊔ LOf L V₂) U₁ = K₀ → LOf (K₀ ⊔ LOf L V₂) U₂ = LOf L V₂ →
    IsCartanX T (K₀ ⊔ LOf L V₂) X → K ≤ Subgroup.centralizer (U₁ : Set G) →
      quasithinIsCComponent K (Subgroup.normalizer (U₁ : Set G))

theorem obl11_1_2StarSymRole_of (hF : FactL34Parab) (hLevi : FactL34Levi)
    (hT : FactPGL34Torus) (hB : FactBorelShape) (hPT : FactParabTwo) (hNP : NatPointFacts)
    (hC : CartanFacts) (hN : NatFacts) (hG2 : FactG2DerivedOrder) (h1102 : Stmt11_0_2)
    (hR5 : Obl11_1_2StarSymRole') : Obl11_1_2StarSymRole := by
  intro G _ _ T L I V₁ V₂ X K K₀ I' U₁ U₂ h hK0 hnSL hY hI₀ hTJ hXJ hshape hn hJ hU₁ hU₂ hZK hCV
  have hK0' := hK0
  obtain ⟨hK₀, hK₀K, hne, hne₁⟩ := hK0
  have hL₁ne : LOf L V₁ ≠ ⊥ :=
    ne_bot_of_mem_cComp (lOf_mem_lFamily hN h1102 h.hyp h.v₁ (Or.inl rfl) le_rfl)
  obtain ⟨P₁, P₂, hP⟩ := h.exists_parData hF hL₁ne
  obtain ⟨cL, -, -⟩ := cartan_of hC hN hG2 h1102 h.hyp h.v₁ h.v₂ h.cartan
  have hK₀eq : K₀ = k0Of K P₂ := by
    rcases h.eq_of_isLocal_le hP hK₀ hK₀K with h1 | h1 | h1
    · exact absurd h1 hne
    · exact absurd h1 hne₁
    · exact h1
  subst hK₀eq
  have hcart := h.isCartanX_J hB hLevi hT hN h1102 cL hP hJ le_sup_left le_sup_right hXJ hn
  have hR1 := h.lOf_one_eq_J hPT hNP hLevi hT hN h1102 cL hP hJ hU₁ hcart hCV le_sup_left
    le_sup_right hXJ hZK
  have hR2 := h.lOf_two_eq_J hPT hLevi hT hC hN hG2 h1102 cL hP hJ hU₁ hU₂ hcart hR1
    le_sup_left le_sup_right hXJ
  have hR4 := h.le_centralizer_U₁ hNP hN h1102 hJ hU₁ hcart hCV hZK
  exact ⟨hR1, hR2, hcart, hR4, hR5 G T L I V₁ V₂ X K _ I' U₁ U₂ h hK0' hnSL hY hI₀ hTJ hXJ
    hshape hn hJ hU₁ hU₂ hZK hCV hR1 hR2 hcart hR4⟩

theorem stmt11_1_2Star_of'''
    (hF : FactL34Parab) (hPGL : FactPGL34Levi) (hLevi : FactL34Levi)
    (hT : FactPGL34Torus) (hIns : FactShapeInspect) (hNo : FactL34NoE9) (hPG : FactParabGen)
    (hB : FactBorelShape) (hPT : FactParabTwo) (hNP : NatPointFacts) (hNF : NatFixedFacts)
    (hC : CartanFacts) (hN : NatFacts) (hG2 : FactG2DerivedOrder) (hG2a : FactG2AdjointOrder)
    (hRQ : RankTwoQuasisimple) (hFp : FactL2Parabolic) (h1102 : Stmt11_0_2)
    (h1110 : Stmt11_1_0) (h128 : Lemma128Four) (hfsu : Ch10.StmtFSUChoice) (h36 : A36ForSQTK)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h312 : A312ForSQTK)
    (hAm : Obl11_1_2StarAmalgam) (hJ4 : Obl11_1_2StarShapeJ4) (hSL3 : Obl11_1_2StarSL3)
    (hZK : Obl11_1_2StarZK) (hR5 : Obl11_1_2StarSymRole') : Stmt11_1_2Star :=
  stmt11_1_2Star_of hF hPGL hC hN hG2 hG2a h1102 h37 h38 h39 hAm
      (obl11_1_2StarShape_of hF hLevi hT hIns hJ4 hC hN hG2 h1102 hFp h36 h312) hSL3
      (obl11_1_2StarSym_of hF hLevi hT hNo hPG hC hN hG2 hG2a hRQ h1102 h1110 h128 hfsu h37 h38 h39
          (obl11_1_2StarZL2_of hNF h1102) hZK
          (obl11_1_2StarSymRole_of hF hLevi hT hB hPT hNP hC hN hG2 h1102 hR5))

end CFSG.Quasithin.Vol2.Ch11.SecS
