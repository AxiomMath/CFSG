module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aAmX
public import CFSG.Quasithin.Vol2.Ch11SecQ9aAmV
public import CFSG.Quasithin.Vol2.Ch11SecQ9aAmT
public import CFSG.Quasithin.Vol2.Ch11SecQ9aAmQ
public import CFSG.Quasithin.Vol2.Ch11SecQ9aAmB
public import CFSG.Quasithin.Vol2.Ch11SecQ9aAmI
public import CFSG.Quasithin.Vol2.Ch11SecQ9aAmJ
public import CFSG.Quasithin.Vol2.Ch11SecQ9aAmL

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem f112L24G2NoNatural_of_l24G2 (hF : F112L24G2Statement) : F112L24G2NoNatural := by
  intro G _ _ L1 L2 S hyp hQ hS h1 h2 hb K V A B hKP hPK hKp hKsl hVP hPV hV4 hKV hAB hBP hBA
    hKA hKB hne y hy hy3
  by_contra hcon
  have hfree : ∀ b ∈ B, y * b * y⁻¹ * b⁻¹ ∈ A → b ∈ A := fun b hb hc =>
    by_contra fun hbA => hcon ⟨b, hb, hbA, hc⟩
  obtain ⟨L1', L2', hsw, hα⟩ := hF G L1 L2 S hyp hQ hS h1 h2 hb
  have hbig : bigB L2 L1 S = bigB L1 L2 S := by
    show borelOf L2 S ⊔ borelOf L1 S ⊔ S = borelOf L1 S ⊔ borelOf L2 S ⊔ S
    rw [sup_comm (borelOf L2 S) (borelOf L1 S)]
  rcases hsw with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1, e2] at hα
    exact false_of_g2Amalgam factG2FourLongParabolic_holds hα (Or.inl rfl) hKP hPK hKp hKsl hVP
      hPV hV4 hKV hAB hBP hBA hKA hKB hne hy hy3 hfree
  · rw [e1, e2, hbig] at hα
    exact false_of_g2Amalgam factG2FourLongParabolic_holds hα (Or.inr rfl) hKP hPK hKp hKsl hVP
      hPV hV4 hKV hAB hBP hBA hKA hKB hne hy hy3 hfree

end CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA C11AmS

theorem obl11_1_2StarAmalgam_of₃ (hF : F112L24G2NoNatural) (hRad : FactParabRadical)
    (hC : CartanFacts) (hN : NatFacts) (hG2 : FactG2DerivedOrder) (h1102 : Stmt11_0_2)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) : Obl11_1_2StarAmalgam := by
  intro G _ _ T L I V₁ V₂ X K K₀ h hK0 hY
  obtain ⟨hK₀, hK₀K, hne, hne₁⟩ := hK0
  have hL₁ne : LOf L V₁ ≠ ⊥ :=
    ne_bot_of_mem_cComp (lOf_mem_lFamily hN h1102 h.hyp h.v₁ (Or.inl rfl) le_rfl)
  obtain ⟨P₁, P₂, hP⟩ := h.exists_parData factL34Parab_holds hL₁ne
  obtain ⟨cL, -, -⟩ := cartan_of hC hN hG2 h1102 h.hyp h.v₁ h.v₂ h.cartan
  have hK₀eq : K₀ = k0Of K P₂ := by
    rcases h.eq_of_isLocal_le hP hK₀ hK₀K with h1 | h1 | h1
    · exact absurd h1 hne
    · exact absurd h1 hne₁
    · exact h1
  subst hK₀eq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hAB, y, hy, hy3, hfree⟩ := natural_section h hP
  have hPK := vertex_le_normalizer_k0Of hN h1102 h cL hP
  have hK₀O : k0Of K P₂ ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    (k0Of_le K P₂).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
  have hO₀ := CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) (k0Of K P₂)
  have hBP : pCoreOf 2 (k0Of K P₂) ≤
      pCoreOf 2 (k0Of K P₂ ⊔ bigB (k0Of K P₂) (LOf L V₂) (sXT X T)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans le_sup_left)
      (hPK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  obtain ⟨b, hb, hbA, hc⟩ := hF G (k0Of K P₂) (LOf L V₂) (sXT X T)
    (hyp111_of hN h1102 h cL hP hY) (isQuasithinSub_of h _)
    (Or.inl (normal_sXT_sup hN h1102 h cL hP)) (card_oTwoQuot_of_SL2 (k0Of_quot_SL2 h hP))
    (card_oTwoQuot_of_SL2 (lOf_two_quot_SL2 hN h1102 h))
    (Or.inr (not_isShort2_L₂ hRad hN h1102 h cL)) (k0Of K P₂) V₁
    (pCoreOf 2 (k0Of K P₂) ⊓ pCoreOf 2 K) (pCoreOf 2 (k0Of K P₂)) le_sup_left hPK
    (k0Of_perfect K P₂) (k0Of_quot_SL2 h hP) (V₁_le_vertex hN h1102 h)
    (vertex_le_normalizer_V₁ hN h1102 h cL) (card_V₁ h37 h38 h39 h)
    ((k0Of_le K P₂).trans h.le_cent) inf_le_left hBP
    (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hx, hK₀O (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx)⟩)
    (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf ⟨hO₀ hx, hK₀O hx⟩) hO₀ hAB y hy hy3
  exact hbA (hfree b hb hc)

theorem obl11_1_2StarAmalgam_of₃'' (hF : F112L24G2NoNatural) (hC : CartanFacts) (hN : NatFacts)
    (hG2 : FactG2DerivedOrder) (h1102 : Stmt11_0_2) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) : Obl11_1_2StarAmalgam :=
  obl11_1_2StarAmalgam_of₃ hF factParabRadical_holds hC hN hG2 h1102 h37 h38 h39

end CFSG.Quasithin.Vol2.Ch11.SecS
