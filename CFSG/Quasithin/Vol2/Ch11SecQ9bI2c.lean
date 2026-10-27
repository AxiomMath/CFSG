module

public import CFSG.Quasithin.Vol2.Ch11SecQ9bC1
public import CFSG.Quasithin.Vol2.Ch11SecOE6G
public import CFSG.Quasithin.Vol2.Ch11SecA12KX
public import CFSG.Quasithin.Vol2.Ch11SecQ9bXi

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin SecS

variable {G : Type} [Group G] [Finite G] {T L I V₁ V₂ X K : Subgroup G}

namespace C11P9B

theorem lOf_one_le_normalizer_xi (h36c : QuasithinUnique.Vol2Native.A36CoreForSQTKCat)
    (h : Hyp11 G T L I 2) (hV₁ : IsVi T L I 2 1 V₁) {K₁ Y : Subgroup G}
    (hK₁ : K₁ ∈ cComp (Subgroup.normalizer (V₁ : Set G)))
    (hNK₁ : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (K₁ : Set G))
    (hL₁K₁ : LOf L V₁ ≤ K₁)
    (hdesc : IsPSL 3 2 2 (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) ∨
      (∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧ IsPSL 2 p 1 (↥K₁ ⧸ CFSG.pCore 2 ↥K₁)) ∨
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
        Nonempty ((↥K₁ ⧸ CFSG.pCore 2 ↥K₁) ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∨
      ¬ CFSG.IsQuasisimple (↥K₁ ⧸ CFSG.pCore 2 ↥K₁))
    (hXi : IsXi T Y) (hYH : Y ⊔ T ≤ Subgroup.normalizer (V₁ : Set G))
    (hY5 : ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ Nat.card Y → 5 ≤ q) :
    LOf L V₁ ≤ Subgroup.normalizer (Y : Set G) := by
  have := h.fsu.simple
  have hloc : QuasithinUnique.LocalSQTK G :=
    (QuasithinUnique.qtkeCore_of_cat h.fsu.nonabelian h.fsu.qtke).1
  exact hL₁K₁.trans (OE6.cComp_le_normalizer_xi h36c hloc h.fsu.sylow
    (pCoreOf_normalizer_ne_bot h hV₁ le_rfl) hK₁ hNK₁ hdesc hXi hYH hY5)

theorem false_of_case_c (hF : Facts12) (hFb : Facts12b) (hF11 : Facts11)
    (hN : NatFacts) (hL3 : FactLineSL3) (hLp : FactLineSp4) (hLg : FactLineG2)
    (hPG : SecS.FactParabGen) (h36c : QuasithinUnique.Vol2Native.A36CoreForSQTKCat)
    (h133 : Tmp1_3_3) (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I 2) (hV₁ : IsVi T L I 2 1 V₁) (hV₂ : IsVi T L I 2 2 V₂) {K₁ : Subgroup G}
    (hK₁ : K₁ ∈ cComp (Subgroup.normalizer (V₁ : Set G)))
    (hNK₁ : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (K₁ : Set G))
    (hL₁K₁ : LOf L V₁ ≤ K₁)
    (hdesc : IsPSL 3 2 2 (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) ∨
      (∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧ IsPSL 2 p 1 (↥K₁ ⧸ CFSG.pCore 2 ↥K₁)) ∨
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
        Nonempty ((↥K₁ ⧸ CFSG.pCore 2 ↥K₁) ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∨
      ¬ CFSG.IsQuasisimple (↥K₁ ⧸ CFSG.pCore 2 ↥K₁))
    (hK : K ∈ cComp (Subgroup.normalizer (V₂ : Set G)))
    (hNK : Subgroup.normalizer (V₂ : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hlt : LOf L V₂ < K) (hc : Concl1111 (↥K ⧸ CFSG.pCore 2 ↥K) 2)
    (hnq : ¬ CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hFc' : ∀ y : ↥K, (QuotientGroup.mk y : ↥K ⧸ CFSG.pCore 2 ↥K) ∈
      CFSG.fittingSubgroup (↥K ⧸ CFSG.pCore 2 ↥K) → Odd (orderOf y) →
      (y : G) ∈ Subgroup.centralizer (V₂ : Set G)) : False := by
  obtain ⟨p, hp, hp2, hpF⟩ := exists_odd_prime_dvd_fitting hF hFb le_rfl hc hnq
  have : Fact p.Prime := ⟨hp⟩
  have hTsyl : QuasithinUnique.IsSylowTwoOf T (Subgroup.normalizer (V₂ : Set G)) :=
    isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow (IsVi.le_normalizer hV₂)
  have hloc' : quasithinIsLocal T K :=
    isLocal_of_mem_cComp_of_sylow hTsyl (pCoreOf_normalizer_ne_bot h hV₂ (by norm_num)) hK
  have hXi : IsXi T (xiP K p) :=
    h133 G T K p h.fsu.simple h.fsu.nonabelian h.fsu.qtke h.fsu.sylow hloc' hnq hp hp2 hpF
  have hKY : K ≤ Subgroup.normalizer (xiP K p : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_xiP p)
  have hYH : xiP K p ⊔ T ≤ Subgroup.normalizer (V₁ : Set G) :=
    sup_le ((xiP_le_centralizer hFc').trans
      ((Subgroup.centralizer_le (IsVi.mono₁₂ hN h1102 h hV₁ hV₂)).trans
        (Subgroup.centralizer_le_normalizer _))) (IsVi.le_normalizer hV₁)
  have := h.fsu.simple
  have hloc : QuasithinUnique.LocalSQTK G :=
    (QuasithinUnique.qtkeCore_of_cat h.fsu.nonabelian h.fsu.qtke).1
  have hY5 := OE6.five_le_of_dvd_card_xiP h36c hloc
    (pCoreOf_normalizer_ne_bot h hV₂ (by norm_num)) hK hNK hnq hp hpF
  have hL₁Y := lOf_one_le_normalizer_xi h36c h hV₁ hK₁ hNK₁ hL₁K₁ hdesc hXi hYH hY5
  have hTY : T ≤ Subgroup.normalizer (xiP K p : Set G) := hXi.2.1
  have hOLT : pCoreOf 2 L ≤ T :=
    (pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_inf_L h)).trans inf_le_left
  have hLY : L ⊔ T ≤ Subgroup.normalizer (xiP K p : Set G) :=
    sup_le ((le_sup_lOf₁₂ hPG hF11 hN hL3 hLp hLg h1102 h hV₁ hV₂).trans
      (sup_le (sup_le hL₁Y (hlt.le.trans hKY)) (hOLT.trans hTY))) hTY
  have hP1 := pCoreOf_ne_bot_of_isXi (charTwo_of_cComp h hV₂ (by norm_num) hK hNK) hXi
    (xiP_le p) hKY
  have hPN := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (xiP K p)
  have hM := normalizer_le_of_isPGroup h331 h
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (xiP K p)) hP1 (hLY.trans hPN)
  exact not_le_normalizer_of_lt hN h1102 h hV₂ (Or.inr rfl) hK hlt (hKY.trans (hPN.trans hM))

end C11P9B

end CFSG.Quasithin.Vol2.Ch11.SecA
