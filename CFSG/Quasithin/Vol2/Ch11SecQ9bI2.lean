module

public import CFSG.Quasithin.Vol2.Ch11SecQ9bI2c
public import CFSG.Quasithin.Vol2.Ch11SecQ9bI1
public import CFSG.Quasithin.Vol2.Ch11SecQ9bI2a
public import CFSG.Quasithin.Vol2.Ch11SecQ9bI2b

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin SecS

variable {G : Type} [Group G] [Finite G] {T L I V₁ V₂ X K : Subgroup G} {n : ℕ}

namespace C11P9B

theorem isSylowTwoOf_inf_normalizer_V1 (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁) :
    QuasithinUnique.IsSylowTwoOf (T ⊓ Subgroup.normalizer (V₁ : Set G))
      (Subgroup.normalizer (V₁ : Set G)) := by
  rw [inf_eq_left.mpr (IsVi.le_normalizer hV₁)]
  exact isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow (IsVi.le_normalizer hV₁)

theorem desc_K₁ (hFb : Facts12b) (hC : CartanFacts) (hF : Facts12) (hF11 : Facts11)
    (hN : NatFacts) (h318 : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2) (h1111 : Stmt11_1_1) (hStar : Stmt11_1_2Star)
    (h : Hyp11 G T L I 2) (hV₁ : IsVi T L I 2 1 V₁) (hV₂ : IsVi T L I 2 2 V₂)
    (hX : IsCartanX T L X) :
    ∃ K₁ : Subgroup G, K₁ ∈ cComp (Subgroup.normalizer (V₁ : Set G)) ∧
      Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (K₁ : Set G) ∧ LOf L V₁ ≤ K₁ ∧
      (IsPSL 3 2 2 (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) ∨
        (∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧ IsPSL 2 p 1 (↥K₁ ⧸ CFSG.pCore 2 ↥K₁)) ∨
        (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
          Nonempty ((↥K₁ ⧸ CFSG.pCore 2 ↥K₁) ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∨
        ¬ CFSG.IsQuasisimple (↥K₁ ⧸ CFSG.pCore 2 ↥K₁)) := by
  obtain ⟨K₁, hL₁K₁, hK₁, hNK₁, hcases⟩ := h1111 G T L I 2 1 V₁ V₁ h hV₁
    (Or.inl ⟨rfl, IsVi.ne_bot h hV₁ le_rfl, le_rfl, isSylowTwoOf_inf_normalizer_V1 h hV₁⟩)
  refine ⟨K₁, hK₁, hNK₁, hL₁K₁, ?_⟩
  rcases case_i1 hFb hC hF hF11 hN h318 h36 h38 h331 h1102 hStar h hV₁ hV₂ hX hK₁ hNK₁ hL₁K₁
      hcases with heq | ⟨-, ⟨-, h3⟩ | ⟨-, h2⟩ | ⟨-, h1⟩⟩
  · subst heq
    obtain ⟨F, _, _, hF4, ⟨e⟩⟩ := lOf_quot_SL2 hN h1102 h (Or.inl rfl) hV₁
    exact Or.inr (Or.inr (Or.inl ⟨F, inferInstance, inferInstance, hF4.trans (by norm_num),
      ⟨e⟩⟩))
  · exact Or.inl h3
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inr h1))

theorem case_i2 (hF : Facts12) (hFb : Facts12b) (hFc : Facts12c) (hC : CartanFacts)
    (hF11 : Facts11) (hN : NatFacts) (hL3 : FactLineSL3) (hLp : FactLineSp4) (hLg : FactLineG2)
    (hPG : SecS.FactParabGen) (h318 : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (h36c : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h133 : Tmp1_3_3)
    (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3) (h1111 : Stmt11_1_1)
    (hStar : Stmt11_1_2Star) (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁)
    (hV₂ : IsVi T L I n 2 V₂) (hX : IsCartanX T L X)
    (hK : K ∈ cComp (Subgroup.normalizer (V₂ : Set G)))
    (hNK : Subgroup.normalizer (V₂ : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hLK : LOf L V₂ ≤ K)
    (hcases : LOf L V₂ = K ∨ List11_1_1Two (↥K ⧸ CFSG.pCore 2 ↥K) n ∨
      (n = 2 ∧ List11_1_1Three (↥K ⧸ CFSG.pCore 2 ↥K))) :
    LOf L V₂ = K := by
  by_contra hne
  have hlt : LOf L V₂ < K := lt_of_le_of_ne hLK hne
  have hc : Concl1111 (↥K ⧸ CFSG.pCore 2 ↥K) n := hcases.resolve_left hne
  rcases modules3n_V2 hFc hN hL3 hLp hLg h1102 h1103 h hV₂ hK hNK hLK hc with
    ⟨rfl, hA7, hZ⟩ | ⟨rfl, hnq, hFit⟩
  · exact false_of_case_b hFb hFc hC hN h318 h36 h38 h1102 h hV₁ hV₂ hX hK hNK hLK hA7 hZ
  · obtain ⟨K₁, hK₁, hNK₁, hL₁K₁, hdesc⟩ :=
      desc_K₁ hFb hC hF hF11 hN h318 h36 h38 h331 h1102 h1111 hStar h hV₁ hV₂ hX
    exact false_of_case_c hF hFb hF11 hN hL3 hLp hLg hPG h36c h133 h331 h1102 h hV₁ hV₂
      hK₁ hNK₁ hL₁K₁ hdesc hK hNK hlt hc hnq hFit

end C11P9B

end CFSG.Quasithin.Vol2.Ch11.SecA
