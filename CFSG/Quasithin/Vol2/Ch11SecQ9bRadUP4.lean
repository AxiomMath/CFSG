module

public import CFSG.Quasithin.Vol2.Ch11SecQ9bRadUP3
public import CFSG.Quasithin.Vol2.Ch11SecQ9bOne

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin SecS

variable {G : Type} [Group G] [Finite G] {T L I V₁ V₂ X : Subgroup G}

namespace C11P9B

theorem desc_point (hFb : Facts12b) (hC : CartanFacts) (hF : Facts12) (hF11 : Facts11)
    (hN : NatFacts) (h318 : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2) (h1111 : Stmt11_1_1) (h : Hyp11 G T L I 2)
    (hV₁ : IsVi T L I 2 1 V₁) (hV₂ : IsVi T L I 2 2 V₂) (hX : IsCartanX T L X)
    {V₀ : Subgroup G} (hV₀₁ : V₀ ≤ V₁) (hV₀ : V₀ ≠ ⊥) (hTV₀ : T ≤ Subgroup.normalizer (V₀ : Set G))
    (hXV₀ : xOne X (LOf L V₁) ≤ Subgroup.normalizer (V₀ : Set G))
    (hXC₀ : xOne X (LOf L V₁) ⊓ Subgroup.centralizer (V₀ : Set G) = ⊥)
    (hLV₀ : L ⊓ Subgroup.normalizer (V₀ : Set G) ≤ Subgroup.normalizer (V₁ : Set G)) :
    ∃ K₀ : Subgroup G, K₀ ∈ cComp (Subgroup.normalizer (V₀ : Set G)) ∧
      Subgroup.normalizer (V₀ : Set G) ≤ Subgroup.normalizer (K₀ : Set G) ∧ LOf L V₁ ≤ K₀ ∧
      (IsPSL 3 2 2 (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) ∨
        (∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧ IsPSL 2 p 1 (↥K₀ ⧸ CFSG.pCore 2 ↥K₀)) ∨
        (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
          Nonempty ((↥K₀ ⧸ CFSG.pCore 2 ↥K₀) ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∨
        ¬ CFSG.IsQuasisimple (↥K₀ ⧸ CFSG.pCore 2 ↥K₀)) := by
  have hsyl : QuasithinUnique.IsSylowTwoOf (T ⊓ Subgroup.normalizer (V₀ : Set G))
      (Subgroup.normalizer (V₀ : Set G)) := by
    rw [inf_eq_left.mpr hTV₀]
    exact isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hTV₀
  obtain ⟨K₀, hL₁K₀, hK₀, hNK₀, hcases⟩ :=
    h1111 G T L I 2 1 V₁ V₀ h hV₁ (Or.inl ⟨rfl, hV₀, hV₀₁, hsyl⟩)
  refine ⟨K₀, hK₀, hNK₀, hL₁K₀, ?_⟩
  by_cases heq : LOf L V₁ = K₀
  · subst heq
    obtain ⟨F, _, _, hF4, ⟨e⟩⟩ := lOf_quot_SL2 hN h1102 h (Or.inl rfl) hV₁
    exact Or.inr (Or.inr (Or.inl ⟨F, inferInstance, inferInstance, hF4.trans (by norm_num),
      ⟨e⟩⟩))
  have hlt : LOf L V₁ < K₀ := lt_of_le_of_ne hL₁K₀ heq
  rcases hcases with heq' | h2 | ⟨-, h3⟩
  · exact (heq heq').elim
  · obtain ⟨hQ, hZ, hrk⟩ := hF.table _ 2 le_rfl h2
    obtain ⟨s, p, e, hp, he, hS⟩ := isPSLEps3_point hC hF hF11 hN h318 h36 h38 h1102 h hV₁ hV₂
      hX hV₀₁ hV₀ hXV₀ hXC₀ hK₀ hNK₀ hlt hQ hZ (hrk 3 Nat.prime_three (by norm_num))
    obtain ⟨rfl, rfl, rfl⟩ := hF.psl3 _ h2 s p e hp he hS
    exact Or.inl hS
  have hR := false_of_rank3_point hFb hC hF hF11 hN h318 h36 h38 h1102 h hV₁ hV₂ hX hV₀₁ hV₀
    hTV₀ hXV₀ hXC₀ hK₀ hNK₀ hlt
  have hO := false_of_outerList_point hFb hC hF hF11 hN h1102 h hV₁ hV₂ hX hV₀₁ hTV₀ hXV₀ hXC₀
    hK₀ hNK₀ hlt.le
  rcases h3 with h1 | h2 | ⟨p, hp, h5, h8, hP⟩ | h4 | ⟨s, h5 | h5⟩ | h6 | h7 | h8 | h9 | h10 |
    h11 | h12 | h13 | h14 | h15
  · exact (hR (Or.inl h1)).elim
  · exact (hR (Or.inr (Or.inl h2))).elim
  · exact Or.inr (Or.inl ⟨p, hp, by omega, hP⟩)
  · exact (hO (Or.inl h4)).elim
  · cases s
    · exact (hR (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl h5))))))))))).elim
    · exact (hO (Or.inr (Or.inl h5))).elim
  · cases s
    · exact (hO (Or.inr (Or.inr (Or.inr h5)))).elim
    · exact (hO (Or.inr (Or.inr (Or.inl h5)))).elim
  · exact (hR (Or.inr (Or.inr (Or.inl h6)))).elim
  · exact (hR (Or.inr (Or.inr (Or.inr (Or.inl h7))))).elim
  · exact (hR (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h8)))))).elim
  · exact (false_of_J1_point hFb hF11 h331 hN h1102 h hV₁ hV₀₁ hTV₀ hLV₀ hK₀ hNK₀ hlt h9).elim
  · exact (hR (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h10))))))).elim
  · exact (hR (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h11)))))))).elim
  · exact (hR (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h12))))))))).elim
  · exact (hR (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h13)))))))))).elim
  · exact Or.inr (Or.inr (Or.inr (case1_of_A36Case4 h14).2))
  · exact Or.inr (Or.inr (Or.inr (case1_of_natural h15).2))

end C11P9B

end CFSG.Quasithin.Vol2.Ch11.SecA
