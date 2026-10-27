module

public import CFSG.Quasithin.Vol2.Ch11SecQ9bOne
public import CFSG.Quasithin.Vol2.Ch11SecQ9bL2pA
public import CFSG.Quasithin.Vol2.Ch11SecQ9bL2pD
public import CFSG.Quasithin.Vol2.Ch11SecQ9bOut

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin SecS

variable {G : Type} [Group G] [Finite G] {T L I V₁ V₂ X K : Subgroup G} {n : ℕ}

namespace C11P9B

theorem list3_cases (hFb : Facts12b) (hC : CartanFacts) (hF : Facts12) (hF11 : Facts11)
    (hN : NatFacts) (h318 : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I 2) (hV₁ : IsVi T L I 2 1 V₁)
    (hV₂ : IsVi T L I 2 2 V₂) (hX : IsCartanX T L X)
    (hK : K ∈ cComp (Subgroup.normalizer (V₁ : Set G)))
    (hNK : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hlt : LOf L V₁ < K) (hlist : List11_1_1Three (↥K ⧸ CFSG.pCore 2 ↥K)) :
    (Case11_1_2One K ∧ ¬ CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) ∨
      (Case11_1_2Two L K ∧ ∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧ IsPSL 2 p 1 (↥K ⧸ CFSG.pCore 2 ↥K)) := by
  have hR := false_of_rank3 hFb hC hF hF11 hN h318 h36 h38 h1102 h hV₁ hV₂ hX hK hNK hlt
  have hO := false_of_outerList hFb hC hF hF11 hN h1102 h hV₁ hV₂ hX hK hNK hlt.le
  rcases hlist with h1 | h2 | ⟨p, hp, h5, h8, hP⟩ | h4 | ⟨s, h5 | h5⟩ | h6 | h7 | h8 | h9 | h10 |
    h11 | h12 | h13 | h14 | h15
  · exact (hR (Or.inl h1)).elim
  · exact (hR (Or.inr (Or.inl h2))).elim
  · have hp11 : 11 ≤ p := by omega
    have hS : ∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧ IsPSL 2 p 1 (↥K ⧸ CFSG.pCore 2 ↥K) := ⟨p, hp, hp11, hP⟩
    refine Or.inr ⟨⟨hS, ?_⟩, hS⟩
    exact not_isSL3_of_centralizes hFb hC hF h331 hN h1102 h hV₁ hV₂ hX hK hNK hlt
      fun x hx k hk => commutator_mem_of_L2p hFb hC hF hN h1102 h hV₁ hV₂ hX hNK hlt.le hS hx hk
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
  · exact (false_of_J1 hFb h331 hN h1102 h hV₁ hK hNK hlt h9).elim
  · exact (hR (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h10))))))).elim
  · exact (hR (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h11)))))))).elim
  · exact (hR (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h12))))))))).elim
  · exact (hR (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h13)))))))))).elim
  · exact Or.inl (case1_of_A36Case4 h14)
  · exact Or.inl (case1_of_natural h15)

theorem case_i1 (hFb : Facts12b) (hC : CartanFacts) (hF : Facts12) (hF11 : Facts11)
    (hN : NatFacts) (h318 : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2) (hStar : Stmt11_1_2Star) (h : Hyp11 G T L I n)
    (hV₁ : IsVi T L I n 1 V₁) (hV₂ : IsVi T L I n 2 V₂) (hX : IsCartanX T L X)
    (hK : K ∈ cComp (Subgroup.normalizer (V₁ : Set G)))
    (hNK : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hLK : LOf L V₁ ≤ K)
    (hcases : LOf L V₁ = K ∨ List11_1_1Two (↥K ⧸ CFSG.pCore 2 ↥K) n ∨
      (n = 2 ∧ List11_1_1Three (↥K ⧸ CFSG.pCore 2 ↥K))) :
    LOf L V₁ = K ∨ (n = 2 ∧
      ((Case11_1_2Three T L K X (LOf L V₁) (LOf L V₂) ∧ IsPSL 3 2 2 (↥K ⧸ CFSG.pCore 2 ↥K)) ∨
        (Case11_1_2Two L K ∧ ∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧ IsPSL 2 p 1 (↥K ⧸ CFSG.pCore 2 ↥K)) ∨
        (Case11_1_2One K ∧ ¬ CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)))) := by
  by_cases heq : LOf L V₁ = K
  · exact Or.inl heq
  have hlt : LOf L V₁ < K := lt_of_le_of_ne hLK heq
  rcases hcases with heq' | h2 | ⟨rfl, h3⟩
  · exact (heq heq').elim
  · obtain ⟨hn, hPSL, h3⟩ := partB' hF hC hF11 hN h318 h36 h38 h1102 hStar h hV₁ hV₂ hX hK hNK
      hlt h2
    exact Or.inr ⟨hn, Or.inl ⟨h3, hPSL⟩⟩
  · rcases list3_cases hFb hC hF hF11 hN h318 h36 h38 h331 h1102 h hV₁ hV₂ hX hK hNK hlt h3 with
      h1 | h2
    · exact Or.inr ⟨rfl, Or.inr (Or.inr h1)⟩
    · exact Or.inr ⟨rfl, Or.inr (Or.inl h2)⟩

end C11P9B

end CFSG.Quasithin.Vol2.Ch11.SecA
