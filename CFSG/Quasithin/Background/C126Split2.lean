module

public import CFSG.Quasithin.Background.C126Split
public import CFSG.GroupTheory.OrderBelowSixtySolvable
public import CFSG.Quasithin.Background.C126Defs

public section

namespace CFSG.Quasithin.C126

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin B2F E2

variable {G : Type} [Group G] [Finite G]

theorem case_split {H V : Subgroup G} (hV : IsElemAbelian 2 V) (T : Subgroup G)
    (hHN : H ≤ Subgroup.normalizer (V : Set G)) (hc : E2.E23Concl H T V hV) :
    perfectCore H ≤ Subgroup.centralizer (V : Set G) ∨ NatCase H T V hV ∨ A5Case H T V hV := by
  obtain ⟨hKJ, I, hfam⟩ := (e23Concl_iff H T V hV).1 hc
  have hfam' := hfam
  obtain ⟨hIcard, hJeq, hcomm, -, hconj, htype, -, -, -, -⟩ := hfam
  obtain ⟨L₀, hL₀⟩ : I.Nonempty := Finset.card_pos.1 (by rcases hIcard with h | h <;> omega)
  have hcardeq : ∀ L ∈ I, Nat.card ↥L = Nat.card ↥L₀ := fun L hL => by
    obtain ⟨t, -, ht⟩ := hconj L₀ hL₀ L hL
    rw [← ht, B1.card_conjAut]
  rcases htype L₀ hL₀ with ⟨n₀, hn₀⟩ | hA₀
  · have hall : ∀ L ∈ I, E2.IsL2Natural L (fixV (autI hV (twoResidual H))) n₀ := by
      intro L hL
      rcases htype L hL with ⟨n, hn⟩ | hA
      · have hnn : n = n₀ := strictMono_two_pow_mul.injective
          ((card_of_isL2Natural hn).symm.trans ((hcardeq L hL).trans (card_of_isL2Natural hn₀)))
        subst hnn
        exact hn
      · exact absurd ((card_of_isL2Natural hn₀).symm.trans
          ((hcardeq L hL).symm.trans (card_of_isA5Module hA))) (two_pow_mul_ne_120 n₀)
    by_cases hn2 : 2 ≤ n₀
    · exact Or.inr (Or.inl ⟨hKJ, I, hfam', fun L hL => ⟨n₀, hn2, hall L hL⟩⟩)
    · left
      have hn1 : n₀ = 1 := by
        have := hn₀.1
        omega
      subst hn1
      refine perfectCore_le_centralizer_of_J hV hHN hKJ ?_
      rw [hJeq]
      refine isSolvable_iSup_family I hIcard hcomm fun L hL => ?_
      have h6 : Nat.card ↥L = 6 := by
        rw [card_of_isL2Natural (hall L hL)]
        norm_num
      have : Finite ↥L := Nat.finite_of_card_ne_zero (by omega)
      exact CFSG.GroupTheory.groups_order_below_sixty_solvable (by omega)
  · have hall : ∀ L ∈ I, E2.IsA5Module L := by
      intro L hL
      rcases htype L hL with ⟨n, hn⟩ | hA
      · exact absurd ((card_of_isL2Natural hn).symm.trans
          ((hcardeq L hL).trans (card_of_isA5Module hA₀))) (two_pow_mul_ne_120 n)
      · exact hA
    exact Or.inr (Or.inr ⟨hKJ, I, hfam', hall⟩)

end CFSG.Quasithin.C126
