module

public import CFSG.Quasithin.Background.GoldschmidtE23FourY0
public import CFSG.Quasithin.Background.C126Defs
public import CFSG.Quasithin.Background.C126Split

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B2F

namespace E2

variable {G : Type} [Group G] [Finite G]

theorem sylow_baum_or_a5Case {H T V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hc : E23Concl H T V hV) :
    IsSylowTwoOf (baum T) (twoResidual H ⊔ baum T) ∨ C126.A5Case H T V hV := by
  obtain ⟨hKJ, I, hfam⟩ := (C126.e23Concl_iff H T V hV).1 hc
  have hfam' := hfam
  obtain ⟨hIcard, -, -, -, hconj, htype, -, -, h2, -⟩ := hfam
  obtain ⟨L₀, hL₀⟩ : I.Nonempty := Finset.card_pos.1 (by rcases hIcard with h | h <;> omega)
  have hcardeq : ∀ L ∈ I, Nat.card ↥L = Nat.card ↥L₀ := fun L hL => by
    obtain ⟨t, -, ht⟩ := hconj L₀ hL₀ L hL
    rw [← ht, B1.card_conjAut]
  rcases htype L₀ hL₀ with ⟨n₀, hn₀⟩ | hA₀
  · left
    have hall : ∀ L ∈ I, ∃ n : ℕ, IsL2Natural L (fixV (autI hV (twoResidual H))) n := by
      intro L hL
      rcases htype L hL with ⟨n, hn⟩ | hA
      · exact ⟨n, hn⟩
      · exact absurd ((C126.card_of_isL2Natural hn₀).symm.trans
          ((hcardeq L hL).symm.trans (C126.card_of_isA5Module hA))) (C126.two_pow_mul_ne_120 n₀)
    exact (h2 hall).2.2.1
  · right
    have hall : ∀ L ∈ I, IsA5Module L := by
      intro L hL
      rcases htype L hL with ⟨n, hn⟩ | hA
      · exact absurd ((C126.card_of_isL2Natural hn).symm.trans
          ((hcardeq L hL).trans (C126.card_of_isA5Module hA₀))) (C126.two_pow_mul_ne_120 n)
      · exact hA
    exact ⟨hKJ, I, hfam', hall⟩

@[expose] def E23FourA5Statement : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (H T M V : Subgroup Γ) (hV : IsElemAbelian 2 V),
    MinParabolic H T M → SQTKGroup ↥H → CharTwo H → IsTwoReducedIn H V →
    ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set Γ) → C126.A5Case H T V hV →
    (∀ C : Subgroup Γ, C ≤ baum T → C ≠ ⊥ → (C.subgroupOf (baum T)).Characteristic →
      ¬ H ≤ Subgroup.normalizer (C : Set Γ)) →
    ∃ L : Subgroup Γ, IsChi0Block H L ∧ H = L ⊔ T ∧ (¬ IsAltType L 3 → L ∈ cComp H)

theorem e23FourStatement_of_inputs (h129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G)
    (he23 : E23Statement) (hA5 : E23FourA5Statement) : E23FourStatement := by
  intro Γ _ _ H T M V hmin hsq hF hred hJ hPU
  have hV : IsElemAbelian 2 V := hred.2.2.1
  have hc := he23 Γ H T M V hV hmin hsq hF hred hJ
  rcases sylow_baum_or_a5Case hV hc with hSyl | h5
  · exact exists_chi0Block_of_sylow_baum (h129 Γ) hmin hsq hF hPU hSyl
  · exact hA5 Γ H T M V hV hmin hsq hF hred hJ h5 hPU

end E2

end CFSG.Quasithin
