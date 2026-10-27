module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213Cl
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213KGW

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

theorem stmt4_2_13FF_of_steps (h36 : A36ForSQTK)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h48 : ∀ (G : Type) [Group G] [Finite G], ASC48Statement G) (h425 : Thm4_2_5)
    (hFF : ∀ (G : Type) [Group G] [Finite G] (T M L Mm I H K : Subgroup G),
      Hyp4_2_3 G T M L Mm I → InM I H → Conf4212 G T M L I H K → ¬ oTwoFstarIn H ≤ M →
      (C48Case1 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
        C48Case2 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
        C48Case3 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
        C48Case4 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
        C48Case5 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
        C48Case7 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
        C48Case8 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K) →
      (∃ _ : IsMulCommutative ↥⁅reducedAggregate (L ⊔ T), L⁆,
        IsFFModule (V := ↥⁅reducedAggregate (L ⊔ T), L⁆)
          (autOn (L ⊔ T) ⁅reducedAggregate (L ⊔ T), L⁆)) ∨
        Orth4213 G M L ⁅reducedAggregate (L ⊔ T), L⁆)
    (hKGf : KGHatA6M24He) (hKGg : KGG2BlockRu)
    (hJ4 : ∀ (G : Type) [Group G] [Finite G] (T M L Mm I H K : Subgroup G),
      Hyp4_2_3 G T M L Mm I → InM I H → Conf4212 G T M L I H K →
      ¬ C48Case6 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K) :
    Stmt4_2_13FF := by
  refine stmt4_2_13FF_of_hyp4_2_3 h37 h38 h39 fun G _ _ T M L Mm I hy => ?_
  obtain ⟨H₀, hH₀, hH₀M⟩ := hy.gammaStar.1.2
  obtain ⟨H, hH⟩ := exists_inM_of_pCoreOf_ne_bot hH₀.2
  have hIH : InM I H := ⟨hH.1, hH₀.1.trans hH.2⟩
  have hHM : ¬ H ≤ M := fun h => hH₀M (hH.2.trans h)
  have hne : H ≠ M := fun h => hHM (h ▸ le_rfl)
  have h425' := h425 G T M L Mm I H hy hIH hne
  obtain ⟨K, c⟩ := hy.lemma_4_2_12_two h36 h37 h38 h39 (h48 G) (inH_of_inM hIH) hHM h425'
  have hgood : (C48Case1 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H))
        ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case2 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case3 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case4 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case5 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case7 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case8 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K) := by
    rcases c.cases with h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact absurd h (hJ4 G T M L Mm I H K hy hIH c)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
    · exact (c.false_of_case9 h37 h38 h39 h).elim
  rcases hFF G T M L Mm I H K hy hIH c h425' hgood with hF | hO
  · exact Or.inl ⟨c.concl443TwoI_of hgood hF (c.hat_clause hKGf) (c.psu_clause hKGg),
      c.irrCase4213 hgood⟩
  · exact Or.inr hO

end CFSG.Quasithin.H13.Ch4
