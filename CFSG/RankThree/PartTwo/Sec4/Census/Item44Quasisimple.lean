module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44EndRep
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Mathieu
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Janko
import CFSG.RankThree.PartTwo.Sec4.Census.Item44Three
import CFSG.RankThree.PartTwo.Sec4.Census.Item44RankTwo
import CFSG.GroupTheory.ABGDGroups.LinearEmbedding

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG CFSG.Blueprint CFSG.RankThree.PartTwo Subgroup
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def QuasisimpleCensus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G) [K.Normal], PartTwoRankThreeHyp G K →
    IsQuasisimple (G ⧸ oddCore G) →
      Nonempty ((G ⧸ oddCore G) ⧸ center (G ⧸ oddCore G) ≃* NativeSporadic.M12) ∨
      (Nonempty ((G ⧸ oddCore G) ⧸ center (G ⧸ oddCore G) ≃* NativeSporadic.M22) ∧
        Nat.card (center (G ⧸ oddCore G)) = 4) ∨
      Nonempty ((G ⧸ oddCore G) ⧸ center (G ⧸ oddCore G) ≃* NativeSporadic.J2) ∨
      (Nonempty ((G ⧸ oddCore G) ⧸ center (G ⧸ oddCore G) ≃* projSL 3 (GaloisField 2 2)) ∧
        IsCyclic (center (G ⧸ oddCore G)) ∧ Nat.card (center (G ⧸ oddCore G)) = 4)

@[expose] def FourL34NotSLFourOdd : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (X : Type) [Group X] [Finite X]
    (ρ : X →* Matrix.SpecialLinearGroup (Fin 4) (ZMod p)) (N : Subgroup X) [N.Normal],
    Odd (Nat.card N) → ρ.ker ≤ N → IsQuasisimple (X ⧸ N) → IsCyclic (center (X ⧸ N)) →
      Nat.card (center (X ⧸ N)) = 4 →
        IsEmpty ((X ⧸ N) ⧸ center (X ⧸ N) ≃* projSL 3 (GaloisField 2 2))

theorem partTwoRankThreeNotQuasisimple_of (hcen : QuasisimpleCensus)
    (hL34 : FourL34NotSLFourOdd) : PartTwoRankThreeNotQuasisimple := by
  intro G _ _ K _ hyp hq
  obtain ⟨p, hp, hp5, ρ, hρ, hdet, -⟩ := exists_rep hyp
  have : Fact p.Prime := ⟨hp⟩
  have hker : ρ.ker ≤ oddCore G := fun y hy => hρ y hy
  let π : G →* (G ⧸ oddCore G) ⧸ center (G ⧸ oddCore G) :=
    (QuotientGroup.mk' (center (G ⧸ oddCore G))).comp (QuotientGroup.mk' (oddCore G))
  have hπ : Function.Surjective π :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hπker : ρ.ker ≤ π.ker := fun y hy => by
    have h1 : QuotientGroup.mk' (oddCore G) y = 1 := (QuotientGroup.eq_one_iff y).mpr (hker hy)
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, h1, map_one]
  rcases hcen G K hyp hq with h | ⟨h, hZ⟩ | h | ⟨h, hcyc, hZ⟩
  · exact h.elim (isEmpty_mulEquiv_m12 ρ π hπ hπker).false
  · exact h.elim (isEmpty_mulEquiv_m22 ρ hdet hker hZ).false
  · exact h.elim (isEmpty_mulEquiv_j2 ρ π hπ hπker).false
  · exact h.elim (hL34 p hp5 G (glToSL ρ hdet) (oddCore G) (CFSG.ABGDGroups.odd_card_oddCore G)
      (by rw [ker_glToSL]; exact hker) hq hcyc hZ).false

theorem rank3II_4_4_of_census (hcen : QuasisimpleCensus) (hL34 : FourL34NotSLFourOdd) :
    Item4_4 :=
  rank3II_4_4_of primeThreeLinear partTwoRankTwo (partTwoRankThreeNotQuasisimple_of hcen hL34)
    partTwoRankThreeEndgame

end CFSG.RankThree.PartTwo.Sec4.Census
