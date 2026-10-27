module

public import CFSG.Quasithin.H13.NQCatOuter
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Candidates
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M12
public import CFSG.Sporadic.Schreier.M22
public import CFSG.Sporadic.Schreier.M23
public import CFSG.Sporadic.Schreier.M24
public import CFSG.Sporadic.Schreier.J1Outer
public import CFSG.Sporadic.Schreier.PairJ2Pairs
public import CFSG.Sporadic.Schreier.PairHePairs
public import CFSG.Sporadic.Schreier.RuAutInner
public import CFSG.Sporadic.SmallOddCore.HSAut

public section

namespace CFSG.Quasithin.H13.NQCat

open CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)

theorem card_outer_sqtkSporadic_le_four
    {s : TauCeti.SporadicName}
    (hs : s ∈ SectionRank.sqtkSporadicNames) (hJ4 : s ≠ .J4) :
    Nat.card (Outer (NativeSporadic.Carrier s)) ≤ 4 := by
  simp only [SectionRank.sqtkSporadicNames, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Sporadic.Schreier.at_m11_schreier.1.trans (by norm_num)
  · exact Sporadic.Schreier.at_m12_schreier.1
  · exact Sporadic.Schreier.at_m22_schreier.1
  · exact Sporadic.Schreier.at_m23_schreier.1.trans (by norm_num)
  · exact Sporadic.Schreier.at_m24_schreier.1
  · exact Sporadic.Schreier.at_j1_schreier.1.le.trans (by norm_num)
  · exact Sporadic.Schreier.AT_J2_Schreier.1.trans (by norm_num)
  · exact absurd rfl hJ4
  · have h : Nat.card (Outer NativeSporadic.HS) ≤ 2 :=
      Sporadic.Schreier.outer_card_le_of_equiv Sporadic.SmallOddCore.hs_outer_card_le
        Sporadic.Schreier.hsPermEquiv
    exact h.trans (by norm_num)
  · exact Sporadic.Schreier.AT_He_Schreier.1.trans (by norm_num)
  · have h : Nat.card (Outer NativeSporadic.Ru) ≤ 1 :=
      Sporadic.Schreier.outer_card_le_of_equiv
        Sporadic.RuSchreier.CTUC_Ru_full_inner_automorphisms_and_second_centralizer.2.2.1.le
        Sporadic.RuSchreier.ruEquivP
    exact h.trans (by norm_num)

theorem sqt_sporadic_perfect_cover_outer_J4_alternative
    (J : Type) [Group J] [Finite J]
    [Group.IsPerfect J] (hS1 : Nontrivial (J ⧸ Subgroup.center J))
    (hSQT : CFSG.IsStronglyQuasithin (J ⧸ Subgroup.center J))
    (hrep : NativeSporadic.SporadicRep (J ⧸ Subgroup.center J)) :
    Nonempty (J ⧸ Subgroup.center J ≃* NativeSporadic.J4) ∨
      (IsMulCommutative (Outer J) ∧ Nat.card (Outer J) ≤ 4 ∧
        ∀ ℓ : ℕ, ℓ.Prime → 5 ≤ ℓ →
          (∀ P : Sylow ℓ (Outer J), (P : Subgroup (Outer J)) = ⊥) ∧
            CFSG.pRank ℓ (Outer J) = 0) := by
  have := hS1
  obtain ⟨s, hs, ⟨e⟩⟩ :=
    QuasithinUnique.Setup.X1.unique_SQT_sporadic_eleven_candidate_restriction hSQT hrep
  by_cases hJ4 : s = .J4
  · subst hJ4
    exact Or.inl ⟨e⟩
  have : Finite (MulAut J) := Finite.of_injective _ (DFunLike.coe_injective (F := MulAut J))
  have hle : Nat.card (Outer J) ≤ 4 :=
    (card_outer_le_of_perfect J e).trans (card_outer_sqtkSporadic_le_four hs hJ4)
  exact Or.inr ⟨isMulCommutative_of_card_le_four hle, hle, outer_large_prime_of_card_le_four hle⟩

end CFSG.Quasithin.H13.NQCat
