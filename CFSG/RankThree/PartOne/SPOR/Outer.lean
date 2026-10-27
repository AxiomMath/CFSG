module

import CFSG.Sporadic.SmallOddCore.HSAut
import CFSG.Sporadic.Schreier.Co1OddInner
import CFSG.Sporadic.Co2Schreier.FullAut
import CFSG.Sporadic.HNSchreier.FullAut
import CFSG.RankThree.PartOne.SPOR.OuterLy
import CFSG.Sporadic.ThSchreier.ThSchreierCase
public import CFSG.Sporadic.Schreier.PairHSFaithful
public import CFSG.Sporadic.Schreier.PairOuter
public import CFSG.Sporadic.Th.Setup

public section

open CFSG CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

namespace CFSG.RankThree.PartOne.SPOR

theorem card_outer_eq_one_of_allInner {K : Type*} [Group K]
    (h : ∀ α : MulAut K, ∃ g : K, α = MulAut.conj g) : Nat.card (Outer K) = 1 := by
  have hsub : Subsingleton (Outer K) := by
    refine ⟨fun p q => ?_⟩
    induction p using QuotientGroup.induction_on with
    | H α =>
      induction q using QuotientGroup.induction_on with
      | H β =>
        rw [QuotientGroup.eq]
        obtain ⟨g, hg⟩ := h (α⁻¹ * β)
        exact ⟨g, hg.symm⟩
  exact Nat.card_eq_one_iff_unique.2 ⟨hsub, inferInstance⟩

theorem isSolvable_of_card_eq_one_or_two {K : Type*} [Group K]
    (h : Nat.card K = 1 ∨ Nat.card K = 2) : Group.IsSolvable K := by
  have hpos : Nat.card K ≠ 0 := by omega
  have : Finite K := Nat.finite_of_card_ne_zero hpos
  rcases h with h | h
  · have : Subsingleton K := (Nat.card_eq_one_iff_unique.1 h).1
    exact inferInstance
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : IsCyclic K := isCyclic_of_prime_card h
    exact Group.isSolvable_of_comm fun a b => (IsCyclic.commGroup (α := K)).mul_comm a b

theorem card_outer_HS_le_two :
    Nat.card (Outer (NativeSporadic.Carrier .HS)) ≤ 2 :=
  CFSG.Sporadic.Schreier.outer_card_le_of_equiv CFSG.Sporadic.SmallOddCore.hs_outer_card_le
    CFSG.Sporadic.Schreier.hsPermEquiv

theorem allInner_Co1 :
    ∀ α : MulAut (NativeSporadic.Carrier .Co1), ∃ g : NativeSporadic.Carrier .Co1,
      α = MulAut.conj g :=
  Sporadic.Co1Schreier.full_automorphisms_inner_of_inputs
      Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner

theorem card_outer_Co1 :
    Nat.card (Outer (NativeSporadic.Carrier .Co1)) = 1 :=
  card_outer_eq_one_of_allInner allInner_Co1

theorem allInner_Co2 :
    ∀ α : MulAut (NativeSporadic.Carrier .Co2), ∃ g : NativeSporadic.Carrier .Co2,
      α = MulAut.conj g := by
  have h := CFSG.Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner_model
    (NativeSporadic.Carrier .Co2) (MulEquiv.refl _)
  exact h

theorem card_outer_Co2 :
    Nat.card (Outer (NativeSporadic.Carrier .Co2)) = 1 :=
  card_outer_eq_one_of_allInner allInner_Co2

theorem card_outer_HN :
    Nat.card (Outer (NativeSporadic.Carrier .HN)) = 2 :=
  CFSG.Sporadic.HNSchreier.card_outer_HN

theorem card_outer_Ly :
    Nat.card (Outer (NativeSporadic.Carrier .Ly)) = 1 ∨
      Nat.card (Outer (NativeSporadic.Carrier .Ly)) = 2 := by
  have e : NativeSporadic.Carrier .Ly ≃* NativeSporadic.Ly := MulEquiv.refl _
  exact (outer_order_divides_two' (T := NativeSporadic.Carrier .Ly) ⟨e⟩).2

theorem card_outer_Th_native :
    Nat.card (Outer NativeSporadic.Th) = 1 := by
  have hTh : @inner NativeSporadic.Th Units.instGroup = ⊤ :=
    @CFSG.Sporadic.ThSchreier.inner_eq_top_of_equiv NativeSporadic.Th CFSG.Sporadic.Th.J
      Units.instGroup (Subgroup.toGroup CFSG.Sporadic.Th.J) CFSG.Sporadic.Th.thEquivJ
      CFSG.Sporadic.ThSchreier.ctuc_Th_full_automorphism_group.{0}.1
  have h := @CFSG.Sporadic.ThSchreier.subsingleton_outer_of_inner NativeSporadic.Th
    Units.instGroup hTh
  exact Nat.card_eq_one_iff_unique.2 ⟨h, inferInstance⟩

theorem card_outer_Th :
    Nat.card (Outer (NativeSporadic.Carrier .Th)) = 1 :=
  card_outer_Th_native

end CFSG.RankThree.PartOne.SPOR
