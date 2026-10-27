module

public import CFSG.RankThree.PartOne.KP.Assembly

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint.NativeSporadic (Carrier)

@[expose] def J4CoprimeAutomorphismSubgroupsTrivial : Prop :=
  ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T], (∃ a b : T, a * b ≠ b * a) →
    Nonempty (T ≃* Carrier .J4) →
    ∀ A : Subgroup (MulAut T), Nat.Coprime (Nat.card A) (Nat.card T) → A = ⊥

theorem j4_coprime_normalized_component_centralization_of_automorphisms
    (h : J4CoprimeAutomorphismSubgroupsTrivial) : J4CoprimeNormalizedComponentCentralization := by
  intro G _ _ p hp hp3 E hE hEc t ht ht1 L hL hpT hJ4 hEL hXL
  have : Fact p.Prime := ⟨hp⟩
  have := hE
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hL.1.2.1
  have : Group.IsPerfect L := hL.1.1
  have hrange : IsPGroup p ((Finkelstein1977.automizer L).comp (inclusion hEL)).range :=
    (IsElementaryAbelian.isPGroup p E).of_surjective _ (MonoidHom.rangeRestrict_surjective _)
  obtain ⟨k, hk⟩ := hrange.exists_card_eq
  have hcop : Nat.Coprime
      (Nat.card ((Finkelstein1977.automizer L).comp (inclusion hEL)).range)
      (Nat.card (L ⧸ Subgroup.center L)) := by
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hpT)
  have hbot := h (L ⧸ Subgroup.center L) hL.1.2.2 hJ4 _ hcop
  have hEC : E ≤ centralizer (L : Set G) := le_centralizer_of_range_eq_bot hEL hbot
  refine ⟨hEC, componentLocalCoreCentralizes_of_le_card hp (by omega) hE hEc ht ht1 hL hXL ?_⟩
  rw [inf_eq_left.mpr hEC, hEc]
  exact Nat.le_self_pow (by norm_num) p

end CFSG.RankThree.PartOne
