module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925Pure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.OddIdx

open Subgroup

@[expose] def OddIdxNone (G : Type) [Group G] : Prop :=
  ∀ N Y D : Subgroup G, N ≠ ⊤ → Odd N.index → Nat.card D = 3 → D ≤ Y → Y ≤ N →
    normalizer (D : Set G) ≤ N → IsPerfA5Cover ↥Y →
    CFSG.KCore.KGroupNonab (DvdOrThreeFree 51840) ↥N → False

theorem oddIdxProp_of_none {G : Type} [Group G] (h : OddIdxNone G) : OddIdxProp G :=
  fun N Y D hN hodd hD hDY hYN hnorm hY hNK =>
    (h N Y D hN hodd hD hDY hYN hnorm hY hNK).elim

theorem oddIdxNone_of_mulEquiv {K G : Type} [Group K] [Group G] (e : K ≃* G)
    (h : OddIdxNone G) : OddIdxNone K := by
  intro N Y D hN hodd hD hDY hYN hnorm hY hNK
  refine h (N.map e.toMonoidHom) (Y.map e.toMonoidHom) (D.map e.toMonoidHom)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro htop
    apply hN
    have hc := Subgroup.comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective N
    rw [htop, Subgroup.comap_top] at hc
    exact hc.symm
  · rw [Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective N]
    exact hodd
  · rw [Subgroup.card_map_of_injective e.injective]
    exact hD
  · exact Subgroup.map_mono hDY
  · exact Subgroup.map_mono hYN
  · calc normalizer ((D.map e.toMonoidHom : Subgroup G) : Set G)
        = (normalizer (D : Set K)).map e.toMonoidHom :=
          (Subgroup.map_equiv_normalizer_eq D e).symm
      _ ≤ N.map e.toMonoidHom := Subgroup.map_mono hnorm
  · exact hY.of_mulEquiv (Y.equivMapOfInjective e.toMonoidHom e.injective)
  · exact CFSG.KCore.KGroupNonab.of_mulEquiv (isoInvariant_dvdOrThreeFree 51840) hNK
      (N.equivMapOfInjective e.toMonoidHom e.injective).symm

theorem oddIdx_not_isSolvable {G : Type} [Group G] [Finite G] {N Y : Subgroup G} (hYN : Y ≤ N)
    (hY : IsPerfA5Cover ↥Y) : ¬ Group.IsSolvable ↥N := by
  intro hsol
  haveI : Group.IsSolvable ↥N := hsol
  have hYsolv : Group.IsSolvable ↥Y :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hYN)
      (Subgroup.inclusion_injective hYN)
  haveI : Group.IsPerfect ↥Y := Group.isPerfect_def.mpr hY.1
  obtain ⟨D0, hD0⟩ := hY.exists_card_three
  haveI : Nontrivial ↥D0 := by
    rw [← Finite.one_lt_card_iff_nontrivial, hD0]
    norm_num
  obtain ⟨d, hd⟩ := exists_ne (1 : ↥D0)
  haveI : Nontrivial ↥Y := ⟨⟨d.1, 1, fun h => hd (Subtype.ext h)⟩⟩
  exact (Group.IsPerfect.not_isSolvable ↥Y) hYsolv

theorem oddIdx_five_dvd_card {Y : Type} [Group Y] [Finite Y] (hY : IsPerfA5Cover Y) :
    5 ∣ Nat.card Y := by
  obtain ⟨-, Z, hZn, hZ2, ⟨e⟩⟩ := hY
  haveI := hZn
  have hcard : Nat.card Y = Nat.card (Y ⧸ Z) * Nat.card Z :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup Z
  have h60 : Nat.card (Y ⧸ Z) = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  rw [hcard, h60]
  exact ⟨12 * Nat.card Z, by ring⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.OddIdx
