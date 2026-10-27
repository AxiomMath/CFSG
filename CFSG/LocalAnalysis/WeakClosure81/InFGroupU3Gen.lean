module

public import CFSG.LocalAnalysis.WeakClosure81.InFGroupU3Setting
public import CFSG.LargeExtraspecial.S8CBFSmall
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderONan
public import CFSG.GroupTheory.OddCentralQuotient

public section

namespace CFSG.LocalAnalysis.WeakClosure81.InFGroupU3

open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase

variable {Q : Type} [Group Q] [Finite Q] {C : Subgroup Q} {n : ℕ}

private theorem conj_map_eq_of_mem_normalizer_image (h : Setting C n)
    {S₀ : Subgroup Q} (hS₀ : IsSylowIn 2 S₀ C) {x : Q} (hxC : x ∈ C)
    (hxN : QuotientGroup.mk' (center ↥C) ⟨x, hxC⟩ ∈
      normalizer (((S₀.subgroupOf C).map (QuotientGroup.mk' (center ↥C))) :
        Set (↥C ⧸ center ↥C))) :
    x ∈ normalizer (S₀ : Set Q) := by
  let Y := ↥C ⧸ center ↥C
  let xC : ↥C := ⟨x, hxC⟩
  let π : ↥C →* Y := QuotientGroup.mk' (center ↥C)
  let S : Subgroup ↥C := S₀.subgroupOf C
  have hS2 : IsPGroup 2 S :=
    hS₀.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hS₀.le).symm
  have hcomp : π.comp (MulAut.conj xC : ↥C →* ↥C) =
      ((MulAut.conj (π xC) : Y →* Y)).comp π := by
    ext y
    simp [π, MulAut.conj_apply, map_mul, map_inv, mul_assoc]
  have hconj : S.map (MulAut.conj xC : ↥C →* ↥C) = S := by
    refine CFSG.GroupTheory.eq_of_map_mk_eq_of_le_center (N := center ↥C) le_rfl
      h.odd_center (hS2.map (MulAut.conj xC : ↥C →* ↥C)) hS2 ?_
    have hnorm := Subgroup.mem_normalizer_iff_map_conj_eq.mp hxN
    calc (S.map (MulAut.conj xC : ↥C →* ↥C)).map π
        = S.map (π.comp (MulAut.conj xC)) := by rw [Subgroup.map_map]
      _ = S.map (((MulAut.conj (π xC) : Y →* Y)).comp π) := by rw [hcomp]
      _ = (S.map π).map (MulAut.conj (π xC) : Y →* Y) := by rw [Subgroup.map_map]
      _ = S.map π := hnorm
  have hcomp2 : ((MulAut.conj x : Q →* Q)).comp C.subtype =
      C.subtype.comp (MulAut.conj xC) := by
    ext y
    simp [xC, MulAut.conj_apply, mul_assoc]
  have hconjQ : S₀.map (MulAut.conj x : Q →* Q) = S₀ := by
    calc S₀.map (MulAut.conj x : Q →* Q)
        = (S.map C.subtype).map (MulAut.conj x : Q →* Q) := by
            rw [Subgroup.map_subgroupOf_eq_of_le hS₀.le]
      _ = S.map (((MulAut.conj x : Q →* Q)).comp C.subtype) := by
            rw [Subgroup.map_map]
      _ = S.map (C.subtype.comp (MulAut.conj xC)) := by rw [hcomp2]
      _ = (S.map (MulAut.conj xC : ↥C →* ↥C)).map C.subtype := by
            rw [Subgroup.map_map]
      _ = S₀ := by rw [hconj, Subgroup.map_subgroupOf_eq_of_le hS₀.le]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hconjQ

private theorem le_of_image_eq_top (h : Setting C n) {X : Subgroup Q} (hXC : X ≤ C)
    (hH : (X.subgroupOf C).map (QuotientGroup.mk' (center ↥C)) = ⊤) : C ≤ X := by
  haveI := h.normal
  refine UCK.Odd.le_of_mul_centerOf C h.quasisimple.1 ?_
  intro y hy
  have hyH : (QuotientGroup.mk' (center ↥C)) ⟨y, hy⟩ ∈
      (X.subgroupOf C).map (QuotientGroup.mk' (center ↥C)) := by
    rw [hH]
    exact Subgroup.mem_top _
  obtain ⟨xC, hxX, hxEq⟩ := Subgroup.mem_map.mp hyH
  obtain ⟨z, hz, hxz⟩ := (QuotientGroup.mk'_eq_mk' (center ↥C)).mp hxEq
  have hzQ : (z : Q) ∈ UCK.Odd.centerOf C :=
    (UCK.Odd.mem_center_iff_mem_centerOf C z).mp hz
  have hxzQ : (xC : Q) * (z : Q) = y := by
    simpa using congrArg Subtype.val hxz
  exact ⟨(xC : Q), ⟨Subgroup.mem_subgroupOf.mp hxX, xC.2⟩, (z : Q), hzQ, hxzQ.symm⟩

theorem Setting.eq_of_sylow_le (h : Setting C n)
    {S₀ X : Subgroup Q} (hS₀ : IsSylowIn 2 S₀ C) (hS₀X : S₀ ≤ X) (hXC : X ≤ C)
    (hX : ¬ X ≤ normalizer (S₀ : Set Q)) : X = C := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Y := ↥C ⧸ center ↥C
  let π : ↥C →* Y := QuotientGroup.mk' (center ↥C)
  let S : Subgroup ↥C := S₀.subgroupOf C
  let U : Sylow 2 Y :=
    Sylow.mapSurjective (f := π) (QuotientGroup.mk'_surjective _) hS₀.toSylow
  have hUcoe : (U : Subgroup Y) = S.map π := by
    rw [Sylow.coe_mapSurjective, IsSylowIn.coe_toSylow]
  have hB : CFSG.Open.fusionIsBenderGroup Y :=
    CFSG.LargeExtraspecial.S8.fusionIsBenderGroup_of_lieModel_psu_three h.isU3
  let X' : Subgroup ↥C := X.subgroupOf C
  let H : Subgroup Y := X'.map π
  have hUH : (U : Subgroup Y) ≤ H := by
    rw [hUcoe]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono C hS₀X)
  rcases CFSG.ComponentClassification.RankTwoBender.le_normalizer_or_eq_top hB U hUH with
    hN | htop
  · exfalso
    rw [hUcoe] at hN
    apply hX
    intro x hx
    have hxC : x ∈ C := hXC hx
    have hxH : π ⟨x, hxC⟩ ∈ H :=
      Subgroup.mem_map.mpr ⟨⟨x, hxC⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    exact conj_map_eq_of_mem_normalizer_image h hS₀ hxC (hN hxH)
  · apply le_antisymm hXC
    apply le_of_image_eq_top h hXC
    simpa [H, X', π] using htop

end CFSG.LocalAnalysis.WeakClosure81.InFGroupU3
