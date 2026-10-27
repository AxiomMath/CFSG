module

public import CFSG.LocalAnalysis.StandardType.GGB36JExcE6Hard
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Three
public import CFSG.LocalAnalysis.StandardType.GGTableBRank

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggE6CoverThreeLocalRank_holds
    : GGE6CoverThreeLocalRank := by
  intro X _ _ lab _ htag h3 hlab hperf hZ
  have hmain := largeEvenLabelAll_torusLift_E6_three htag h3
    (fun R _ _ _ => Nonempty (X ⧸ Subgroup.center X ≃* R)) hlab
  obtain ⟨R, hRgrp, I, F, ⟨θ⟩, hlift⟩ := largeEvenRawDatum_exists hmain
  have := Fact.mk Nat.prime_three
  obtain ⟨z', hz'⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center X) 3 hZ
  have hz1 : (z' : X) ≠ 1 := by
    intro h
    have h1 : z' = 1 := Subtype.ext h
    rw [h1, orderOf_one] at hz'
    exact absurd hz' (by norm_num)
  have hzp : (z' : X) ^ 3 = 1 := by
    have : z' ^ 3 = 1 := by rw [← hz']; exact pow_orderOf_eq_one z'
    exact congrArg Subtype.val this
  have hLx : (⊤ : Subgroup X) ≤ Subgroup.centralizer ({(z' : X)} : Set X) := fun g _ =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp z'.2 g)
  have hL : commutator ↥(⊤ : Subgroup X) = ⊤ := by
    let e : ↥(⊤ : Subgroup X) →* X := (Subgroup.topEquiv : ↥(⊤ : Subgroup X) ≃* X).toMonoidHom
    have he : Function.Injective e := (Subgroup.topEquiv : ↥(⊤ : Subgroup X) ≃* X).injective
    have hs : Function.Surjective e := (Subgroup.topEquiv : ↥(⊤ : Subgroup X) ≃* X).surjective
    apply Subgroup.map_injective he
    rw [commutator, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ hs]
    exact hperf
  let e : ↥(⊤ : Subgroup X) ≃* X := Subgroup.topEquiv
  have hc : (Subgroup.center ↥(⊤ : Subgroup X)).map e.toMonoidHom = Subgroup.center X := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : y ∈ Subgroup.center ↥(⊤ : Subgroup X) := hy
      rw [Subgroup.mem_center_iff] at hy'
      show (y : X) ∈ Subgroup.center X
      rw [Subgroup.mem_center_iff]
      intro g
      exact congrArg Subtype.val (hy' ⟨g, Subgroup.mem_top g⟩)
    · intro hx
      refine ⟨⟨x, Subgroup.mem_top x⟩, ?_, rfl⟩
      show (⟨x, Subgroup.mem_top x⟩ : ↥(⊤ : Subgroup X)) ∈ Subgroup.center ↥(⊤ : Subgroup X)
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext ((Subgroup.mem_center_iff.mp hx) g)
  let θ' : ↥(⊤ : Subgroup X) ⧸ Subgroup.center ↥(⊤ : Subgroup X) ≃* R :=
    (QuotientGroup.congr (Subgroup.center ↥(⊤ : Subgroup X)) (Subgroup.center X) e hc).trans θ
  have h6 := succ_le_twoLocalRank_of_torusLift Nat.prime_three hLx hzp hz1 hL θ' hlift
  simpa using h6

end CFSG.StandardType

end
