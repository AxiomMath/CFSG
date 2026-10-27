module

public import CFSG.LocalAnalysis.StandardType.FS81.S7E7Incl
import CFSG.LocalAnalysis.StandardType.FS81.S7E7InclRange

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.SeitzReduction CFSG.QuasithinUnique

local notation "GF₂" => GaloisField 2 1
local notation "sθ" => rootThree Tag.E8 (GaloisField 2 1) (highRoot Tag.E8)

private theorem sl2_two_pow_three_eq_one_or_inv :
    ∀ A : SL2 (ZMod 2), A ^ 3 = 1 → A ≠ 1 →
      A = uSL 1 * vSL 1 ∨ A = (uSL 1 * vSL 1)⁻¹ := by
  decide

private theorem sl2_two_exists_conj_uSL :
    ∀ A : SL2 (ZMod 2), A * A = 1 → A ≠ 1 →
      ∃ B : SL2 (ZMod 2), B * uSL 1 * B⁻¹ = A := by
  decide

section E7Model


private theorem e7Incl_rootThree_highRoot :
    e7Incl (rootThree .E7 (ZMod 2) (highRoot .E7)) =
      rootThree .E8 GF₂ (E8Pilot.e7Embed (highRoot .E7)) := by
  have hθ : IsRoot .E7 (highRoot .E7) := isRoot_highRoot .E7
  have h1 : e7Incl (EPilot.pinnedElt .E7 (highRoot .E7) (1 : ZMod 2)) =
      EPilot.pinnedElt .E8 (E8Pilot.e7Embed (highRoot .E7)) (1 : GF₂) := by
    simpa using e7Incl_pinnedElt hθ (1 : ZMod 2)
  have h2 : e7Incl (EPilot.pinnedElt .E7 (-(highRoot .E7)) (1 : ZMod 2)) =
      EPilot.pinnedElt .E8 (-(E8Pilot.e7Embed (highRoot .E7))) (1 : GF₂) := by
    have h := e7Incl_pinnedElt (IsRoot.neg hθ) (1 : ZMod 2)
    rw [E8Pilot.e7Embed_neg] at h
    simpa using h
  simp only [rootThree, map_mul, h1, h2]

theorem exists_mem_highRootSL2_orderOf_three :
    ∃ r : ↥(adjointGroup .E7 (ZMod 2)),
      (r : ModGL .E7 (ZMod 2)) ∈ EPilot.highRootSL2 .E7 (ZMod 2) ∧ orderOf r = 3 := by
  refine ⟨rootThree .E7 (ZMod 2) (highRoot .E7),
    ?_, orderOf_rootThree (isRoot_highRoot .E7)⟩
  rw [coe_rootThree (isRoot_highRoot .E7)]
  exact E6Pilot.rootSL2_highRoot_mem_highRootSL2 (uSL 1 * vSL 1)

theorem exists_conj_rootThree_e7Incl (r : ↥(adjointGroup .E7 (ZMod 2)))
    (hr : (r : ModGL .E7 (ZMod 2)) ∈ EPilot.highRootSL2 .E7 (ZMod 2)) (hr3 : orderOf r = 3) :
    ∃ m : ↥(adjointGroup .E8 GF₂), m * e7Incl r * m⁻¹ = sθ := by
  have hr' : (r : ModGL .E7 (ZMod 2)) ∈
      (rootSL2 .E7 (ZMod 2) (highRoot .E7)).range := by
    rw [E6Pilot.range_rootSL2_highRoot]
    exact hr
  obtain ⟨A, hA⟩ := hr'
  have hAo : orderOf A = 3 := by
    rw [← orderOf_injective (rootSL2 .E7 (ZMod 2) (highRoot .E7))
      (E6Pilot.rootSL2_highRoot_injective (K := ZMod 2)) A, hA, Subgroup.orderOf_coe, hr3]
  have hA3 : A ^ 3 = 1 := by
    simpa [hAo] using pow_orderOf_eq_one A
  have hA1 : A ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hAo
    exact absurd hAo (by decide)
  obtain ⟨g, hg⟩ := exists_conj_rootThree_eq (K := GaloisField 2 1) (Or.inr (Or.inr rfl))
    (E8Pilot.isRoot_e7Embed (isRoot_highRoot .E7)) (isRoot_highRoot .E8)
  rcases sl2_two_pow_three_eq_one_or_inv A hA3 hA1 with hAeq | hAeq
  · refine ⟨g, ?_⟩
    have hr_eq : r = rootThree .E7 (ZMod 2) (highRoot .E7) := by
      apply Subtype.ext
      rw [← hA, hAeq, ← coe_rootThree (isRoot_highRoot .E7)]
    rw [hr_eq, e7Incl_rootThree_highRoot]
    exact hg
  · refine ⟨EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂) * g, ?_⟩
    have hr_eq : r = (rootThree .E7 (ZMod 2) (highRoot .E7))⁻¹ := by
      apply Subtype.ext
      rw [← hA, hAeq, map_inv, ← coe_rootThree (isRoot_highRoot .E7)]
      rfl
    have hginv : g * (rootThree .E8 GF₂ (E8Pilot.e7Embed (highRoot .E7)))⁻¹ * g⁻¹ =
        sθ⁻¹ := by
      rw [← hg]
      group
    have hxinv : EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂) * sθ⁻¹ *
        (EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂))⁻¹ = sθ := by
      have h := pinnedElt_mul_rootThree_mul_inv (K := GaloisField 2 1) (isRoot_highRoot .E8)
      have h' : (EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂) * sθ *
          (EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂))⁻¹)⁻¹ =
          EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂) * sθ⁻¹ *
            (EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂))⁻¹ := by group
      rw [← h', h, inv_inv]
    rw [hr_eq, map_inv, e7Incl_rootThree_highRoot]
    calc (EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂) * g) *
          (rootThree .E8 GF₂ (E8Pilot.e7Embed (highRoot .E7)))⁻¹ *
          (EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂) * g)⁻¹
        = EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂) *
            (g * (rootThree .E8 GF₂ (E8Pilot.e7Embed (highRoot .E7)))⁻¹ * g⁻¹) *
            (EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂))⁻¹ := by group
      _ = EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂) * sθ⁻¹ *
            (EPilot.pinnedElt .E8 (highRoot .E8) (1 : GF₂))⁻¹ := by rw [hginv]
      _ = sθ := hxinv

theorem exists_conj_pinnedElt_of_mem_highRootSL2 (s : ↥(adjointGroup .E7 (ZMod 2)))
    (hs : (s : ModGL .E7 (ZMod 2)) ∈ EPilot.highRootSL2 .E7 (ZMod 2)) (hs2 : orderOf s = 2) :
    ∃ h : ↥(adjointGroup .E7 (ZMod 2)),
      (h : ModGL .E7 (ZMod 2)) ∈ EPilot.highRootSL2 .E7 (ZMod 2) ∧
        h * EPilot.pinnedElt .E7 (highRoot .E7) (1 : ZMod 2) * h⁻¹ = s := by
  have hs' : (s : ModGL .E7 (ZMod 2)) ∈
      (rootSL2 .E7 (ZMod 2) (highRoot .E7)).range := by
    rw [E6Pilot.range_rootSL2_highRoot]
    exact hs
  obtain ⟨A, hA⟩ := hs'
  have hAo : orderOf A = 2 := by
    rw [← orderOf_injective (rootSL2 .E7 (ZMod 2) (highRoot .E7))
      (E6Pilot.rootSL2_highRoot_injective (K := ZMod 2)) A, hA, Subgroup.orderOf_coe, hs2]
  have hA2 : A * A = 1 := by
    simpa [hAo, pow_two] using pow_orderOf_eq_one A
  have hA1 : A ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hAo
    exact absurd hAo (by decide)
  obtain ⟨B, hB⟩ := sl2_two_exists_conj_uSL A hA2 hA1
  refine ⟨⟨rootSL2 .E7 (ZMod 2) (highRoot .E7) B,
    E6Pilot.rootSL2_highRoot_mem_adjointGroup B⟩, ?_, ?_⟩
  · exact E6Pilot.rootSL2_highRoot_mem_highRootSL2 B
  · apply Subtype.ext
    change rootSL2 .E7 (ZMod 2) (highRoot .E7) B * pinnedX .E7 (ZMod 2) (highRoot .E7) 1 *
        (rootSL2 .E7 (ZMod 2) (highRoot .E7) B)⁻¹ = (s : ModGL .E7 (ZMod 2))
    rw [← CFSG.LieType.Chevalley.E6GraphInvolution.rootSL2_uSL_of_two
      (by decide : (2 : ZMod 2) = 0) (highRoot .E7) 1]
    rw [← map_mul, ← map_inv, ← map_mul, hB, hA]

end E7Model

end CFSG.StandardType.FrameRoute.FS81

end
