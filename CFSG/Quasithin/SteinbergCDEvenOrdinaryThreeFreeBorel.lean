module

public import CFSG.LieType.Chevalley.GraphFixedHighestRoot

public section

namespace CFSG.Quasithin.SteinbergCD

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise

variable {τ : Tag} {K : Type} [Field K] [CharP K 2]

theorem orderOf_xUnit_one_mul_yUnit_one
    (i : Fin τ.rank) :
    orderOf (xUnit τ K i 1 * yUnit τ K i 1) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set x := xUnit τ K i 1 with hx
  set y := yUnit τ K i 1 with hy
  set n := weylElt τ K i 1 with hn
  have hneg : -(((1 : Kˣ)⁻¹ : Kˣ) : K) = 1 := by
    rw [inv_one, Units.val_one, CharTwo.neg_eq]
  have h1 : x * y * x = n := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, hx, hy, hn, coe_xUnit, coe_yUnit, coe_weylElt, hneg,
      Units.val_one]
  have h2 : y * x * y = n := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, hx, hy, hn, coe_xUnit, coe_yUnit, coe_weylElt_eq_yOp_mul,
      hneg, Units.val_one]
  have hm1 : (-1 : Kˣ) = 1 := Units.ext (by rw [Units.val_neg, Units.val_one, CharTwo.neg_eq])
  have h3 : n * n = 1 := by
    rw [mul_eq_one_iff_eq_inv, hn, weylElt_inv, hm1]
  have hy2 : y * y = 1 := by
    rw [hy, ← pinnedX_neg_single, ← pinnedX_add, one_add_one_eq_two, CharTwo.two_eq_zero,
      pinnedX_zero]
  have hx1 : x ≠ 1 := by
    intro h
    have h' : pinnedX τ K (Pi.single i 1) 1 = pinnedX τ K (Pi.single i 1) 0 := by
      rw [pinnedX_single, pinnedX_single, xUnit_zero]
      exact h
    exact one_ne_zero (pinnedX_injective (τ := τ) (R := K) _ h')
  refine orderOf_eq_prime ?_ fun h => hx1 ?_
  · calc (x * y) ^ 3 = (x * y * x) * (y * x * y) := by
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := by rw [h1, h2, h3]
  · have hxy : x = y := (eq_inv_of_mul_eq_one_left h).trans (inv_eq_of_mul_eq_one_right hy2)
    have hxB : x ∈ borelGroup τ K ⊓ negUnipotent τ K :=
      ⟨Subgroup.mem_sup_right (xUnit_mem_posUnipotent i 1), hxy ▸ yUnit_mem_negUnipotent i 1⟩
    rw [borelGroup_inf_negUnipotent] at hxB
    exact hxB

theorem le_borelGroup_of_posUnipotent_le_of_orderOf_ne_three
    {D : Subgroup (ModGL τ K)}
    (hDC : D ≤ adjointGroup τ K) (hUD : posUnipotent τ K ≤ D) (h3 : ∀ g ∈ D, orderOf g ≠ 3) :
    D ≤ borelGroup τ K := by
  intro g hg
  have hg' : g ∈ ⋃ w, bruhatCell τ K w := by
    rw [← adjointGroup_eq_iUnion_bruhatCell]
    exact hDC hg
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg'
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hw
  have hT := triangular_borel_structure.{0, 0} τ K
  have hbUH : b ∈ (posUnipotent τ K : Set (ModGL τ K)) * (torusGroup τ K : Set (ModGL τ K)) := by
    rw [← hT.2.2.2.2.2.1]
    exact hb
  have hbHU : b' ∈ (torusGroup τ K : Set (ModGL τ K)) * (posUnipotent τ K : Set (ModGL τ K)) := by
    rw [← hT.2.2.2.2.1]
    exact hb'
  obtain ⟨u₁, hu₁, h₁, hh₁, rfl⟩ := Set.mem_mul.1 hbUH
  obtain ⟨h₂, hh₂, u₂, hu₂, rfl⟩ := Set.mem_mul.1 hbHU
  set n := canonicalRep (coxeterSystem τ) K w with hn
  set z := h₁ * n * h₂ with hz
  have hzD : z ∈ D := by
    have h := mul_mem (mul_mem (inv_mem (hUD hu₁)) hg) (inv_mem (hUD hu₂))
    have e : u₁⁻¹ * (u₁ * h₁ * n * (h₂ * u₂)) * u₂⁻¹ = z := by
      rw [hz]
      group
    rwa [e] at h
  by_cases hw1 : w = 1
  · have hn1 : n = 1 := by
      rw [hn, hw1, canonicalRep_one]
    rw [hn1, mul_one]
    exact mul_mem hb hb'
  exfalso
  obtain ⟨i, hi⟩ := (coxeterSystem τ).exists_rightDescent_of_ne_one (inv_ne_one.2 hw1)
  have hneg := (smul_single_mem_negRoots_iff w⁻¹ i).2 hi
  set β : Fin τ.rank → ℤ := -(w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ)) with hβ
  have hβroot : IsRoot τ β := IsRoot.neg (IsRoot.smul (isRoot_single τ i) w⁻¹)
  have hβpos : 0 < height β := by
    rw [hβ, height_neg]
    exact neg_pos.2 hneg.2
  have hwβ : w • β = -Pi.single i 1 := by
    rw [hβ, smul_neg, smul_inv_smul]
  have hyD : yUnit τ K i 1 ∈ D := by
    have hy : yUnit τ K i 1 ∈ rootSubgroup τ K (-Pi.single i 1) := by
      rw [← pinnedX_neg_single]
      exact Subgroup.subset_closure ⟨1, rfl⟩
    have hN₁ := torusGroup_le_normalizer_rootSubgroup (R := K) (isRoot_neg_single τ i)
      (inv_mem hh₁)
    have hy₁ := (Subgroup.mem_normalizer_iff.1 hN₁ _).1 hy
    rw [← hwβ, ← (canonical_weyl_root_transport τ K).2.1 w β hβroot] at hy₁
    obtain ⟨u, hu, hue⟩ := hy₁
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hue
    have hN₂ := torusGroup_le_normalizer_rootSubgroup (R := K) hβroot (inv_mem hh₂)
    have hu' := (Subgroup.mem_normalizer_iff.1 hN₂ _).1 hu
    have huD : h₂⁻¹ * u * h₂⁻¹⁻¹ ∈ D :=
      hUD (Subgroup.mem_iSup_of_mem β (Subgroup.mem_iSup_of_mem ⟨hβroot, hβpos⟩ hu'))
    have e : yUnit τ K i 1 = z * (h₂⁻¹ * u * h₂⁻¹⁻¹) * z⁻¹ := by
      have e' : yUnit τ K i 1 = h₁ * (n * u * n⁻¹) * h₁⁻¹ := by
        rw [hue]
        group
      rw [e', hz]
      group
    rw [e]
    exact mul_mem (mul_mem hzD huD) (inv_mem hzD)
  exact h3 _ (mul_mem (hUD (xUnit_mem_posUnipotent i 1)) hyD) (orderOf_xUnit_one_mul_yUnit_one i)

theorem even_ordinary_three_free_posUnipotent_overgroups_le_borelGroup
    {D : Subgroup (ModGL τ K)}
    (hDC : D ≤ adjointGroup τ K) (hUD : posUnipotent τ K ≤ D) (h3 : ¬ 3 ∣ Nat.card D) :
    D ≤ borelGroup τ K :=
  le_borelGroup_of_posUnipotent_le_of_orderOf_ne_three hDC hUD fun _ hg hg3 =>
    h3 (hg3 ▸ Subgroup.orderOf_dvd_natCard D hg)

end CFSG.Quasithin.SteinbergCD
