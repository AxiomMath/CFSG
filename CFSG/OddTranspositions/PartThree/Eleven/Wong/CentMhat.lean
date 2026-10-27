module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentFusion

public section

namespace CFSG.OddTranspositions.PartThree.Wong

open Subgroup
open scoped commutatorElement

private theorem mem_zpowers_hM_iff {x : SL5} :
    x ∈ zpowers hM ↔ x = 1 ∨ x = -1 ∨ x = hM ∨ x = -hM := by
  refine ⟨fun hx => (commute_hM_iff x).mp ?_, ?_⟩
  · obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
    exact (Commute.refl hM).zpow_left k
  · rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · rw [← hM_sq]
      exact pow_mem (mem_zpowers _) 2
    · exact mem_zpowers _
    · rw [neg_hM]
      exact inv_mem (mem_zpowers _)

private theorem cM_conj {x : SL5} (hx : x ∈ zpowers hM) : cM * x * cM⁻¹ = x⁻¹ := by
  rcases mem_zpowers_hM_iff.mp hx with rfl | rfl | rfl | rfl <;> decide

namespace SplitData

variable {G : Type} [Group G] (D : SplitData G)

@[expose] def Mh : Subgroup G := closure {D.h1, D.h2, D.u * D.w}

private theorem u_mul_prod (x y : SL5) :
    D.u * (D.i1 x * D.i2 y) = D.i1 y * D.i2 x * D.u := by
  rw [← mul_assoc, D.u_mul_i1, mul_assoc, D.u_mul_i2, ← mul_assoc, ← (D.commute y x).eq]

private theorem w_mul_prod {x y : SL5} (hx : x ∈ zpowers hM) (hy : y ∈ zpowers hM) :
    D.w * (D.i1 x * D.i2 y) = D.i1 x⁻¹ * D.i2 y⁻¹ * D.w := by
  have h := D.conj_prod cM cM x y
  rw [cM_conj hx, cM_conj hy] at h
  exact mul_inv_eq_iff_eq_mul.mp h

private theorem uw_mul_prod {x y : SL5} (hx : x ∈ zpowers hM) (hy : y ∈ zpowers hM) :
    D.u * D.w * (D.i1 x * D.i2 y) = D.i1 y⁻¹ * D.i2 x⁻¹ * (D.u * D.w) := by
  rw [mul_assoc, D.w_mul_prod hx hy, ← mul_assoc, D.u_mul_prod, mul_assoc]

private theorem uw_mul_uw : D.u * D.w * (D.u * D.w) = 1 := by
  simp only [mul_assoc, D.w_mul_u_mul, D.u_mul_u_mul, D.w_mul_w]

private theorem uw_inv : (D.u * D.w)⁻¹ = D.u * D.w := inv_eq_of_mul_eq_one_right D.uw_mul_uw

private theorem prod_uw_mul_prod {x y x' y' : SL5} (hx' : x' ∈ zpowers hM)
    (hy' : y' ∈ zpowers hM) :
    D.i1 x * D.i2 y * (D.u * D.w) * (D.i1 x' * D.i2 y') =
      D.i1 (x * y'⁻¹) * D.i2 (y * x'⁻¹) * (D.u * D.w) := by
  rw [mul_assoc _ (D.u * D.w), D.uw_mul_prod hx' hy', ← mul_assoc, D.prod_mul_prod]

private def InMh (g : G) : Prop :=
  ∃ x ∈ zpowers hM, ∃ y ∈ zpowers hM,
    g = D.i1 x * D.i2 y ∨ g = D.i1 x * D.i2 y * (D.u * D.w)

private theorem mul_InMh {a b : G} (ha : D.InMh a) (hb : D.InMh b) : D.InMh (a * b) := by
  obtain ⟨x, hx, y, hy, rfl | rfl⟩ := ha <;> obtain ⟨x', hx', y', hy', rfl | rfl⟩ := hb
  · exact ⟨x * x', mul_mem hx hx', y * y', mul_mem hy hy', Or.inl (D.prod_mul_prod x y x' y')⟩
  · exact ⟨x * x', mul_mem hx hx', y * y', mul_mem hy hy',
      Or.inr (by rw [← mul_assoc, D.prod_mul_prod])⟩
  · exact ⟨x * y'⁻¹, mul_mem hx (inv_mem hy'), y * x'⁻¹, mul_mem hy (inv_mem hx'),
      Or.inr (D.prod_uw_mul_prod hx' hy')⟩
  · exact ⟨x * y'⁻¹, mul_mem hx (inv_mem hy'), y * x'⁻¹, mul_mem hy (inv_mem hx'),
      Or.inl (by rw [← mul_assoc, D.prod_uw_mul_prod hx' hy', mul_assoc, D.uw_mul_uw, mul_one])⟩

private theorem inv_InMh {a : G} (ha : D.InMh a) : D.InMh a⁻¹ := by
  obtain ⟨x, hx, y, hy, rfl | rfl⟩ := ha
  · exact ⟨x⁻¹, inv_mem hx, y⁻¹, inv_mem hy, Or.inl (D.prod_inv x y)⟩
  · refine ⟨y, hy, x, hx, Or.inr ?_⟩
    rw [mul_inv_rev, D.uw_inv, D.prod_inv, D.uw_mul_prod (inv_mem hx) (inv_mem hy), inv_inv,
      inv_inv]

private theorem i1_mem_zpowers_h1 {x : SL5} (hx : x ∈ zpowers hM) : D.i1 x ∈ zpowers D.h1 := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  exact mem_zpowers_iff.mpr ⟨k, (map_zpow _ _ _).symm⟩

private theorem i2_mem_zpowers_h2 {x : SL5} (hx : x ∈ zpowers hM) : D.i2 x ∈ zpowers D.h2 := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  exact mem_zpowers_iff.mpr ⟨k, (map_zpow _ _ _).symm⟩

private theorem h1_mem_Mh : D.h1 ∈ D.Mh := subset_closure (by simp)

private theorem h2_mem_Mh : D.h2 ∈ D.Mh := subset_closure (by simp)

private theorem uw_mem_Mh : D.u * D.w ∈ D.Mh := subset_closure (by simp)

theorem mem_Mh_iff {g : G} : g ∈ D.Mh ↔ ∃ x ∈ zpowers hM, ∃ y ∈ zpowers hM,
    g = D.i1 x * D.i2 y ∨ g = D.i1 x * D.i2 y * (D.u * D.w) := by
  refine ⟨fun hg => ?_, ?_⟩
  · change g ∈ closure {D.h1, D.h2, D.u * D.w} at hg
    show D.InMh g
    induction hg using Subgroup.closure_induction with
    | mem a ha =>
      rcases ha with rfl | rfl | rfl
      · exact ⟨hM, mem_zpowers _, 1, one_mem _,
          Or.inl (by show D.i1 hM = D.i1 hM * D.i2 1; rw [map_one, mul_one])⟩
      · exact ⟨1, one_mem _, hM, mem_zpowers _,
          Or.inl (by show D.i2 hM = D.i1 1 * D.i2 hM; rw [map_one, one_mul])⟩
      · exact ⟨1, one_mem _, 1, one_mem _,
          Or.inr (by rw [map_one, map_one, mul_one, one_mul])⟩
    | one => exact ⟨1, one_mem _, 1, one_mem _, Or.inl (by rw [map_one, map_one, mul_one])⟩
    | mul a b _ _ ha hb => exact D.mul_InMh ha hb
    | inv a _ ha => exact D.inv_InMh ha
  · rintro ⟨x, hx, y, hy, rfl | rfl⟩
    · exact mul_mem (zpowers_le.mpr D.h1_mem_Mh (D.i1_mem_zpowers_h1 hx))
        (zpowers_le.mpr D.h2_mem_Mh (D.i2_mem_zpowers_h2 hy))
    · exact mul_mem (mul_mem (zpowers_le.mpr D.h1_mem_Mh (D.i1_mem_zpowers_h1 hx))
        (zpowers_le.mpr D.h2_mem_Mh (D.i2_mem_zpowers_h2 hy))) D.uw_mem_Mh

end SplitData

end CFSG.OddTranspositions.PartThree.Wong
