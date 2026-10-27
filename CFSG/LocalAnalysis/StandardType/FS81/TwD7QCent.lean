module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD7PtQuot
public import CFSG.LocalAnalysis.StandardType.FS81.TwD7ClassArg

public noncomputable section

namespace CFSG.StandardType.FrameRoute.FS81

open Subgroup
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace TwD7Q

variable {G : Type} [Group G]

theorem commute_of_mem_zpowers {β z y : G} (hz : z ∈ zpowers β) (hy : y ∈ cen β) :
    z * y = y * z := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hz
  exact ((Commute.zpow_right (mem_cen_iff.mp hy : Commute y β) n).eq).symm

theorem pr_commute_iff {β : G} (g x : ↥(cen β)) :
    pr β x * pr β g = pr β g * pr β x ↔ (x : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) ∈ zpowers β := by
  rw [← map_mul, ← map_mul, pr_eq_pr_iff]
  have hu : (((x * g : ↥(cen β)) : G))⁻¹ * ((g * x : ↥(cen β)) : G) =
      (g : G)⁻¹ * ((x : G)⁻¹ * ((g : G) * x * (g : G)⁻¹)) * g := by
    simp only [Subgroup.coe_mul]
    group
  rw [hu]
  constructor
  · intro h
    have hc := commute_of_mem_zpowers h g.2
    have hv : (x : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) =
        (g : G) * ((g : G)⁻¹ * ((x : G)⁻¹ * ((g : G) * x * (g : G)⁻¹)) * g) * (g : G)⁻¹ := by
      group
    rw [hv, ← hc, mul_inv_cancel_right]
    exact h
  · intro h
    have hc := commute_of_mem_zpowers h g.2
    rw [mul_assoc, hc, inv_mul_cancel_left]
    exact h

private theorem commutatorElement_mul_central {T : Type} [Group T] {a b z w : T}
    (hz : z ∈ center T) (hw : w ∈ center T) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have hz1 : ∀ g : T, g * z = z * g := fun g => mem_center_iff.1 hz g
  have hw1 : ∀ g : T, g * w = w * g := fun g => mem_center_iff.1 hw g
  have hz2 : ∀ g : T, g * z⁻¹ = z⁻¹ * g := fun g => mem_center_iff.1 (inv_mem hz) g
  have hw2 : ∀ g : T, g * w⁻¹ = w⁻¹ * g := fun g => mem_center_iff.1 (inv_mem hw) g
  have hconj : z⁻¹ * w * z = w := by rw [mul_assoc, hz1 w, inv_mul_cancel_left]
  have key : ∀ X : T, w⁻¹ * (z⁻¹ * (w * (z * X))) = X := by
    intro X
    have : w⁻¹ * (z⁻¹ * (w * (z * X))) = w⁻¹ * ((z⁻¹ * w * z) * X) := by simp only [mul_assoc]
    rw [this, hconj, inv_mul_cancel_left]
  simp only [commutatorElement_def, mul_inv_rev, ← mul_assoc]
  simp only [hz1, hw1, hz2, hw2, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left,
    inv_mul_cancel, mul_inv_cancel, mul_one, one_mul]
  exact key _

theorem mem_centralizer_of_pr_mem_centralizer_img {β : G} {M : Subgroup G} (hM : M ≤ cen β)
    (hperf : M ≤ ⁅M, M⁆) {g : ↥(cen β)}
    (hg : pr β g ∈ centralizer (img β M : Set (Q β))) : (g : G) ∈ centralizer (M : Set G) := by
  have hz : ∀ x ∈ M, (x : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) ∈ zpowers β := fun x hx =>
    (pr_commute_iff g ⟨x, hM hx⟩).mp (mem_centralizer_iff.mp hg _ (pr_mem_img hx))
  have he : ∀ x (hx : x ∈ M), g * (⟨x, hM hx⟩ : ↥(cen β)) * g⁻¹ =
      ⟨x, hM hx⟩ * ⟨_, zpowers_le_cen β (hz x hx)⟩ := by
    intro x hx
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hc : ∀ x (hx : x ∈ M), (⟨_, zpowers_le_cen β (hz x hx)⟩ : ↥(cen β)) ∈
      center ↥(cen β) := fun x hx => zb_le_center β (mem_subgroupOf.mpr (hz x hx))
  have hle : ⁅M, M⁆ ≤ centralizer ({(g : G)} : Set G) := by
    refine commutator_le.mpr fun x₁ h₁ x₂ h₂ => ?_
    rw [mem_centralizer_singleton_iff]
    have hmap := map_commutatorElement (MulAut.conj g) (⟨x₁, hM h₁⟩ : ↥(cen β)) ⟨x₂, hM h₂⟩
    simp only [MulAut.conj_apply] at hmap
    rw [he x₁ h₁, he x₂ h₂, commutatorElement_mul_central (hc x₁ h₁) (hc x₂ h₂)] at hmap
    have h := congrArg Subtype.val hmap
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk] at h
    simp only [commutatorElement_def]
    calc x₁ * x₂ * x₁⁻¹ * x₂⁻¹ * (g : G)
        = (g : G) * (x₁ * x₂ * x₁⁻¹ * x₂⁻¹) * (g : G)⁻¹ * g := by rw [h]
      _ = (g : G) * (x₁ * x₂ * x₁⁻¹ * x₂⁻¹) := by group
  rw [mem_centralizer_iff]
  intro x hx
  exact mem_centralizer_singleton_iff.mp (hle (hperf hx))

end TwD7Q

namespace Basis3

open TwD7Q

variable {G : Type} [Group G] [Finite G]

theorem pr_mem_centralizer_twD7Quot_b_zero_iff {B : Basis3 G 8} (hrec : RecOutTwD7 B (B.b 0))
    (g : ↥(cen (B.b 0 * B.b 1))) :
    pr _ g ∈ centralizer ({B.twD7Quot.b 0} : Set (Q (B.b 0 * B.b 1))) ↔
      (g : G) ∈ centralizer ({B.b 0} : Set G) := by
  rw [← B.pr_b_zero_twD7Quot, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 := (pr_commute_iff g ⟨B.b 0, B.b_mem_cen_twD7 0⟩).mp h.symm
    have h2 := conj_b_zero_eq_of_mem_zpowers_twD7 hrec (mem_cen_iff.mp g.2) h1
    calc (g : G) * B.b 0 = (g : G) * B.b 0 * (g : G)⁻¹ * g := by group
      _ = B.b 0 * g := by rw [h2]
  · intro h
    rw [← map_mul, ← map_mul]
    exact congrArg (pr _) (Subtype.ext h)

theorem pr_mem_centralizer_twD7Quot_span_iff {B : Basis3 G 8} (hrec : RecOutTwD7 B (B.b 0))
    (g : ↥(cen (B.b 0 * B.b 1))) :
    pr _ g ∈ centralizer (B.twD7Quot.span : Set (Q (B.b 0 * B.b 1))) ↔
      (g : G) ∈ centralizer (B.span : Set G) := by
  have hspan : B.span ≤ cen (B.b 0 * B.b 1) := by
    intro x hx
    obtain ⟨v, rfl⟩ := B.exists_vec_eq hx
    exact B.vec_mem_cen_twD7 v
  rw [B.twD7Quot_span]
  constructor
  · intro h
    refine mem_centralizer_span_of_conj_mem_zpowers_twD7 hrec (mem_cen_iff.mp g.2) ?_
    intro x hx
    exact (pr_commute_iff g ⟨x, hspan hx⟩).mp
      (mem_centralizer_iff.mp h _ (pr_mem_img (x := ⟨x, hspan hx⟩) hx))
  · intro h
    rw [mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg (pr _) (Subtype.ext (mem_centralizer_iff.mp h _ (mem_subgroupOf.mp hx)))

end Basis3

end CFSG.StandardType.FrameRoute.FS81
