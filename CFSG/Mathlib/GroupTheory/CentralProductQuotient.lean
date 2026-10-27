module

public import Mathlib.GroupTheory.QuotientGroup.Basic

public section

namespace CFSG.GroupTheory

open Subgroup

theorem exists_centerQuotient_equiv_of_central_product
    {H G : Type*} [Group H] [Group G] (ι : H →* G) (hι : Function.Injective ι)
    (hdec : ∀ g : G, ∃ z ∈ center G, ∃ h : H, g = z * ι h) :
    ∃ e : H ⧸ center H ≃* G ⧸ center G,
      ∀ h : H, e (QuotientGroup.mk h) = QuotientGroup.mk (ι h) := by
  let f : H →* G ⧸ center G := (QuotientGroup.mk' (center G)).comp ι
  have hker : f.ker = center H := by
    ext h
    change QuotientGroup.mk (ι h) = 1 ↔ h ∈ center H
    rw [QuotientGroup.eq_one_iff, mem_center_iff, mem_center_iff]
    constructor
    · intro hc k
      apply hι
      simpa only [map_mul] using hc (ι k)
    · intro hc g
      obtain ⟨z, hz, k, rfl⟩ := hdec g
      have hzh := mem_center_iff.mp hz (ι h)
      have hkh : ι k * ι h = ι h * ι k := by rw [← map_mul, hc k, map_mul]
      calc (z * ι k) * ι h = z * (ι k * ι h) := mul_assoc _ _ _
        _ = z * (ι h * ι k) := by rw [hkh]
        _ = (z * ι h) * ι k := (mul_assoc _ _ _).symm
        _ = (ι h * z) * ι k := by rw [hzh]
        _ = ι h * (z * ι k) := mul_assoc _ _ _
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨z, hz, h, rfl⟩ := hdec g
    refine ⟨h, ?_⟩
    change QuotientGroup.mk (ι h) = QuotientGroup.mk (z * ι h)
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff z).2 hz, one_mul]
  let e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hsurj)
  refine ⟨e, ?_⟩
  intro h
  simp only [e, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

theorem equivariant_of_central_product
    {H G P : Type*} [Group H] [Group G] [Group P] (ι : H →* G)
    (hdec : ∀ g : G, ∃ z ∈ center G, ∃ h : H, g = z * ι h)
    (π : G →* P) (hker : center G ≤ π.ker) (α : MulAut G) (β : MulAut P)
    (hact : ∀ h : H, π (α (ι h)) = β (π (ι h))) (g : G) :
    π (α g) = β (π g) := by
  obtain ⟨z, hz, h, rfl⟩ := hdec g
  have hzα : α z ∈ center G := by
    rw [mem_center_iff]
    intro y
    have hc := congrArg α (mem_center_iff.mp hz (α.symm y))
    simpa only [map_mul, MulEquiv.apply_symm_apply] using hc
  have hπz : π z = 1 := hker hz
  have hπαz : π (α z) = 1 := hker hzα
  simp only [map_mul, hπz, hπαz, one_mul, hact]

end CFSG.GroupTheory
