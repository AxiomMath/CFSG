module

public import CFSG.Quasithin.H13.NQCatQuasisimpleJ4
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.QuasithinUnique.Vol2Native CFSG.ComponentClassification.OuterAutomorphisms

theorem mem_sup_centralizer_of_conjNormal_inner {A : Type*} [Group A] {L : Subgroup A}
    [L.Normal] {y : A} (h : MulAut.conjNormal (H := L) y ∈ inner ↥L) :
    y ∈ L ⊔ Subgroup.centralizer (L : Set A) := by
  obtain ⟨l, hl⟩ := h
  have key : ∀ z : L, y * (z : A) * y⁻¹ = (l : A) * z * (l : A)⁻¹ := by
    intro z
    have h1 := congrArg (fun φ : MulAut L => ((φ z : L) : A)) hl
    simpa [MulAut.conj_apply, MulAut.conjNormal_apply] using h1.symm
  have hc : (l : A)⁻¹ * y ∈ Subgroup.centralizer (L : Set A) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have h2 := key ⟨z, hz⟩
    calc z * ((l : A)⁻¹ * y) = (l : A)⁻¹ * ((l : A) * z * (l : A)⁻¹) * y := by group
      _ = (l : A)⁻¹ * (y * z * y⁻¹) * y := by rw [h2]
      _ = (l : A)⁻¹ * y * z := by group
  have h3 : y = (l : A) * ((l : A)⁻¹ * y) := by group
  rw [h3]
  exact Subgroup.mul_mem_sup l.2 hc

@[expose] noncomputable def toOuter {A : Type*} [Group A] (L : Subgroup A) [L.Normal]
    (U : Subgroup A) : U →* Outer ↥L :=
  (QuotientGroup.mk' (inner ↥L)).comp ((MulAut.conjNormal (H := L)).comp U.subtype)

theorem exists_zpowers_sup_of_cyclic_range {A : Type*} [Group A] (L : Subgroup A) [L.Normal]
    (U : Subgroup A) (hcyc : IsCyclic (toOuter L U).range) :
    ∃ u ∈ U, U ≤ Subgroup.zpowers u ⊔ (L ⊔ Subgroup.centralizer (L : Set A)) := by
  obtain ⟨g, hg⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top (toOuter L U).range).mp hcyc
  have hgr : g ∈ (toOuter L U).range := hg ▸ Subgroup.mem_zpowers g
  obtain ⟨u, hu⟩ := hgr
  refine ⟨(u : A), u.2, fun x hx => ?_⟩
  have hxr : toOuter L U ⟨x, hx⟩ ∈ Subgroup.zpowers g := hg ▸ ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxr
  have h1 : toOuter L U (⟨x, hx⟩ * u ^ (-k)) = 1 := by
    rw [map_mul, map_zpow, hu, ← hk, zpow_neg, mul_inv_cancel]
  have h2 : ((⟨x, hx⟩ * u ^ (-k) : U) : A) ∈ L ⊔ Subgroup.centralizer (L : Set A) :=
    mem_sup_centralizer_of_conjNormal_inner ((QuotientGroup.eq_one_iff _).mp h1)
  have h3 : x = ((⟨x, hx⟩ * u ^ (-k) : U) : A) * (u : A) ^ k := by
    simp [zpow_neg]
  rw [sup_comm, h3]
  exact Subgroup.mul_mem_sup h2 (Subgroup.zpow_mem_zpowers _ _)

theorem facts134Odd_outCyclic
    :
    ∀ (A : Type) [Group A] [Finite A] (L U : Subgroup A) (p : ℕ), p.Prime → 5 ≤ p →
      SQTKHypCat A → L.Normal → CFSG.IsComponent L → IsPGroup p U →
      ∃ u ∈ U, U ≤ Subgroup.zpowers u ⊔ (L ⊔ Subgroup.centralizer (L : Set A)) := by
  intro A _ _ L U p hp hp5 hS hLn hL hU
  have := hLn
  have : Finite (MulAut ↥L) := Finite.of_injective _ (DFunLike.coe_injective (F := MulAut ↥L))
  have hsqtk : CFSG.SectionRank.IsSQTKCat ↥L :=
    ⟨CFSG.SectionRank.IsStronglyQuasithin.subgroup hS.sqt L,
      CFSG.SectionRank.IsKGroupCat.subgroup hS.kgroup L⟩
  obtain ⟨hcyc, -⟩ :=
    NQCat.sqtk_quasisimple_cyclic_large_prime_outer_sylows ↥L hL.1 hsqtk p hp hp5
  have hψ : IsPGroup p (toOuter L U).range :=
    hU.of_surjective (toOuter L U).rangeRestrict (toOuter L U).rangeRestrict_surjective
  obtain ⟨Q, hQ⟩ := hψ.exists_le_sylow
  have := hcyc Q
  exact exists_zpowers_sup_of_cyclic_range L U (Subgroup.isCyclic_of_le hQ)

end CFSG.Quasithin.H13.NQCore
