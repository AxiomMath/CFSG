module

public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

theorem exists_mulEquiv_genFittingFStar_of_hasQuotShape {Q : Type} [Group Q] [Finite Q]
    {H N : Subgroup Q} (hN : (N.subgroupOf H).Normal) {P : ∀ (X : Type) [Group X], Prop}
    (h : HasQuotShape (fStarMod N H) (N : Set Q) P) :
    ∃ (X : Type) (_ : Group X), P X ∧
      Nonempty (↥(CFSG.Open.genFittingFStar (↥H ⧸ (N.subgroupOf H).normalCore)) ≃* X) := by
  obtain ⟨X, hX, φ, hφ, hker, hP⟩ := h
  haveI := hN
  let Nc : Subgroup ↥H := (N.subgroupOf H).normalCore
  have hcore : Nc = N.subgroupOf H := Subgroup.normalCore_eq_self _
  let F : Subgroup (↥H ⧸ Nc) := CFSG.Open.genFittingFStar (↥H ⧸ Nc)
  let Fp : Subgroup ↥H := F.comap (QuotientGroup.mk' Nc)
  let π : ↥H →* ↥H ⧸ Nc := QuotientGroup.mk' Nc
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Nc
  let ψ : ↥Fp →* ↥F := π.subgroupComap F
  have hψ : Function.Surjective ψ := MonoidHom.subgroupComap_surjective π F hπ
  let α : ↥Fp ≃* ↥(Fp.map H.subtype) :=
    Subgroup.equivMapOfInjective Fp H.subtype H.subtype_injective
  have hcoe : ∀ k : ↥Fp, ((α k : ↥(Fp.map H.subtype)) : Q) = ((k : ↥H) : Q) := fun k =>
    Subgroup.coe_equivMapOfInjective_apply Fp H.subtype H.subtype_injective k
  let φ' : ↥Fp →* X := φ.comp α.toMonoidHom
  have hφ' : Function.Surjective φ' := hφ.comp α.surjective
  have hkerφ' : ∀ k : ↥Fp, φ' k = 1 ↔ (k : ↥H) ∈ Nc := by
    intro k
    change φ (α k) = 1 ↔ (k : ↥H) ∈ Nc
    rw [hker (α k), hcoe k, hcore, Subgroup.mem_subgroupOf]
    rfl
  have hkerψ : ∀ k : ↥Fp, ψ k = 1 ↔ (k : ↥H) ∈ Nc := by
    intro k
    rw [Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff (k : ↥H)
  have hker_eq : ψ.ker = φ'.ker := by
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hkerψ k, hkerφ' k]
  refine ⟨X, hX, hP, ?_⟩
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker_eq).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ' hφ'))⟩

end CFSG.LocalAnalysis.WeakClosure81
