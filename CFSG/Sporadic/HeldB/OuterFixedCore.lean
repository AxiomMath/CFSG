module

public import CFSG.Sporadic.HeldB.AutModelCore
public import CFSG.Sporadic.HeldB.FixedTransport

public noncomputable section

namespace CFSG.Sporadic.HeldB

open CFSG.ComponentClassification.FixedCommutingProduct

theorem map_fixedSubgroup_heConjR
    (x : heAutGroup) :
    (fixedSubgroup (heConjR x)).map heP.subtype =
      heP ⊓ Subgroup.centralizer {(x : Equiv.Perm (Fin 8330))} := by
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [mem_fixedSubgroup] at hz
    have h := congrArg Subtype.val hz
    simp only [heConjR_apply, Subgroup.coe_inv] at h
    refine ⟨z.2, ?_⟩
    calc (z : Equiv.Perm (Fin 8330)) * x = x * z * (x : Equiv.Perm (Fin 8330))⁻¹ * x := by
          rw [h]
      _ = x * z := by group
  · rintro ⟨hy, hyx⟩
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    rw [mem_fixedSubgroup]
    apply Subtype.ext
    rw [heConjR_apply]
    change (x : Equiv.Perm (Fin 8330)) * y * (x : Equiv.Perm (Fin 8330))⁻¹ = y
    rw [← hyx, mul_inv_cancel_right]

@[expose] def fixedSubgroupEquivOfConj
    (x : heAutGroup) {g : Equiv.Perm (Fin 8330)} (hg : g ∈ heP)
    (y : Equiv.Perm (Fin 8330)) (hx : (x : Equiv.Perm (Fin 8330)) = g * y * g⁻¹) :
    fixedSubgroup (heConjR x) ≃* (heP ⊓ Subgroup.centralizer {y} : Subgroup _) :=
  (((fixedSubgroup (heConjR x)).equivMapOfInjective heP.subtype heP.subtype_injective).trans
    (MulEquiv.subgroupCongr (by rw [map_fixedSubgroup_heConjR, hx]))).trans
    (infCentralizerConjEquiv hg y)

theorem exists_heConjR_eq
    (hbij : Function.Bijective heConjR) (β : MulAut heP)
    (hβ : orderOf β = 2) (hinn : β ∉ (MulAut.conj : heP →* MulAut heP).range) :
    ∃ x : heAutGroup, heConjR x = β ∧ (x : Equiv.Perm (Fin 8330)) ∉ heP ∧
      orderOf (x : Equiv.Perm (Fin 8330)) = 2 := by
  obtain ⟨x, hx⟩ := hbij.2 β
  refine ⟨x, hx, fun hmem => hinn ⟨⟨x, hmem⟩, ?_⟩, ?_⟩
  · rw [← hx]
    refine MulEquiv.ext fun p => Subtype.ext ?_
    rw [heConjR_apply, MulAut.conj_apply]
    rfl
  · rw [Subgroup.orderOf_coe, ← orderOf_injective heConjR hbij.1 x, hx, hβ]

theorem outer_fixed_pComponent_quasisimple_of
    (hbij : Function.Bijective heConjR)
    (hcls : ∀ x ∈ heAutGroup, x ∉ heP → orderOf x = 2 → ∃ g ∈ heP, x = g * heAutU * g⁻¹)
    (hC : ∀ L : Subgroup (heP ⊓ Subgroup.centralizer {heAutU} : Subgroup _),
      CFSG.IsPComponent 2 L → CFSG.IsQuasisimple L)
    {S : Type*} [Group S] (e : S ≃* heP) (α : MulAut S) (hα : orderOf α = 2)
    (hinn : α ∉ (MulAut.conj : S →* MulAut S).range)
    (L : Subgroup (fixedSubgroup α)) (hL : CFSG.IsPComponent 2 L) : CFSG.IsQuasisimple L := by
  have : Finite S := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨x, hx, hxP, hx2⟩ := exists_heConjR_eq hbij (MulAut.congr e α)
    (by rw [orderOf_congr, hα]) (by rwa [congr_mem_range_conj_iff])
  obtain ⟨g, hg, hxg⟩ := hcls x x.2 hxP hx2
  let f : fixedSubgroup α ≃* (heP ⊓ Subgroup.centralizer {heAutU} : Subgroup _) :=
    ((fixedSubgroupCongr e α).trans (MulEquiv.subgroupCongr (by rw [hx]))).trans
      (fixedSubgroupEquivOfConj x hg heAutU hxg)
  exact pComponent_quasisimple_of_mulEquiv f 2 Nat.prime_two hC L hL

end CFSG.Sporadic.HeldB
