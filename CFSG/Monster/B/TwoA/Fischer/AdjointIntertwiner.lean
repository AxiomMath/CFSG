module

public import CFSG.Monster.B.TwoA.Fischer.AdjointIntertwinerQuot
public import CFSG.Monster.B.TwoA.Fischer.GramMinor

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.E6.FixedE6 CFSG.Monster.B.E6.FixedE6Root CFSG.Monster.B.E6.StdF4
  CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.FieldExtension
  CFSG.Monster.B.Fischer CFSG.Sporadic.SmallF2
open scoped Matrix

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

namespace IsFischerSlice

variable (hS : IsFischerSlice act lab Y)
include hS

theorem exact_fixed_E6_adjoint_intertwiner
    (ρ : sliceGroup lab Y →* stdGroup)
    (hρ : Function.Injective ρ)
    (hroot : ∀ y : Y, ρ ⟨lab y, lab_mem_sliceGroup y.2⟩ ∈ rootClass)
    (Φ : Y ≃ CFSG.Monster.B.Fischer.Y) (ψ : sliceGroup lab Y ≃* CFSG.Monster.B.Fischer.J)
    (hψ : ∀ (h : sliceGroup lab Y) (v w : Y), (w : V) = act (h : S) v →
      (ψ h : Equiv.Perm CFSG.Monster.B.Fischer.Y) (Φ v) = Φ w)
    {x : V} (hx : x ∈ Y) (hxo : Φ ⟨x, hx⟩ = CFSG.Monster.B.Fischer.o)
    (hxT : (ψ ⟨lab x, lab_mem_sliceGroup hx⟩ : Equiv.Perm CFSG.Monster.B.Fischer.Y) = tPerm) :
    Function.Surjective (adjMap ρ) ∧ LinearMap.ker (adjMap ρ) = ncommRad lab Y ∧
    Module.finrank (ZMod 2) (NcommQuot lab Y) = 78 ∧
    (∀ u ∈ ncommRad lab Y, ∀ u', ncommProd act lab Y u u' ∈ ncommRad lab Y ∧
      ncommProd act lab Y u' u ∈ ncommRad lab Y) ∧
    ∃ (Ψ : NcommQuot lab Y ≃ₗ[ZMod 2] fixedL)
      (μ : NcommQuot lab Y →ₗ[ZMod 2] NcommQuot lab Y →ₗ[ZMod 2] NcommQuot lab Y),
      (∀ y, Ψ (ncommVec lab Y y) = adjVec ρ y) ∧
      (∀ a b, formL (Ψ a) (Ψ b) = ncommQuotForm lab Y a b) ∧
      (∀ h a, Ψ (ncommQuotRep act lab Y (sliceGroup lab Y) hS.mapsTo hS.lab_act h a) =
        actStar (SemidirectProduct.inl (ρ h)) (Ψ a)) ∧
      (∀ u u', μ (Submodule.Quotient.mk u) (Submodule.Quotient.mk u') =
        Submodule.Quotient.mk (ncommProd act lab Y u u')) ∧
      (∀ a, μ a a = 0) ∧ (∀ a b c, μ a (μ b c) + μ b (μ c a) + μ c (μ a b) = 0) ∧
      (∀ a b, Ψ (μ a b) = bracketL (Ψ a) (Ψ b)) ∧
      (∀ (y : Y) a, ncommQuotRep act lab Y (sliceGroup lab Y) hS.mapsTo hS.lab_act
          ⟨lab y, lab_mem_sliceGroup y.2⟩ a =
        a + μ (ncommVec lab Y y) a + ncommQuotForm lab Y (ncommVec lab Y y) a • ncommVec lab Y y) ∧
      (∀ i : Fin 78, (ι (Φ (Φ.symm (Cert.jWord (Cert.labelWord i) o))) : ℕ) = Cert.basisPt i) ∧
      LinearIndependent (ZMod 2)
        (fun i : Fin 78 => ncommVec lab Y (Φ.symm (Cert.jWord (Cert.labelWord i) o))) ∧
      ∀ y : Y, ncommVec lab Y y = ∑ i : Fin 78,
        (if (Cert.labelCoord (ι (Φ y))).testBit i then (1 : ZMod 2) else 0) •
          ncommVec lab Y (Φ.symm (Cert.jWord (Cert.labelWord i) o)) := by
  have hG : ∀ i k : Fin 78, ncommInd lab (gramPt Y Φ i) (gramPt Y Φ k) =
      rowsMatrix 78 Cert.gramRowArr i k := fun i k =>
    (ncommQuotForm_ncommVec lab Y _ _).symm.trans (hS.ncommQuotForm_gramPt hψ hx hxo hxT i k)
  have hsurj := hS.adjMap_surjective hρ hroot gramMinor_det_ne_zero hG
  have hker := hS.adjMap_eq_zero_iff hρ hroot hsurj
  refine ⟨hsurj, hS.ker_adjMap hρ hroot hsurj,
    hS.finrank_ncommQuot hρ hroot gramMinor_det_ne_zero hG,
    fun u hu u' => hS.ncommProd_mem_ncommRad hρ hroot hsurj hu u',
    adjEquiv hsurj hker, adjProd hsurj hker, adjEquiv_ncommVec hsurj hker,
    hS.formL_adjEquiv hρ hroot hsurj, hS.adjEquiv_ncommQuotRep hroot hsurj hker,
    hS.adjProd_mk hρ hroot hsurj, adjProd_self hsurj hker, adjProd_jacobi hsurj hker,
    adjEquiv_adjProd hsurj hker, hS.ncommQuotRep_lab hρ hroot hsurj,
    fun i => ι_gramPt Φ i.2, linearIndependent_ncommVec_yb gramMinor_det_ne_zero hG,
    fun y => ?_⟩
  refine hS.ncommVec_eq_sum hρ hroot gramMinor_det_ne_zero hG y _ ?_
  change rowsMatrix 78 Cert.gramRowArr *ᵥ toVecD 78 (Cert.labelCoord (ι (Φ y))) = _
  rw [Cert.fischer_label_coordinates_certificate.2 (Φ y)]
  funext i
  rw [hS.ncommInd_gramPt hψ hx hxo hxT i.2]

end IsFischerSlice

end CFSG.Monster.B.TwoA.Fischer
