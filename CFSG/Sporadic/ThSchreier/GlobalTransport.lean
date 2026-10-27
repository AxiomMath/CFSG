
module

public import CFSG.Sporadic.ThSchreier.GlobalTransportBase1

public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.Th.Simple
public meta import CFSG.Sporadic.ThSchreier.Row
public meta import CFSG.Sporadic.ThSchreier.LocalOrbit
public import Certificates.Certificate2311
public import CFSG.Sporadic.ThSchreier.RowInputs
public meta import Certificates.Data.CFSGNative.Th.Base
public import CFSG.Sporadic.Th.Plane
public import CFSG.Sporadic.Th.FormBase
public import Certificates.Data.CFSGNative.Th.Base
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate
public import CFSG.Sporadic.ThSchreier.AutCore

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 Pointwise

private theorem native_rowKey_wKey : rowKeyOf wKey = wKeyRow :=
  Certificates.certificate2311

theorem psiSet_W : psiSet W = planeWSet := by
  rw [psiSet, W, ← rowPlane_rowKeyOf, native_rowKey_wKey, rowPlane_wKeyRow]

theorem planeX_eq_image : planeX = psiSet '' MulAction.orbit J W := by
  ext U
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g • W, ⟨g, rfl⟩, by rw [psiSet_smul, psiSet_W]⟩
  · rintro ⟨S, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, by rw [psiSet_smul, psiSet_W]⟩

section Facts

variable (hF : OrbitFacts)
include hF

theorem psiSet_planeAt_mem (i : Fin nX) : psiSet (planeAt i) ∈ planeX := by
  rw [planeX_eq_image]
  refine ⟨planeAt i, ?_, rfl⟩
  have h : planeAt i ∈ MulAction.orbit J (planeAt 0) := by
    rw [← planeEquiv_apply hF i]
    exact (planeEquiv hF i).2
  rwa [planeAt_zero hF] at h

theorem ncard_planeX_eq : planeX.ncard = nX := by
  rw [planeX_eq_image, Set.ncard_image_of_injective _ psiSet_injective, ← planeAt_zero hF,
    ← Nat.card_coe_set_eq, Nat.card_congr (planeEquiv hF).symm, Nat.card_eq_fintype_card,
    Fintype.card_fin]

@[expose] noncomputable def colToRow : Fin nX →[J] planeX where
  toFun i := ⟨psiSet (planeAt i), psiSet_planeAt_mem hF i⟩
  map_smul' g i := by
    apply Subtype.ext
    show psiSet (planeAt (g • i : Fin nX)) = g • psiSet (planeAt i)
    rw [planeAt_smul hF, psiSet_smul]

theorem colToRow_bijective : Function.Bijective (colToRow hF) := by
  refine ⟨fun i j h => ?_, fun U => ?_⟩
  · have h' : psiSet (planeAt i) = psiSet (planeAt j) := congrArg Subtype.val h
    exact Fin.ext (planeAt_injective hF _ i.isLt _ j.isLt (psiSet_injective h'))
  · have hU : (U : Set RowV) ∈ psiSet '' MulAction.orbit J W := by
      rw [← planeX_eq_image]
      exact U.2
    obtain ⟨S, hS, hSU⟩ := hU
    rw [← planeAt_zero hF] at hS
    obtain ⟨i, hi⟩ := (planeEquiv hF).surjective ⟨S, hS⟩
    refine ⟨i, Subtype.ext ?_⟩
    show psiSet (planeAt i) = U
    rw [← hSU, ← planeEquiv_apply hF i, hi]

end Facts

section Cert

variable {c : ℕ} (hC : CertFacts c)
include hC

theorem ncard_planeX : planeX.ncard = 143127000 := by
  rw [ncard_planeX_eq hC.orbit, hC.count]

theorem stabilizer_planeWSet : MulAction.stabilizer J planeWSet = H := by
  rw [← stabilizer_root hC]
  ext g
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, ← psiSet_W, ← psiSet_smul,
    psiSet_injective.eq_iff, smul_idx_eq_iff hC.orbit]
  rw [show ((root hC : Fin nX) : ℕ) = 0 from rfl, planeAt_zero hC.orbit]

theorem card_stabilizer_planeWSet : Nat.card (MulAction.stabilizer J planeWSet) = 634023936 := by
  rw [stabilizer_planeWSet hC]
  exact card_H hC

theorem isPreprimitive_planeX : MulAction.IsPreprimitive J planeX := by
  have := isPreprimitive hC
  exact MulAction.IsPreprimitive.of_surjective (colToRow_bijective hC.orbit).surjective

end Cert

end CFSG.Sporadic.ThSchreier
