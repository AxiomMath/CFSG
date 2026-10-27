
module

public import CFSG.Monster.B.TwoA.Sp8.GenActionGenBase

public import CFSG.Monster.B.TwoA.Sp8.GenActionConj
public import CFSG.Monster.B.Rep4371.FaithfulImage
public meta import CFSG.Monster.B.TwoA.Sp8.GenActionConj
public import Certificates.Data.CFSGNative.MonsterB.Short
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Certificates.Data.Kernel.VisFrame.Gens
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Co2Inv.ConjCertInputs
public import CFSG.Monster.B.TwoA.Co2Inv.FrameCertInputs
public import CFSG.Monster.B.TwoA.Sp8.LiftsInputs
public import CFSG.Monster.B.TwoA.Sp8.A8Inputs
public import CFSG.Monster.B.TwoA.Sp8.GenActionLiftsInputs
public import CFSG.Monster.B.TwoA.Sp8.GenActionDiffInputs
public import CFSG.Monster.B.TwoA.Sp8.GenActionConjInputs
public import CFSG.Monster.B.Rep4371.SmallFaithful
public import CFSG.Monster.B.Gen.Max2Assembly
public import CFSG.Monster.B.Gen.PacketGeneration
public import CFSG.Monster.B.Gen.EbarPairing
public import CFSG.Monster.B.Cbar.SimpleAux
public import CFSG.Monster.B.Rep4371.FaithfulImageInputs
public import CFSG.Monster.B.TwoA.Base.WCls
public import CFSG.Monster.B.TwoA.Census.PermBFS
public import CFSG.Monster.B.TwoA.Co2Inv.Data
public import CFSG.Monster.B.TwoA.Co2Inv.RowsInputs

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.Rep4371

instance finite_A8 : Finite (A8 : Set Dfull) := Subtype.finite

abbrev Lcl :
    Subgroup Dfull := Subgroup.closure (Set.range h1LiftD)

theorem h1LiftD_mem_Lcl
    (k : Fin 44) : h1LiftD k ∈ Lcl := Subgroup.subset_closure ⟨k, rfl⟩

theorem iotaD_ePauli
    {i : Fin 23} {k : Fin 44} (hk : (k : ℕ) < 23)
    (h : Model.qPauli i = pauliGen k) : iotaD (ePauli i) = h1LiftD k := by
  rw [h1LiftD, h1LiftC_pauli hk, ePauli]
  exact congrArg (fun x => iotaD (kappa x))
    (Subtype.ext (congrArg rhoEquiv ((qElt_eq i).trans (congrArg pauliQ h))))

@[expose] def pauliD
    (i : Fin 23) : Dfull := h1LiftD ⟨i, by omega⟩

abbrev Ecl :
    Subgroup Dfull := Subgroup.closure (Set.range pauliD)

theorem pauliD_mem_Ecl
    (i : Fin 23) : pauliD i ∈ Ecl := Subgroup.subset_closure ⟨i, rfl⟩

theorem xhat_mem_Ecl :
    xhat ∈ Ecl := by
  have hg : (gramPauli 0 11).val = 1 := by decide
  have h := congrArg iotaD (ePauli'_rel 0 11)
  rw [map_mul, map_mul, map_mul, map_pow, iotaD_xbar, hg, pow_one] at h
  have e0 : iotaD (ePauli' 0) = pauliD 0 :=
    iotaD_ePauli (by decide) (qPauli_low 1 le_rfl (by decide))
  have e12 : iotaD (ePauli' 11) = pauliD 12 := iotaD_ePauli (by decide) (qPauli_high 12 le_rfl)
  rw [e0, e12] at h
  have hx : xhat = (pauliD 12 * pauliD 0)⁻¹ * (pauliD 0 * pauliD 12) := by
    rw [h, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [hx]
  exact Ecl.mul_mem (Ecl.inv_mem (Ecl.mul_mem (pauliD_mem_Ecl _) (pauliD_mem_Ecl _)))
    (Ecl.mul_mem (pauliD_mem_Ecl _) (pauliD_mem_Ecl _))

theorem iotaD_ePauli_mem
    (i : Fin 23) : iotaD (ePauli i) ∈ Ecl := by
  by_cases h0 : (i : ℕ) = 0
  · have hi : i = 0 := Fin.ext h0
    rw [hi, ePauli_zero, iotaD_xbar]
    exact xhat_mem_Ecl
  by_cases h11 : (i : ℕ) ≤ 11
  · rw [iotaD_ePauli (k := ⟨i - 1, by omega⟩) (by simp; omega)
      (qPauli_low i (by omega) h11)]
    exact pauliD_mem_Ecl ⟨i - 1, by omega⟩
  · rw [iotaD_ePauli (k := ⟨i, by omega⟩) (by simp) (qPauli_high i (by omega))]
    exact pauliD_mem_Ecl i

theorem Ehat_eq_closure :
    Ehat = Subgroup.closure (Set.range pauliD) := by
  refine le_antisymm ?_ ((Subgroup.closure_le _).2 ?_)
  · rw [Ehat, Ebar_eq_closure_pauli, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact iotaD_ePauli_mem i
  · rintro _ ⟨i, rfl⟩
    exact h1LiftD_mem_Ehat (show ((⟨i, by omega⟩ : Fin 44) : ℕ) < 23 from i.2)

theorem Ehat_le_closure :
    Ehat ≤ Lcl := by
  rw [Ehat_eq_closure, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact h1LiftD_mem_Lcl _

theorem closure_cGen :
    Subgroup.closure (Set.range cGen) = Cr := by
  rw [← G21_eq, G21_eq_Cr]

theorem H1_eq_closure :
    H1 = Subgroup.closure (Set.range h1LiftD) := by
  refine le_antisymm (fun h hh => ?_) ((Subgroup.closure_le _).2 ?_)
  · obtain ⟨hJ, -⟩ := (mem_H1_iff h).1 hh
    have hCr : Cr ≤ (Lcl.subgroupOf Jhat).map jhatToKv0 := by
      rw [← closure_cGen, Subgroup.closure_le]
      rintro _ ⟨j, rfl⟩
      have hj : (cGen j)⁻¹ ∈ (Lcl.subgroupOf Jhat).map jhatToKv0 := by
        refine ⟨⟨h1LiftD ⟨23 + j, by omega⟩, h1LiftD_mem_Jhat _⟩, h1LiftD_mem_Lcl _, ?_⟩
        rw [jhatToKv0_h1LiftD (by simp)]
        congr 2
        ext
        simp
      simpa using Subgroup.inv_mem _ hj
    obtain ⟨hJ', hC⟩ := (mem_H1_iff h).1 hh
    obtain ⟨g, hg, hgh⟩ := hCr hC
    have hk : (⟨h, hJ'⟩ : Jhat) * g⁻¹ ∈ jhatToKv0.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hgh, mul_inv_cancel]
    rw [ker_jhatToKv0, Subgroup.mem_subgroupOf] at hk
    have e : h = ((⟨h, hJ'⟩ : Jhat) * g⁻¹ : Jhat) * (g : Dfull) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]
    rw [e]
    exact Lcl.mul_mem (Ehat_le_closure hk) hg
  · rintro _ ⟨k, rfl⟩
    exact h1LiftD_mem_H1 k

theorem Xgrp_eq_closure :
    Xgrp = Subgroup.closure (insert tauhat (Set.range h1LiftD)) := by
  rw [Xgrp, H1_eq_closure]
  refine le_antisymm ((Subgroup.closure_le _).2 ?_)
    (Subgroup.closure_mono (Set.insert_subset_insert Subgroup.subset_closure))
  rintro x (rfl | hx)
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.closure_mono (Set.subset_insert _ _) hx

theorem h1LiftD_mem_normalizer
    (k : Fin 44) :
    h1LiftD k ∈ Subgroup.normalizer (A8 : Set Dfull) :=
  Subgroup.mem_normalizer_fintype fun x hx => conj_A8_le (h1LiftD k)
    (fun j => by rw [h1LiftD_conj_aT]; exact (aEquiv _).2) x hx

theorem H1_le_normalizer :
    H1 ≤ Subgroup.normalizer (A8 : Set Dfull) := by
  rw [H1_eq_closure, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  exact h1LiftD_mem_normalizer k

theorem Xgrp_le_normalizer :
    Xgrp ≤ Subgroup.normalizer (A8 : Set Dfull) := by
  rw [Xgrp, Subgroup.closure_le]
  rintro x (rfl | hx)
  · exact tauhat_mem_normalizer_A8
  · exact H1_le_normalizer hx

end CFSG.Monster.B.TwoA.Sp8
