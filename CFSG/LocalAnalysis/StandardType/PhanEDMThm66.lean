module

public import CFSG.LocalAnalysis.StandardType.PhanEDMThm314
public import CFSG.LocalAnalysis.StandardType.PhanEDMAff
public import CFSG.LocalAnalysis.StandardType.PhanEDMRestrict

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.DM

open CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding
  CFSG.ClassicalInvolution.Phan.PhanE

variable {ι : Type} {M : CoxeterMatrix ι} {W : Type} [Group W] (cs : CoxeterSystem M W)
  {C : Type} (δ : C → C → W)

theorem inducedSystem_eq_restrictBy (J : Set ι) (A : Set C) :
    inducedSystem cs δ J A = restrictBy (buildingSystem cs δ) (Subtype.val : J → ι) A := rfl

theorem inducedSystemAll_eq_restrictBy (A : Set C) :
    inducedSystemAll cs δ A = restrictBy (buildingSystem cs δ) (id : ι → ι) A := rfl

theorem connected_inducedSystem_iff (J : Set ι) (A : Set C) :
    (inducedSystem cs δ J A).Connected ↔ ConnectedIn (buildingSystem cs δ) J A := by
  rw [inducedSystem_eq_restrictBy,
    connected_restrictBy_iff (buildingSystem cs δ) (A := A) (e := Subtype.val)
      Subtype.val_injective,
    Subtype.range_coe]

theorem simplyTwoConnected_inducedSystem_iff (J : Set ι) (A : Set C) :
    (inducedSystem cs δ J A).SimplyTwoConnected ↔
      SimplyConnectedIn (buildingSystem cs δ) J A 2 := by
  rw [inducedSystem_eq_restrictBy,
    simplyTwoConnected_restrictBy_iff (buildingSystem cs δ) (A := A) (e := Subtype.val)
      Subtype.val_injective,
    Subtype.range_coe]

theorem connected_inducedSystemAll_iff (A : Set C) :
    (inducedSystemAll cs δ A).Connected ↔ ConnectedIn (buildingSystem cs δ) Set.univ A := by
  rw [inducedSystemAll_eq_restrictBy,
    connected_restrictBy_iff (buildingSystem cs δ) (A := A) (e := id) Function.injective_id,
    Set.range_id]

theorem simplyTwoConnected_inducedSystemAll_iff (A : Set C) :
    (inducedSystemAll cs δ A).SimplyTwoConnected ↔
      SimplyConnectedIn (buildingSystem cs δ) Set.univ A 2 := by
  rw [inducedSystemAll_eq_restrictBy,
    simplyTwoConnected_restrictBy_iff (buildingSystem cs δ) (A := A) (e := id)
      Function.injective_id,
    Set.range_id]

theorem dm07Thm66 : DM07Thm66 := by
  intro ι _ M W _ cs w₀ hw C δ hB _hthick t ht hb hc
  haveI : Finite W := CoxeterSystem.finite_of_w0 cs w₀ hw
  obtain ⟨rk, hinj, hone, hmono⟩ := CoxeterSystem.exists_rank cs
  have hrk : IsRankFn cs rk := ⟨hinj, hone, hmono⟩
  have hX : (buildingSystem cs δ).Connected := buildingSystem_connected hB
  have hsc : (buildingSystem cs δ).SimplyTwoConnected := buildingSystem_simplyTwoConnected hB
  have hres : IsResidual (buildingSystem cs δ) (flipLev rk δ w₀ t) :=
    flipLev_isResidual hB hw ht hrk
  have hlco : Lco (buildingSystem cs δ) (flipLev rk δ w₀ t) := by
    intro J c hJ
    rw [buildingSystem_residue hB J c, aff_flipLev_eq_flipMaxSet hB hw ht hrk J c]
    have hJ' : J.ncard = 2 := by simp [Set.ncard_def, hJ]
    exact (connected_inducedSystem_iff cs δ J _).mp (hb J c hJ')
  have hlsco : Lsco (buildingSystem cs δ) (flipLev rk δ w₀ t) := by
    intro J c hJ
    rw [buildingSystem_residue hB J c, aff_flipLev_eq_flipMaxSet hB hw ht hrk J c]
    have hJ' : J.ncard = 3 := by simp [Set.ncard_def, hJ]
    exact (simplyTwoConnected_inducedSystem_iff cs δ J _).mp (hc J c hJ').2
  obtain ⟨hC, hS⟩ := DM07_thm314 hres hlco hlsco hX hsc
  have hset : levelSet (flipLev rk δ w₀ t) 0 = flipOpSet δ w₀ t := by
    ext x
    simpa [levelSet] using flipLev_eq_zero_iff hw hrk x
  rw [hset] at hC hS
  exact ⟨(connected_inducedSystemAll_iff cs δ _).mpr hC,
    (simplyTwoConnected_inducedSystemAll_iff cs δ _).mpr hS⟩

end CFSG.ClassicalInvolution.Phan.PhanE.DM
