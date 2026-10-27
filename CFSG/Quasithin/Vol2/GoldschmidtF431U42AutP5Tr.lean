module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5Mod3
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP1Lat

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

variable {G : Type} [Group G] {M₁ M₂ : Subgroup G}

@[expose] def AutIso.toG1 (iso : AutIso M₁ M₂) : ↥P1h →* G :=
  M₁.subtype.comp iso.phi1.toMonoidHom

@[expose] def AutIso.toG2 (iso : AutIso M₁ M₂) : ↥P2h →* G :=
  M₂.subtype.comp iso.phi2.toMonoidHom

theorem AutIso.toG1_injective (iso : AutIso M₁ M₂) : Function.Injective iso.toG1 :=
  fun _ _ h => iso.phi1.injective (Subtype.ext h)

theorem AutIso.toG2_injective (iso : AutIso M₁ M₂) : Function.Injective iso.toG2 :=
  fun _ _ h => iso.phi2.injective (Subtype.ext h)

theorem AutIso.toG1_inclusion (iso : AutIso M₁ M₂) (x : Bh) :
    iso.toG1 (Subgroup.inclusion Bh_le_P1h x) = iso.toG x :=
  congrArg Subtype.val (iso.comm1 x).symm

theorem AutIso.toG2_inclusion (iso : AutIso M₁ M₂) (x : Bh) :
    iso.toG2 (Subgroup.inclusion Bh_le_P2h x) = iso.toG x :=
  congrArg Subtype.val (iso.comm2 x).symm

@[expose] def fhB : ↥Bh := ⟨fhatA, fhatA_mem_Bh⟩

@[expose] def vB : ↥Bh := ⟨vA, vA_mem_Bh⟩

@[expose] def vP1 : ↥P1h := Subgroup.inclusion Bh_le_P1h vB

@[expose] def vP2 : ↥P2h := Subgroup.inclusion Bh_le_P2h vB

@[expose] def fP1 : ↥P1h := Subgroup.inclusion Bh_le_P1h fhB

@[expose] def fP2 : ↥P2h := Subgroup.inclusion Bh_le_P2h fhB

@[expose] def bP2 : ↥P2h := ⟨bA, bA_mem_P2h⟩

@[expose] def xP1 : ↥P1h := ⟨xwA, xwA_mem_P1h⟩

theorem coe_vP1 : (vP1 : Ah) = vA := rfl

theorem coe_vP2 : (vP2 : Ah) = vA := rfl

theorem coe_fP1 : (fP1 : Ah) = fhatA := rfl

theorem coe_bP2 : (bP2 : Ah) = bA := rfl

theorem coe_xP1 : (xP1 : Ah) = xwA := rfl

theorem vP2_sq : vP2 * vP2 = 1 := Subtype.ext vA_sq

theorem bP2_cube : bP2 * bP2 * bP2 = 1 := Subtype.ext bA_cube

theorem bP2_vP2_ne : bP2 * vP2 * bP2⁻¹ ≠ vP2 := by
  intro h
  apply wA_ne_vA
  have h' := congrArg Subtype.val h
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_bP2, coe_vP2, wA] using h'

theorem vP2_comm : vP2 * (bP2 * vP2 * bP2⁻¹) = (bP2 * vP2 * bP2⁻¹) * vP2 :=
  Subtype.ext vA_comm_wA

theorem bP2_rel : bP2 * (bP2 * vP2 * bP2⁻¹) * bP2⁻¹ = vP2 * (bP2 * vP2 * bP2⁻¹) :=
  Subtype.ext bA_rel

theorem vP2_comm_f : vP2 * fP2 = fP2 * vP2 := Subtype.ext vA_comm_f

theorem bP2_comm_f : bP2 * fP2 = fP2 * bP2 := Subtype.ext bA_comm_f

theorem xP1_comm_f : xP1 * fP1 = fP1 * xP1 := Subtype.ext xwA_comm_f

theorem uP1_cube : (vP1 * (xP1 * vP1 * xP1⁻¹)) * ((vP1 * (xP1 * vP1 * xP1⁻¹)) *
    (vP1 * (xP1 * vP1 * xP1⁻¹))) = 1 := by
  apply Subtype.ext
  have h := uA_cube
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one, coe_vP1, coe_xP1, uA] using h

theorem uP1_ne_one : vP1 * (xP1 * vP1 * xP1⁻¹) ≠ 1 := by
  intro h
  apply uA_ne_one
  have h' := congrArg Subtype.val h
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one, coe_vP1, coe_xP1, uA] using h'

end CFSG.Quasithin.H13.F431.U42Aut
