module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C56a3
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C56Irr
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Stmt
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C56a2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53
open scoped commutatorElement

namespace S35.C56

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace Six

theorem false_of_inter_le_Kb (hS : Sit H M S) (hI : CaseI H M) {β l : Geo H M}
    (hβ : vtype β = false) (hl : l ∈ nbrs β) (hK : Qv β ⊓ Qv l ≤ Kb β) : False := by
  have horth := orthZ hS hI hβ
  obtain ⟨q0, hq0, hq0l⟩ := Set.not_subset.mp (Std.Q_not_le hS hβ hl)
  have hZ2 := hS.cardZ5 β hβ
  have hcomm : ∀ v ∈ Vn β, ⁅v, q0⁆ ∈ Zv β := fun v hv => by
    have := Subgroup.commutator_mem_commutator hv hq0
    rwa [Std.comm_Vn_Qv hS hβ] at this
  rcases horth.irred (CVQ β) (Zv_le_CVQ hS hβ) inf_le_left (stab_le_normalizer_CVQ β) with hC | hC
  · have h16 := horth.relIndex_eq
    rw [← hC] at h16
    have hle : (CVQ β).relIndex (Vn β) ≤ 2 := by
      refine relIndex_le_two fun u hu v hv huC hvC => ?_
      have hu1 : ⁅u, q0⁆ ≠ 1 := fun h =>
        huC (mem_CVQ_iff hS hβ hl hK hq0 hq0l hu (commutatorElement_eq_one_iff_mul_comm.mp h))
      have hv1 : ⁅v, q0⁆ ≠ 1 := fun h =>
        hvC (mem_CVQ_iff hS hβ hl hK hq0 hq0l hv (commutatorElement_eq_one_iff_mul_comm.mp h))
      have e := eq_of_card_two hZ2 (hcomm u hu) (hcomm v hv) hu1 hv1
      rw [commutatorElement_def, commutatorElement_def] at e
      have e2 : u * q0 * u⁻¹ = v * q0 * v⁻¹ := mul_right_cancel e
      refine mem_CVQ_iff hS hβ hl hK hq0 hq0l ((Vn β).mul_mem ((Vn β).inv_mem hu) hv) ?_
      calc u⁻¹ * v * q0 = u⁻¹ * (v * q0 * v⁻¹) * v := by group
        _ = u⁻¹ * (u * q0 * u⁻¹) * v := by rw [e2]
        _ = q0 * (u⁻¹ * v) := by group
    omega
  · have h1 : Vn β ≤ Subgroup.centralizer (Qv β : Set G) := by
      rw [← hC]
      exact inf_le_right
    have hbot : ⁅Vn β, Qv β⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h1
    rw [Std.comm_Vn_Qv hS hβ] at hbot
    rw [hbot, Subgroup.card_bot] at hZ2
    omega

end Six

theorem claim6a (hS : Sit H M S) (hI : CaseI H M) : Claim6a H M := by
  intro β l hβ hl h
  exact Six.false_of_inter_le_Kb hS hI hβ hl (Six.inter_le_Kb hS hl h)

end S35.C56

end F53.Stellmacher

end CFSG.Quasithin
