module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35S6A
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Stmt2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C56a2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53
open scoped commutatorElement

namespace S35.S6

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

open S35.C56 S35.C56.Six

theorem CVQ_relIndex_le_two (hS : Sit H M S) {β : Geo H M} (hβ : vtype β = false) {q0 : G}
    (hq0 : q0 ∈ Qv β) (hq0K : ∀ q ∈ Qv β, q ∉ Kb β → q0⁻¹ * q ∈ Kb β) :
    (CVQ β).relIndex (Vn β) ≤ 2 := by
  have hZ2 := hS.cardZ5 β hβ
  have hcomm : ∀ v ∈ Vn β, ⁅v, q0⁆ ∈ Zv β := fun v hv => by
    have := Subgroup.commutator_mem_commutator hv hq0
    rwa [Std.comm_Vn_Qv hS hβ] at this
  have hmem : ∀ v ∈ Vn β, v * q0 = q0 * v → v ∈ CVQ β := by
    intro v hv hc
    refine ⟨hv, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
    by_cases hqK : q ∈ Kb β
    · exact (Subgroup.mem_centralizer_iff.mp hqK.2 v hv).symm
    · have hy := hq0K q hq hqK
      have hyc := Subgroup.mem_centralizer_iff.mp hy.2 v hv
      have hqe : q = q0 * (q0⁻¹ * q) := by group
      rw [hqe]
      calc q0 * (q0⁻¹ * q) * v = q0 * ((q0⁻¹ * q) * v) := by rw [mul_assoc]
        _ = q0 * (v * (q0⁻¹ * q)) := by rw [hyc]
        _ = (q0 * v) * (q0⁻¹ * q) := by rw [← mul_assoc]
        _ = v * q0 * (q0⁻¹ * q) := by rw [hc]
        _ = v * (q0 * (q0⁻¹ * q)) := by rw [mul_assoc]
  refine relIndex_le_two fun u hu v hv huC hvC => ?_
  have hu1 : ⁅u, q0⁆ ≠ 1 := fun h =>
    huC (hmem u hu (commutatorElement_eq_one_iff_mul_comm.mp h))
  have hv1 : ⁅v, q0⁆ ≠ 1 := fun h =>
    hvC (hmem v hv (commutatorElement_eq_one_iff_mul_comm.mp h))
  have e := eq_of_card_two hZ2 (hcomm u hu) (hcomm v hv) hu1 hv1
  rw [commutatorElement_def, commutatorElement_def] at e
  have e2 : u * q0 * u⁻¹ = v * q0 * v⁻¹ := mul_right_cancel e
  refine hmem _ ((Vn β).mul_mem ((Vn β).inv_mem hu) hv) ?_
  calc u⁻¹ * v * q0 = u⁻¹ * (v * q0 * v⁻¹) * v := by group
    _ = u⁻¹ * (u * q0 * u⁻¹) * v := by rw [e2]
    _ = q0 * (u⁻¹ * v) := by group

theorem claimS6 (hS : Sit H M S) : S35.II.ClaimS6 H M := by
  intro β hβ
  by_contra hlt
  rw [not_le] at hlt
  have hKQ : Kb β ≤ Qv β := inf_le_left
  have hZ2 := hS.cardZ5 β hβ
  have hpow : ∃ j : ℕ, (Kb β).relIndex (Qv β) = 2 ^ j := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 (pCoreOf_isPGroup 2 (stab β))
    have hmul := Subgroup.relIndex_mul_card (Kb β) (Qv β)
    have hdvd : (Kb β).relIndex (Qv β) ∣ 2 ^ m := by
      refine ⟨Nat.card ((Kb β ⊓ Qv β : Subgroup G)), ?_⟩
      rw [← hm]
      exact hmul.symm
    exact (Nat.dvd_prime_pow Nat.prime_two).mp hdvd |>.imp fun j hj => hj.2
  obtain ⟨j, hj⟩ := hpow
  have hj' : j = 0 ∨ j = 1 := by
    by_contra hne
    have : 2 ^ 2 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rcases hj' with rfl | rfl
  ·
    have hQK : Qv β ≤ Kb β := Subgroup.relIndex_eq_one.mp (by simpa using hj)
    have h1 : Vn β ≤ Subgroup.centralizer (Qv β : Set G) := fun v hv =>
      Subgroup.mem_centralizer_iff.mpr fun q hq =>
        (Subgroup.mem_centralizer_iff.mp (hQK hq).2 v hv).symm
    have hbot : ⁅Vn β, Qv β⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h1
    rw [Std.comm_Vn_Qv hS hβ] at hbot
    rw [hbot, Subgroup.card_bot] at hZ2
    omega
  · have h2 : (Kb β).relIndex (Qv β) = 2 := by simpa using hj
    have hnle : ¬ Qv β ≤ Kb β := fun h => by
      rw [Subgroup.relIndex_eq_one.mpr h] at h2
      omega
    obtain ⟨q0, hq0, hq0K⟩ := Set.not_subset.mp hnle
    exact false_of_CVQ_index hS hβ (CVQ_relIndex_le_two hS hβ hq0 fun q hq hqK =>
      EmptyFaithful.Stellmacher.OrdinaryProofs.quot_mem_of_relIndex_two h2 hq0 hq hq0K hqK)

theorem claim6a (hS : Sit H M S) : Claim6a H M := by
  intro β l hβ hl h
  have hK := inter_le_Kb hS hl h
  have h4 := claimS6 hS β hβ
  have h2 := Std.relIndex_Qv hS hβ hl
  have := Subgroup.relIndex_le_of_le_left (L := Qv β) hK (relIndex_ne_zero' _ _)
  omega

end S35.S6

end F53.Stellmacher

end CFSG.Quasithin
