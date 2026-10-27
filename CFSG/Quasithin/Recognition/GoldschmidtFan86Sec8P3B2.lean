module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3B1
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Stmt3
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3WFrat

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

namespace Sec8P3

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
  {F : FanTree Γ G} {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem z_not_mem_nbrStab_delta (F : FanTree Γ G) (h71c : Fan71c F L) :
    L.z α ∉ nbrStab Γ G (D.delta 0) := by
  intro hz
  obtain ⟨ν, hν, hνξ⟩ := F.exists_adj_ne (D.delta 0) (D.xi 0)
  have hd : Γ.dist α ν = 5 := by
    have := IsTree.dist_succ_of_ne F.isTree (D.adj_xi_delta 0).symm hν (fun h => hνξ h.symm)
      (w := α) (by rw [D.dist_start_xi F 0, D.dist_delta F 0])
    rw [this, D.dist_delta F 0]
  have h1 := mem_nbrStab.1 hz ν hν
  have h2 := (h71c.z_smul_eq_iff D.val ν).1 h1
  omega

theorem pow_four_mem_nbrStab (F : FanTree Γ G) {v a : V} (hva : Γ.Adj v a)
    (hv : valence Γ v = 5) {w : G} (hwv : w • v = v) (hwa : w • a = a) :
    w ^ 4 ∈ nbrStab Γ G v := by
  obtain ⟨φ, hφ, -⟩ := F.exists_edge_char hva
  have hmem : w ∈ MulAction.stabilizer G v ⊓ MulAction.stabilizer G a := ⟨hwv, hwa⟩
  have hp : Fact (Fan86.valence Γ v).Prime := ⟨F.valence_isPrime v⟩
  have h4 : φ ⟨w, hmem⟩ ^ 4 = 1 := units_pow_four (Or.inr hv) _
  have := (hφ ((⟨w, hmem⟩ : ↥(MulAction.stabilizer G v ⊓ MulAction.stabilizer G a)) ^ 4)).2
    (by rw [map_pow, h4])
  simpa using this

theorem exists_w1 (F : FanTree Γ G) (h71a : Fan71a F L) (h71c : Fan71c F L) (h75 : Fan75 F L)
    (h65 : Fan65 F) (hcyc : IsCyclic ↥D.calpha) (hle : Nat.card ↥D.calpha ≤ 4) :
    ∃ w, IsW1Elem D w := by
  obtain ⟨w, ⟨hwα, hwβ⟩, hw⟩ := F.exists_normalizing_two h65 D.val (D.adj_start_beta 0)
    (D.x_mem_stabilizer F h71c) (D.orderOf_x F)
  have hwα' : w • α = α := MulAction.mem_stabilizer_iff.1 hwα
  have hwβ' : w • D.beta 0 = D.beta 0 := MulAction.mem_stabilizer_iff.1 hwβ
  have hwδ : w • D.delta 0 = D.delta 0 :=
    fixes_delta D F h71a h71c h75 hcyc hwα' hwβ' hw
  have hx5 : D.x ^ 5 = 1 := D.x_pow_five
  have hz2 : L.z (D.delta 0) * L.z (D.delta 0) = 1 := D.zd_mul_self F 0
  have hzx : L.z (D.delta 0) * D.x * L.z (D.delta 0) = D.x⁻¹ := D.zd_x_inv F
  have hP : w ∈ (D.P 0).stab G := (Arc.mem_stab G).2 fun m hm =>
    Arc.fixes_of_ends F.isTree F.adj_smul (D.P 0) (by rw [D.start]; exact hwα')
      (by exact hwδ) m hm
  have hwξ : w • D.xi 0 = D.xi 0 := (Arc.mem_stab G).1 hP 3 (by norm_num)
  have hz0β : L.z (D.delta 0) • D.beta 0 = D.beta 0 := by
    rw [h71c.z_smul_eq_iff (D.valence_delta F 0), dist_comm, D.dist_beta_delta F 0]
    norm_num
  have hz0α : L.z (D.delta 0) ∈ MulAction.stabilizer G α := D.z_delta_mem_stabilizer F h71c 0
  have hwz : w⁻¹ * L.z (D.delta 0) * w = L.z (D.delta 0) := by
    have h1 := L.z_inv_smul w (D.valence_delta F 0)
    rw [inv_smul_eq_iff.2 hwδ.symm] at h1
    exact h1.symm
  have hcomm : L.z (D.delta 0) * w = w * L.z (D.delta 0) := by
    have := congrArg (fun y => w * y) hwz
    simpa [mul_assoc] using this
  have hcomm2 : L.z (D.delta 0) * w ^ 2 = w ^ 2 * L.z (D.delta 0) :=
    (((show Commute w (L.z (D.delta 0)) from hcomm.symm).pow_left 2).eq).symm
  have hw2β : w ^ 2 • D.beta 0 = D.beta 0 := by
    rw [pow_two, mul_smul, hwβ', hwβ']
  have hc'x : (w ^ 2 * L.z (D.delta 0)) * D.x = D.x * (w ^ 2 * L.z (D.delta 0)) := by
    rw [← mul_inv_eq_iff_eq_mul]
    have h1 := sq_conj_eq_inv hx5 hw
    calc (w ^ 2 * L.z (D.delta 0)) * D.x * (w ^ 2 * L.z (D.delta 0))⁻¹
        = w ^ 2 * (L.z (D.delta 0) * D.x * L.z (D.delta 0)) * (w ^ 2)⁻¹ := by
          rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hz2]
          group
      _ = w ^ 2 * D.x⁻¹ * (w ^ 2)⁻¹ := by rw [hzx]
      _ = (w ^ 2 * D.x * (w ^ 2)⁻¹)⁻¹ := by group
      _ = D.x := by rw [h1, inv_inv]
  have hc' : w ^ 2 * L.z (D.delta 0) ∈ D.calpha :=
    mem_calpha_of_comm h71c D hc'x (by rw [mul_smul, hz0β, hw2β])
  have hw4 : w ^ 4 = (w ^ 2 * L.z (D.delta 0)) * (w ^ 2 * L.z (D.delta 0)) := by
    calc w ^ 4 = w ^ 2 * (w ^ 2 * (L.z (D.delta 0) * L.z (D.delta 0))) := by
          rw [hz2, mul_one]
          group
      _ = w ^ 2 * (L.z (D.delta 0) * w ^ 2) * L.z (D.delta 0) := by
          rw [hcomm2]
          group
      _ = (w ^ 2 * L.z (D.delta 0)) * (w ^ 2 * L.z (D.delta 0)) := by group
  have hK : w ^ 4 ∈ nbrStab Γ G (D.delta 0) :=
    pow_four_mem_nbrStab F (D.adj_xi_delta 0).symm (D.valence_delta F 0) hwδ hwξ
  have hsq : (w ^ 2 * L.z (D.delta 0)) * (w ^ 2 * L.z (D.delta 0)) = 1 := by
    rcases calpha_sq_mem D F h71c h75 hcyc hle hc' with h | h
    · exact h
    · exfalso
      rw [← hw4] at h
      rw [h] at hK
      exact z_not_mem_nbrStab_delta D F h71c hK
  have hw4' : w ^ 4 = 1 := by rw [hw4, hsq]
  have hcases := calpha_involution D F h71c h75 hcyc hc' hsq
  have hw2 : w ^ 2 ≠ 1 := by
    intro h2
    have h1 := sq_conj_eq_inv hx5 hw
    rw [h2] at h1
    have h3 : D.x = D.x⁻¹ := by simpa using h1
    have h22 : D.x ^ 2 = 1 := by
      rw [pow_two]
      exact mul_eq_one_iff_eq_inv.2 h3
    apply D.x_ne_one F
    calc D.x = D.x * (D.x ^ 2) ^ 2 := by rw [h22, one_pow, mul_one]
      _ = D.x ^ 5 := by group
      _ = 1 := hx5
  have hord : orderOf w = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := w) (by simpa using hw2)
      (by simpa using hw4')
    simpa using this
  refine ⟨w, hP, hord, hw, ?_⟩
  have hw2eq : w * w = (w ^ 2 * L.z (D.delta 0)) * L.z (D.delta 0) := by
    calc w * w = w ^ 2 * (L.z (D.delta 0) * L.z (D.delta 0)) := by rw [hz2, mul_one, pow_two]
      _ = (w ^ 2 * L.z (D.delta 0)) * L.z (D.delta 0) := by group
  rcases hcases with h | h
  · left
    rw [hw2eq, h, one_mul]
  · right
    rw [hw2eq, h, ← L.comm_z_of_mem_stabilizer D.val hz0α]

end Sec8P3

end CFSG.Quasithin.Fan86
