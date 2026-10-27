module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKZ3Def

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

private def s16k_z3odd_omega : S16kGL6 :=
  Units.mk (s16kBlockMat 0 * s16kBlockMat 1 * s16kBlockMat 2)
    ((s16kBlockMat 0 * s16kBlockMat 1 * s16kBlockMat 2) *
      (s16kBlockMat 0 * s16kBlockMat 1 * s16kBlockMat 2))
    (by decide) (by decide)

private theorem s16k_z3odd_omega_val :
    (s16k_z3odd_omega : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      s16kBlockMat 0 * s16kBlockMat 1 * s16kBlockMat 2 := rfl

private theorem s16k_z3odd_omega_pow_three : s16k_z3odd_omega ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, s16k_z3odd_omega_val]
  decide

private theorem s16k_z3odd_omega_ne_one : s16k_z3odd_omega ≠ 1 := by
  intro h
  have h' : s16kBlockMat 0 * s16kBlockMat 1 * s16kBlockMat 2 =
      (1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
    have := congrArg (fun u : S16kGL6 => (u : Matrix (Fin 6) (Fin 6) (ZMod 2))) h
    simpa [s16k_z3odd_omega_val] using this
  exact (by decide : s16kBlockMat 0 * s16kBlockMat 1 * s16kBlockMat 2 ≠
    (1 : Matrix (Fin 6) (Fin 6) (ZMod 2))) h'

private theorem s16k_z3odd_omega_orderOf : orderOf s16k_z3odd_omega = 3 := by
  have hdvd : orderOf s16k_z3odd_omega ∣ 3 :=
    orderOf_dvd_iff_pow_eq_one.mpr s16k_z3odd_omega_pow_three
  rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) s16k_z3odd_omega_ne_one
  · exact h

private theorem s16k_z3odd_scal_eq_zpowers :
    s16kScal = Subgroup.zpowers s16k_z3odd_omega := by
  rw [s16kScal, Subgroup.zpowers_eq_closure]
  congr 1
  ext u
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    exact Units.ext (h.trans s16k_z3odd_omega_val.symm)
  · intro h
    rw [h]
    exact s16k_z3odd_omega_val

private theorem s16k_z3odd_eq_one_of_conj_eq_one {G : Type*} [Group G] {g x : G}
    (h : g * x * g⁻¹ = 1) : x = 1 := by
  have h1 : g⁻¹ * (g * x * g⁻¹) * g = x := by group
  rw [h, mul_one, inv_mul_cancel] at h1
  exact h1.symm

private theorem s16k_z3odd_not_conj_sq {G : Type*} [Group G] {g x : G}
    (h2 : g * x * g⁻¹ = x ^ 2) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hodd : Odd (orderOf g)) : False := by
  have hg2 : g ^ 2 * x * (g ^ 2)⁻¹ = x := by
    calc g ^ 2 * x * (g ^ 2)⁻¹ = g * (g * x * g⁻¹) * g⁻¹ := by
          simp only [pow_two, mul_inv_rev, mul_assoc]
      _ = g * x ^ 2 * g⁻¹ := by rw [h2]
      _ = (g * x * g⁻¹) ^ 2 := (conj_pow).symm
      _ = (x ^ 2) ^ 2 := by rw [h2]
      _ = x := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by omega, pow_succ, hx3, one_mul]
  have hg2_comm : g ^ 2 * x = x * g ^ 2 := by
    have h := congrArg (fun y => y * g ^ 2) hg2
    simpa [mul_assoc, inv_mul_cancel] using h
  obtain ⟨k, hk⟩ := hodd
  have hg_eq : g = (g ^ 2) ^ (k + 1) := by
    rw [← pow_mul]
    rw [show 2 * (k + 1) = orderOf g + 1 by omega]
    rw [pow_succ, pow_orderOf_eq_one, one_mul]
  have hcomm : Commute g x := by
    rw [hg_eq]
    exact (show Commute (g ^ 2) x from hg2_comm).pow_left (k + 1)
  have hconj_id : g * x * g⁻¹ = x := by
    rw [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hx2 : x ^ 2 = x := by
    rw [← h2]
    exact hconj_id
  have hx1' : x = 1 := by
    have h := congrArg (fun y => x⁻¹ * y) hx2
    rw [inv_mul_cancel] at h
    rw [pow_two, ← mul_assoc, inv_mul_cancel, one_mul] at h
    exact h
  exact hx1 hx1'

theorem s16k_z3_odd_cent {g : S16kGL6}
    (hg : g ∈ Subgroup.normalizer (s16kScal : Set S16kGL6)) (hodd : Odd (orderOf g)) :
    g ∈ Subgroup.centralizer (s16kScal : Set S16kGL6) := by
  have hxS : s16k_z3odd_omega ∈ s16kScal := by
    rw [s16k_z3odd_scal_eq_zpowers]
    exact Subgroup.mem_zpowers s16k_z3odd_omega
  have hconj : g * s16k_z3odd_omega * g⁻¹ ∈ s16kScal :=
    ((Subgroup.mem_normalizer_iff.mp hg) s16k_z3odd_omega).mp hxS
  rw [s16k_z3odd_scal_eq_zpowers] at hconj
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hconj
  rw [← zpow_mod_orderOf s16k_z3odd_omega n, s16k_z3odd_omega_orderOf] at hn
  simp only [Nat.cast_ofNat] at hn
  have h0 : 0 ≤ n % 3 := Int.emod_nonneg n (by omega)
  have hlt : n % 3 < 3 := Int.emod_lt_of_pos n (by omega)
  have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  have hcomm : Commute g s16k_z3odd_omega := by
    rcases hcases with h | h | h
    · exfalso
      rw [h, zpow_zero] at hn
      exact s16k_z3odd_omega_ne_one (s16k_z3odd_eq_one_of_conj_eq_one hn.symm)
    · rw [h, zpow_one] at hn
      change g * s16k_z3odd_omega = s16k_z3odd_omega * g
      have hxg : s16k_z3odd_omega * g = g * s16k_z3odd_omega := by
        conv_lhs => rw [hn]
        group
      exact hxg.symm
    · exfalso
      rw [h] at hn
      have hn' : g * s16k_z3odd_omega * g⁻¹ = s16k_z3odd_omega ^ 2 := by
        simpa using hn.symm
      exact s16k_z3odd_not_conj_sq hn' s16k_z3odd_omega_pow_three
        s16k_z3odd_omega_ne_one hodd
  rw [s16k_z3odd_scal_eq_zpowers, Subgroup.mem_centralizer_iff]
  intro h hh
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hh
  rw [← hm]
  exact (hcomm.zpow_right m).symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
