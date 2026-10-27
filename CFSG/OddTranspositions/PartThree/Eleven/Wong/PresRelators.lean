module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.RootRelations
public import CFSG.OddTranspositions.PartThree.Eleven.Wong.RootTwist
public import CFSG.ClassicalGroups.Symplectic.PSp45.PresData
public import CFSG.Certificates.CosetTableCompactColumns
public import CFSG.Certificates.CosetTableShort

public section

namespace CFSG.OddTranspositions.PartThree.Wong.RootData

open CFSG.ClassicalGroups.Symplectic.PSp45

variable {G : Type} [Group G] (D : RootData G)

@[expose] def gens : Fin 8 → G :=
  ![D.q1 (.ofAdd 1), D.q2 (.ofAdd 1), D.q3 (.ofAdd 1), D.q4 (.ofAdd 1), D.h1, D.h2, D.u, D.c2]

private theorem pspRels_eq : pspRels =
    [[(0, true), (0, true), (0, true), (0, true), (0, true)],
     [(1, true), (1, true), (1, true), (1, true), (1, true)],
     [(3, true), (3, true), (3, true), (3, true), (3, true)],
     [(0, false), (1, false), (0, true), (1, true)],
     [(0, false), (2, false), (0, true), (2, true)],
     [(0, false), (3, false), (0, true), (3, true)],
     [(1, false), (2, false), (1, true), (2, true)],
     [(3, false), (1, true), (3, true), (2, false), (1, false), (0, true)],
     [(3, false), (2, true), (3, true), (2, false), (0, true), (0, true)],
     [(4, false), (5, false), (4, true), (5, true)],
     [(4, true), (4, true), (5, false), (5, false)],
     [(4, true), (4, true), (4, true), (4, true)],
     [(4, false), (1, true), (4, true), (1, false)],
     [(5, false), (1, true), (5, true), (1, false), (1, false), (1, false), (1, false)],
     [(4, false), (3, true), (4, true), (3, false), (3, false)],
     [(5, false), (3, true), (5, true), (3, false), (3, false), (3, false)],
     [(6, true), (6, true)],
     [(6, false), (0, true), (6, true), (1, false)],
     [(6, false), (4, true), (6, true), (5, false)],
     [(7, false), (2, true), (7, true), (3, false)],
     [(7, true), (1, true), (7, true), (1, true), (7, true), (1, true)],
     [(5, true), (5, true), (6, true), (4, true), (5, true), (3, true), (5, true), (5, true),
      (6, true), (4, true), (5, true), (3, true), (5, true), (5, true), (6, true), (4, true),
      (5, true), (3, true)],
     [(6, true), (7, true), (6, true), (7, true), (6, true), (7, true), (6, true), (7, true)],
     [(5, true), (7, true), (1, false), (1, false), (1, false), (7, false), (1, false), (1, false),
      (7, true), (1, false), (1, false), (1, false)]] := by
  decide

private theorem map_ofAdd_natCast (q : Multiplicative (ZMod 5) →* G) (n : ℕ) :
    q (.ofAdd (n : ZMod 5)) = q (.ofAdd 1) ^ n := by
  rw [← map_pow, ← ofAdd_nsmul, nsmul_one]

theorem constructed_generators_satisfy_relators [Finite G] :
    (∀ r ∈ pspRels, FreeGroup.lift D.gens (FreeGroup.mk r) = 1) ∧ ∃ i, D.gens i ≠ 1 := by
  obtain ⟨h12, h13, h14, h23, h42, h43, -, h1q2, -, h1q4, -, h2q2, -, h2q4, hu1, -, -, -, -, -⟩ :=
    D.exact_root_torus_and_weyl_actions 1 1
  have hpow2 : ∀ q : Multiplicative (ZMod 5) →* G, q (.ofAdd 2) = q (.ofAdd 1) ^ 2 :=
    fun q => map_ofAdd_natCast q 2
  have hpow3 : ∀ q : Multiplicative (ZMod 5) →* G, q (.ofAdd 3) = q (.ofAdd 1) ^ 3 :=
    fun q => map_ofAdd_natCast q 3
  have hpow4 : ∀ q : Multiplicative (ZMod 5) →* G, q (.ofAdd 4) = q (.ofAdd 1) ^ 4 :=
    fun q => map_ofAdd_natCast q 4
  have hpow5 : ∀ q : Multiplicative (ZMod 5) →* G, q (.ofAdd 1) ^ 5 = 1 := fun q => by
    rw [← map_ofAdd_natCast, show ((5 : ℕ) : ZMod 5) = 0 by decide, ofAdd_zero, map_one]
  simp only [one_pow, mul_one] at h42 h43 h1q4 h2q2 h2q4
  rw [ofAdd_neg, map_inv] at h42 h43
  rw [hpow2] at h43 h1q4
  rw [hpow4] at h2q2
  rw [hpow3] at h2q4
  have hh1 : D.h1 ^ 2 = D.t := by
    rw [show D.h1 = D.i1 hM from rfl, ← map_pow, hM_sq, ← D.t_eq_i1]
  have hh2 : D.h2 ^ 2 = D.t := by
    rw [show D.h2 = D.i2 hM from rfl, ← map_pow, hM_sq, ← D.t_eq_i2]
  have hh : Commute D.h1 D.h2 := D.commute hM hM
  have hs : D.u⁻¹ * D.h1 * D.u = D.h2 := D.swap hM
  refine ⟨fun r hr => ?_, 6, ?_⟩
  · rw [pspRels_eq] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [FreeGroup.lift_mk, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, cond_true, cond_false, mul_one, gens, Matrix.cons_val]
    · calc _ = D.q1 (.ofAdd 1) ^ 5 := by
            simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = 1 := hpow5 _
    · calc _ = D.q2 (.ofAdd 1) ^ 5 := by
            simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = 1 := hpow5 _
    · calc _ = D.q4 (.ofAdd 1) ^ 5 := by
            simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = 1 := hpow5 _
    · rw [h12.eq]; group
    · rw [h13.eq]; group
    · rw [h14.eq]; group
    · rw [h23.eq]; group
    · calc _ = ((D.q4 (.ofAdd 1))⁻¹ * D.q2 (.ofAdd 1) * D.q4 (.ofAdd 1)) *
            ((D.q3 (.ofAdd 1))⁻¹ * (D.q2 (.ofAdd 1))⁻¹ * D.q1 (.ofAdd 1)) := by group
        _ = 1 := by rw [h42]; group
    · calc _ = ((D.q4 (.ofAdd 1))⁻¹ * D.q3 (.ofAdd 1) * D.q4 (.ofAdd 1)) *
            ((D.q3 (.ofAdd 1))⁻¹ * D.q1 (.ofAdd 1) * D.q1 (.ofAdd 1)) := by group
        _ = 1 := by rw [h43, pow_two]; group
    · rw [hh.eq]; group
    · calc _ = D.h1 ^ 2 * (D.h2 ^ 2)⁻¹ := by
            simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
        _ = 1 := by rw [hh1, hh2, mul_inv_cancel]
    · calc _ = D.h1 ^ 2 * D.h1 ^ 2 := by
            simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = 1 := by rw [hh1, D.t_mul_t]
    · calc _ = (D.h1⁻¹ * D.q2 (.ofAdd 1) * D.h1) * (D.q2 (.ofAdd 1))⁻¹ := by group
        _ = 1 := by rw [h1q2, mul_inv_cancel]
    · calc _ = (D.h2⁻¹ * D.q2 (.ofAdd 1) * D.h2) * (D.q2 (.ofAdd 1) ^ 4)⁻¹ := by
            simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
        _ = 1 := by rw [h2q2, mul_inv_cancel]
    · calc _ = (D.h1⁻¹ * D.q4 (.ofAdd 1) * D.h1) * (D.q4 (.ofAdd 1) ^ 2)⁻¹ := by
            simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
        _ = 1 := by rw [h1q4, mul_inv_cancel]
    · calc _ = (D.h2⁻¹ * D.q4 (.ofAdd 1) * D.h2) * (D.q4 (.ofAdd 1) ^ 3)⁻¹ := by
            simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
        _ = 1 := by rw [h2q4, mul_inv_cancel]
    · exact D.u_mul_u
    · calc _ = (D.u⁻¹ * D.q1 (.ofAdd 1) * D.u) * (D.q2 (.ofAdd 1))⁻¹ := by group
        _ = 1 := by rw [hu1, mul_inv_cancel]
    · calc _ = (D.u⁻¹ * D.h1 * D.u) * D.h2⁻¹ := by group
        _ = 1 := by rw [hs, mul_inv_cancel]
    · calc _ = (D.c2⁻¹ * D.q3 (.ofAdd 1) * D.c2) * (D.q4 (.ofAdd 1))⁻¹ := by group
        _ = 1 := by rw [← D.q4_ofAdd, mul_inv_cancel]
    · calc _ = (D.c2 * D.q2 (.ofAdd 1)) ^ 3 := by rw [pow_three]; group
        _ = D.i2 ((cM * thetaM 1) ^ 3) := by rw [map_pow, map_mul]; rfl
        _ = 1 := by rw [show (cM * thetaM 1) ^ 3 = 1 by decide, map_one]
    · calc _ = (D.h2 * D.h2 * D.u * (D.h1 * D.h2) * D.q4 (.ofAdd 1)) ^ 3 := by
            rw [pow_three]; group
        _ = (D.t * D.u * D.v * D.q4 (.ofAdd 1)) ^ 3 := by rw [← pow_two, hh2]; rfl
        _ = 1 := D.twist_root_and_weyl_images.2.2
    · have huc : D.u * D.c2 * D.u = D.c1 := by
        rw [show D.u * D.c2 = D.c1 * D.u from D.u_mul_i2 cM, mul_assoc, D.u_mul_u, mul_one]
      calc _ = (D.u * D.c2 * D.u * D.c2) ^ 2 := by rw [pow_two]; group
        _ = D.w ^ 2 := by rw [huc]; rfl
        _ = 1 := by rw [pow_two, D.w_mul_w]
    · rw [show D.h2 = D.i2 hM from rfl, show D.c2 = D.i2 cM from rfl,
        show D.q2 (.ofAdd 1) = D.i2 (thetaM 1) from rfl]
      calc _ = D.i2 (hM * cM * (thetaM 1 ^ 3)⁻¹ * cM⁻¹ * (thetaM 1 ^ 2)⁻¹ * cM *
            (thetaM 1 ^ 3)⁻¹) := by simp only [map_mul, map_inv, map_pow]; group
        _ = 1 := by
          rw [show hM * cM * (thetaM 1 ^ 3)⁻¹ * cM⁻¹ * (thetaM 1 ^ 2)⁻¹ * cM *
            (thetaM 1 ^ 3)⁻¹ = 1 by decide, map_one]
  · intro h
    have h2 := D.orderOf_u
    rw [show D.gens 6 = D.u from rfl] at h
    rw [h, orderOf_one] at h2
    exact absurd h2 (by norm_num)

end CFSG.OddTranspositions.PartThree.Wong.RootData
