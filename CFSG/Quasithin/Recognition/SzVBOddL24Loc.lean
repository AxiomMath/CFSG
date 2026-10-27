module

public import CFSG.Quasithin.Recognition.F112WLocal
public import CFSG.Quasithin.Recognition.SzVBLocal

public section

namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T V : Subgroup G}

theorem inf_centralizer_le_T (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hS : F112W.IsNaturalS3 G₁ V)
    (h3 : T.relIndex G₁ = 3) : G₁ ⊓ Subgroup.centralizer (V : Set G) ≤ T := by
  have hQ : pCoreOf 2 G₁ = T ⊓ Subgroup.centralizer (V : Set G) := pCoreOf_eq_inf_centralizer hyp
  have h2 : (T ⊓ Subgroup.centralizer (V : Set G)).relIndex T = 2 := by
    have := F112W.relIndex_pCoreOf_T hyp hS
    rwa [hQ] at this
  have hT1 : T ≤ G₁ := hyp.sylow₁.1
  have hTC : T ⊓ Subgroup.centralizer (V : Set G) ≤ G₁ ⊓ Subgroup.centralizer (V : Set G) :=
    inf_le_inf_right _ hT1
  have e1 := Subgroup.relIndex_mul_relIndex (T ⊓ Subgroup.centralizer (V : Set G)) T G₁
    inf_le_left hT1
  have e2 := Subgroup.relIndex_mul_relIndex (T ⊓ Subgroup.centralizer (V : Set G))
    (G₁ ⊓ Subgroup.centralizer (V : Set G)) G₁ hTC inf_le_left
  rw [h2, h3] at e1
  rw [hS.index_eq] at e2
  have h1 : (T ⊓ Subgroup.centralizer (V : Set G)).relIndex
      (G₁ ⊓ Subgroup.centralizer (V : Set G)) = 1 := by omega
  exact (Subgroup.relIndex_eq_one.mp h1).trans inf_le_left

omit [Finite G] in
theorem commute_of_odd_order {t a z : G} (hz2 : z * z = 1) (hz1 : z ≠ 1) (htz : t * z = z * t)
    (hodd : Odd (orderOf t))
    (h : t * a * t⁻¹ * a⁻¹ = 1 ∨ t * a * t⁻¹ * a⁻¹ = z) : t * a = a * t := by
  rcases h with h | h
  · have h1 : t * a * t⁻¹ = a := by
      have := congrArg (fun w => w * a) h
      simpa [mul_assoc] using this
    calc t * a = t * a * t⁻¹ * t := by group
      _ = a * t := by rw [h1]
  · exfalso
    have hta : t * a * t⁻¹ = z * a := by
      have := congrArg (fun w => w * a) h
      simpa [mul_assoc] using this
    have hzt : ∀ k : ℕ, t * z ^ k * t⁻¹ = z ^ k := by
      intro k
      rw [mul_inv_eq_iff_eq_mul]
      exact (Commute.pow_right (show Commute t z from htz) k).eq
    have key : ∀ k : ℕ, t ^ k * a * (t ^ k)⁻¹ = z ^ k * a := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have e : t ^ (k + 1) * a * (t ^ (k + 1))⁻¹ = t * (t ^ k * a * (t ^ k)⁻¹) * t⁻¹ := by
          rw [pow_succ', mul_inv_rev]
          group
        rw [e, ih]
        calc t * (z ^ k * a) * t⁻¹ = (t * z ^ k * t⁻¹) * (t * a * t⁻¹) := by group
          _ = z ^ k * (z * a) := by rw [hzt, hta]
          _ = z ^ (k + 1) * a := by rw [pow_succ, mul_assoc]
    have h1 := key (orderOf t)
    rw [pow_orderOf_eq_one] at h1
    simp only [inv_one, mul_one, one_mul] at h1
    obtain ⟨j, hj⟩ := hodd
    have hzk : z ^ orderOf t = z := by
      rw [hj, pow_succ, pow_mul, pow_two, hz2, one_pow, one_mul]
    rw [hzk] at h1
    exact hz1 (by
      have := congrArg (fun w => w * a⁻¹) h1
      simpa using this.symm)

omit [Finite G] in
theorem commute_klein_of_odd_order {U : Subgroup G} {z t : G} (hU : IsElemAbelian 2 U)
    (hcard : Nat.card ↥U = 4) (hz : z ∈ U) (hz1 : z ≠ 1) (htz : t * z = z * t)
    (htU : conjSub t U = U) (hodd : Odd (orderOf t)) {a : G} (ha : a ∈ U) : t * a = a * t := by
  have hz2 : z * z = 1 := by
    rw [← pow_two]
    exact F7.isElemAbelian_pow_eq_one hU hz
  exact commute_of_odd_order hz2 hz1 htz hodd (commutator_mem_klein hU hcard hz hz1 htz htU ha)

end CFSG.Quasithin.SzVB
