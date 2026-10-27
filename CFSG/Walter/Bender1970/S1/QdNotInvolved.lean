module

public import CFSG.Walter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Definitions
import all CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.PStability

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Walter

open Glauberman

private theorem isPGroup_zpowers_of_pow_four {H : Type*} [Group H] {x : H} (hx : x ^ 4 = 1) :
    IsPGroup 2 (Subgroup.zpowers x) :=
  IsPGroup.of_card_dvd_pow (n := 2) (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hx)

private theorem mul_comm_of_hasAbelianSylow_two {H : Type*} [Group H]
    (hH : BenderSuzuki.HasAbelianSylow 2 H) {x y : H} (hx : x ^ 4 = 1) (hy : y ^ 4 = 1)
    (hyx : y * x = x ^ 3 * y) : x * y = y * x := by
  have hconj : y * x * y⁻¹ = x⁻¹ := by
    rw [hyx, mul_inv_cancel_right]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hx])
  have hnorm : Subgroup.zpowers y ≤ Subgroup.normalizer (Subgroup.zpowers x : Set H) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    simp [MulAut.conj_apply, hconj]
  obtain ⟨S, hS⟩ := ((isPGroup_zpowers_of_pow_four hx).to_sup_of_normal_left'
    (isPGroup_zpowers_of_pow_four hy) hnorm).exists_le_sylow
  have := hH S
  exact setLike_mul_comm (hS (Subgroup.mem_sup_left (Subgroup.mem_zpowers x)))
    (hS (Subgroup.mem_sup_right (Subgroup.mem_zpowers y)))

private def qdI (p : ℕ) : qdSL p :=
  ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two_of]⟩

private def qdJ {p : ℕ} {a b : ZMod p} (hab : a ^ 2 + b ^ 2 = -1) : qdSL p :=
  ⟨!![a, b; b, -a], by rw [Matrix.det_fin_two_of]; linear_combination -hab⟩

private theorem qdI_sq {p : ℕ} : qdI p ^ 2 = -1 := by
  apply Subtype.ext
  change (!![(0 : ZMod p), -1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ 2 = -1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two]

private theorem qdJ_sq {p : ℕ} {a b : ZMod p} (hab : a ^ 2 + b ^ 2 = -1) : qdJ hab ^ 2 = -1 := by
  apply Subtype.ext
  change (!![a, b; b, -a] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ 2 = -1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination hab
  · ring
  · ring
  · linear_combination hab

private theorem qdI_mul_qdJ {p : ℕ} {a b : ZMod p} (hab : a ^ 2 + b ^ 2 = -1) :
    qdI p * qdJ hab = -(qdJ hab * qdI p) := by
  apply Subtype.ext
  change (!![(0 : ZMod p), -1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) * !![a, b; b, -a] =
    -(!![a, b; b, -a] * !![0, -1; 1, 0])
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem neg_one_ne_one_qdSL {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) : -(1 : qdSL p) ≠ 1 := by
  have : Fact (2 < p) := ⟨(Fact.out : p.Prime).two_le.lt_of_ne' hp2⟩
  intro h
  exact ZMod.neg_one_ne_one <| by
    simpa using congrArg (fun A : qdSL p => (A : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0) h

private theorem qdSL_not_injective {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {H : Type*} [Group H]
    (hH : BenderSuzuki.HasAbelianSylow 2 H) (φ : qdSL p →* H) : ¬ Function.Injective φ := by
  intro hφ
  obtain ⟨a, b, hab⟩ := ZMod.sq_add_sq p (-1)
  have hI4 : qdI p ^ 4 = 1 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, qdI_sq, neg_one_sq]
  have hJ4 : qdJ hab ^ 4 = 1 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, qdJ_sq, neg_one_sq]
  have hJI : qdJ hab * qdI p = qdI p ^ 3 * qdJ hab := by
    rw [pow_succ, qdI_sq, neg_one_mul, neg_mul, qdI_mul_qdJ, neg_neg]
  have hcomm : φ (qdI p) * φ (qdJ hab) = φ (qdJ hab) * φ (qdI p) :=
    mul_comm_of_hasAbelianSylow_two hH (by rw [← map_pow, hI4, map_one])
      (by rw [← map_pow, hJ4, map_one]) (by rw [← map_pow, ← map_mul, ← map_mul, hJI])
  rw [← map_mul, ← map_mul] at hcomm
  apply neg_one_ne_one_qdSL hp2
  apply mul_left_cancel (a := qdJ hab * qdI p)
  rw [mul_neg_one, mul_one, ← qdI_mul_qdJ]
  exact hφ hcomm

theorem qd_not_involved_of_hasAbelianSylowTwo {G : Type*} [Group G] [Finite G]
    (hG : HasAbelianSylowTwo G) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ¬ Glauberman.Involved (Glauberman.Qd p) G := by
  rintro ⟨K, N, hN, ⟨e⟩⟩
  have hQ : BenderSuzuki.HasAbelianSylow 2 (K ⧸ N) :=
    (BenderSuzuki.HasAbelianSylow.subgroup hG K).mapSurjective (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N)
  exact qdSL_not_injective hp2 hQ (e.symm.toMonoidHom.comp SemidirectProduct.inr)
    (e.symm.injective.comp SemidirectProduct.inr_injective)

end CFSG.Walter
