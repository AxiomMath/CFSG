module

public import CFSG.Quasithin.Vol2.Ch11SecBK7D
public import CFSG.Quasithin.Vol2.Ch11SecBK7I

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin Matrix
open CFSG.Quasithin.Vol2.KGNat
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.ClassicalInvolution.ModelFacts.OddCover (qSp qSp_mul qSp_zero)
open scoped IsMulCommutative

namespace K7

variable {K : Type} [Field K]

theorem trv_e0 (c : K) : trv (vec4 1 0 0 0) c = qSp (-c) 0 0 :=
  sp_ext fun x => by
    rw [trv_mulVec, qSp_mulVec, toBilin'_spJ_apply]
    refine vec4_eq ?_ ?_ ?_ ?_ <;> simp [Fin.sum_univ_two, vec4]

theorem trv_e1 (c : K) : trv (vec4 0 1 0 0) c = qSp 0 0 (-c) :=
  sp_ext fun x => by
    rw [trv_mulVec, qSp_mulVec, toBilin'_spJ_apply]
    refine vec4_eq ?_ ?_ ?_ ?_ <;> simp [Fin.sum_univ_two, vec4]

theorem qSp_mul_inv (x y z x' y' z' : K) :
    qSp x y z * (qSp x' y' z')⁻¹ = qSp (x - x') (y - y') (z - z') := by
  rw [mul_inv_eq_iff_eq_mul, qSp_mul, sub_add_cancel, sub_add_cancel, sub_add_cancel]

theorem conjV_one {G : Type} [Group G] (V : Subgroup G) (h : (1 : G) ∈ Subgroup.normalizer
    (V : Set G)) : SecA.conjV V 1 h = 1 := by
  ext v
  rw [SecA.conjV_apply_coe, one_mul, inv_one, mul_one, MulAut.one_apply]

theorem comm_eq_of_fix {W : Type*} [CommGroup W] {x : MulAut W} {v v₂ : W}
    (h : x (v * v₂⁻¹) = v * v₂⁻¹) : x v * v⁻¹ = x v₂ * v₂⁻¹ := by
  have e : x v = v * v₂⁻¹ * x v₂ := by
    rw [← h, ← map_mul, inv_mul_cancel_right]
  rw [e, mul_comm (v * v₂⁻¹) (x v₂), mul_assoc, mul_comm v v₂⁻¹, mul_assoc,
    mul_inv_cancel, mul_one]

variable {G : Type} [Group G] {V : Subgroup G} [IsMulCommutative ↥V]
  {H : Subgroup (MulAut ↥V)} {Z : Subgroup ↥V} {π : ↥(StatedSp 2 K) →* ↥H}
  {f : ↥V → (Fin 2 ⊕ Fin 2 → K)}

theorem mem_centralizer_iff_of_trv [CharP K 2]
    (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z)
    {e : G} (he : e ∈ Subgroup.normalizer (V : Set G)) {y : Fin 2 ⊕ Fin 2 → K} (hy : y ≠ 0)
    {d : K} (hd : d ≠ 0) (hed : SecA.conjV V e he = ((π (trv y d) : ↥H) : MulAut ↥V))
    (u : ↥V) : (u : G) ∈ Subgroup.centralizer ({e} : Set G) ↔
      Matrix.toBilin' (spJ K) (f u) y = 0 := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    apply bil_eq_zero_of_trv_fix hf hy hd
    rw [← hed]
    exact Subtype.ext (by rw [SecA.conjV_apply_coe, ← h, mul_inv_cancel_right])
  · intro h
    have h1 := trv_fix hf hZ hy d h
    rw [← hed] at h1
    have h2 := congrArg Subtype.val h1
    rw [SecA.conjV_apply_coe] at h2
    calc (u : G) * e = e * u * e⁻¹ * e := by rw [h2]
      _ = e * u := by group

theorem mQuot_singleton_eq [CharP K 2] (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f)
    (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z) {n : ℕ} (hK : Nat.card K = 2 ^ n) {e : G}
    (he : e ∈ Subgroup.normalizer (V : Set G)) {y : Fin 2 ⊕ Fin 2 → K} (hy : y ≠ 0) {d : K}
    (hd : d ≠ 0) (hed : SecA.conjV V e he = ((π (trv y d) : ↥H) : MulAut ↥V)) :
    E3.mQuot V (V ⊓ Subgroup.centralizer ({e} : Set G)) = n :=
  mQuot_eq_of_iff hf hK hy (mem_centralizer_iff_of_trv hf hZ he hy hd hed)

end K7

end CFSG.Quasithin.Vol2.Ch11.SecB
