module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PGroup.Omega
public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.SectionRank.Ccomm.PGroupBasics

public section

namespace CFSG.LocalAnalysis.SteinbergBV

open Subgroup CFSG CFSG.SectionRank.Ccomm

attribute [local instance] CFSG.omega₁_characteristic

section Model

variable {p a : ℕ}

theorem zmod_p_mul_eq_zero_iff (hp : p.Prime) (ha : 1 ≤ a) (t : ZMod (p ^ a)) :
    (p : ZMod (p ^ a)) * t = 0 ↔
      ∃ m : ZMod (p ^ a), t = ((p ^ (a - 1) : ℕ) : ZMod (p ^ a)) * m := by
  have : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hpa : p ^ a = p * p ^ (a - 1) := by rw [← pow_succ', Nat.sub_add_cancel ha]
  constructor
  · intro h
    rw [← ZMod.natCast_zmod_val t, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at h
    obtain ⟨m, hm⟩ := Nat.dvd_of_mul_dvd_mul_left hp.pos ((dvd_of_eq hpa.symm).trans h)
    exact ⟨m, by rw [← ZMod.natCast_zmod_val t, hm, Nat.cast_mul]⟩
  · rintro ⟨m, rfl⟩
    rw [← mul_assoc, ← Nat.cast_mul, ← hpa, ZMod.natCast_self, zero_mul]

theorem cyclic_pow_eq_one_iff (hp : p.Prime) (ha : 1 ≤ a) (z : Multiplicative (ZMod (p ^ a))) :
    z ^ p = 1 ↔ ∃ w, z = w ^ (p ^ (a - 1)) := by
  rw [← toAdd_eq_zero, toAdd_pow, nsmul_eq_mul, zmod_p_mul_eq_zero_iff hp ha]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨Multiplicative.ofAdd m, Multiplicative.toAdd.injective ?_⟩
    rw [toAdd_pow, toAdd_ofAdd, nsmul_eq_mul]
    exact hm
  · rintro ⟨w, rfl⟩
    exact ⟨w.toAdd, by rw [toAdd_pow, nsmul_eq_mul]⟩

theorem card_cyclic_pow_eq_one (hp : p.Prime) (ha : 1 ≤ a) :
    Nat.card {z : Multiplicative (ZMod (p ^ a)) // z ^ p = 1} = p := by
  have : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hset : {z : Multiplicative (ZMod (p ^ a)) | z ^ p = 1} =
      Multiplicative.ofAdd '' (AddSubgroup.zmultiples ((p ^ (a - 1) : ℕ) : ZMod (p ^ a)) :
        Set (ZMod (p ^ a))) := by
    ext z
    rw [Set.mem_ofPred_eq, cyclic_pow_eq_one_iff hp ha]
    constructor
    · rintro ⟨w, rfl⟩
      refine ⟨(w ^ (p ^ (a - 1))).toAdd,
        (AddSubgroup.mem_zmultiples_iff).2 ⟨((w.toAdd.val : ℕ) : ℤ), ?_⟩, rfl⟩
      rw [toAdd_pow, nsmul_eq_mul, natCast_zsmul, nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm]
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨k, rfl⟩ := (AddSubgroup.mem_zmultiples_iff).1 ht
      refine ⟨Multiplicative.ofAdd (k : ZMod (p ^ a)), Multiplicative.toAdd.injective ?_⟩
      rw [toAdd_pow, toAdd_ofAdd, toAdd_ofAdd, nsmul_eq_mul, zsmul_eq_mul, mul_comm]
  have hord : addOrderOf ((p ^ (a - 1) : ℕ) : ZMod (p ^ a)) = p := by
    rw [ZMod.addOrderOf_coe _ (pow_ne_zero _ hp.ne_zero),
      Nat.gcd_eq_right (pow_dvd_pow p (Nat.sub_le a 1)),
      Nat.pow_div (Nat.sub_le a 1) hp.pos, show a - (a - 1) = 1 by omega, pow_one]
  calc Nat.card {z : Multiplicative (ZMod (p ^ a)) // z ^ p = 1}
      = ({z : Multiplicative (ZMod (p ^ a)) | z ^ p = 1} : Set _).ncard := Nat.card_coe_set_eq _
    _ = (AddSubgroup.zmultiples ((p ^ (a - 1) : ℕ) : ZMod (p ^ a)) :
        Set (ZMod (p ^ a))).ncard := by
      rw [hset, Set.ncard_image_of_injective _ Multiplicative.ofAdd.injective]
    _ = Nat.card (AddSubgroup.zmultiples ((p ^ (a - 1) : ℕ) : ZMod (p ^ a))) :=
      (Nat.card_coe_set_eq _).symm
    _ = p := by rw [Nat.card_zmultiples, hord]

end Model

variable {p a : ℕ}

end CFSG.LocalAnalysis.SteinbergBV
