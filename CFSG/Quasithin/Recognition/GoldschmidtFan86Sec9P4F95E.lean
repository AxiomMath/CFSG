module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Coll
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Tactic.FinCases

public section

namespace CFSG.Quasithin.Fan86

namespace Sec9P4F95Alg

variable {H : Type*} [Group H] {x w za c : H} {y z : Fin 5 → H}

theorem interchange5 {A B C D E A' B' C' D' E' : H} (h1 : Commute A' B) (h2 : Commute A' C)
    (h3 : Commute A' D) (h4 : Commute A' E) (h5 : Commute B' C) (h6 : Commute B' D)
    (h7 : Commute B' E) (h8 : Commute C' D) (h9 : Commute C' E) (h10 : Commute D' E) :
    A * B * C * D * E * (A' * B' * C' * D' * E') =
      A * A' * (B * B') * (C * C') * (D * D') * (E * E') := by
  simp only [mul_assoc]
  rw [h4.symm.left_comm, h3.symm.left_comm, h2.symm.left_comm, h1.symm.left_comm,
    h7.symm.left_comm, h6.symm.left_comm, h5.symm.left_comm, h9.symm.left_comm,
    h8.symm.left_comm, h10.symm.left_comm]

theorem z_commute (hR : P1Rel x w za y z) (i j : Fin 5) : Commute (z i) (z j) :=
  commute_of_fcomm_one (hR.zz j i)

theorem z_commute_za (hR : P1Rel x w za y z) (i : Fin 5) : Commute (z i) za :=
  (commute_of_fcomm_one (hR.cent_z i)).symm

@[expose] def Ee (z : Fin 5 → H) (za : H) (a₀ a₁ a₂ a₃ b : ℕ) : H :=
  z 0 ^ a₀ * z 1 ^ a₁ * z 2 ^ a₂ * z 3 ^ a₃ * za ^ b

theorem Ee_mul (hR : P1Rel x w za y z) (a₀ a₁ a₂ a₃ b a₀' a₁' a₂' a₃' b' : ℕ) :
    Ee z za a₀ a₁ a₂ a₃ b * Ee z za a₀' a₁' a₂' a₃' b' =
      Ee z za (a₀ + a₀') (a₁ + a₁') (a₂ + a₂') (a₃ + a₃') (b + b') := by
  unfold Ee
  rw [interchange5 ((z_commute hR 0 1).pow_pow _ _) ((z_commute hR 0 2).pow_pow _ _)
    ((z_commute hR 0 3).pow_pow _ _) ((z_commute_za hR 0).pow_pow _ _)
    ((z_commute hR 1 2).pow_pow _ _) ((z_commute hR 1 3).pow_pow _ _)
    ((z_commute_za hR 1).pow_pow _ _) ((z_commute hR 2 3).pow_pow _ _)
    ((z_commute_za hR 2).pow_pow _ _) ((z_commute_za hR 3).pow_pow _ _)]
  simp only [pow_add]

theorem pow_add_self_eq_one {g : H} (hg : g ^ 2 = 1) (n : ℕ) : g ^ (n + n) = 1 := by
  rw [← two_mul, pow_mul, hg, one_pow]

theorem Ee_dbl (hR : P1Rel x w za y z) (a₀ a₁ a₂ a₃ b m : ℕ) :
    Ee z za (a₀ + a₀) (a₁ + a₁) (a₂ + a₂) (a₃ + a₃) (b + m + b) = za ^ m := by
  unfold Ee
  rw [pow_add_self_eq_one (hR.z2 0), pow_add_self_eq_one (hR.z2 1),
    pow_add_self_eq_one (hR.z2 2), pow_add_self_eq_one (hR.z2 3),
    show b + m + b = m + (b + b) by omega, pow_add, pow_add_self_eq_one hR.za2]
  simp

theorem Ee_mod (hR : P1Rel x w za y z) (a₀ a₁ a₂ a₃ b : ℕ) :
    Ee z za a₀ a₁ a₂ a₃ b = Ee z za (a₀ % 2) (a₁ % 2) (a₂ % 2) (a₃ % 2) (b % 2) := by
  unfold Ee
  rw [pow_eq_pow_mod a₀ (hR.z2 0), pow_eq_pow_mod a₁ (hR.z2 1), pow_eq_pow_mod a₂ (hR.z2 2),
    pow_eq_pow_mod a₃ (hR.z2 3), pow_eq_pow_mod b hR.za2]

theorem Ee_mul_self (hR : P1Rel x w za y z) (a₀ a₁ a₂ a₃ b : ℕ) :
    Ee z za a₀ a₁ a₂ a₃ b * Ee z za a₀ a₁ a₂ a₃ b = 1 := by
  have := Ee_dbl hR a₀ a₁ a₂ a₃ b 0 (z := z)
  rw [Ee_mul hR, show b + b = b + 0 + b by omega, this, pow_zero]

theorem z_four' (hR : P1Rel x w za y z) : z 4 = Ee z za 1 1 1 1 0 := by
  unfold Ee
  simp only [pow_one, pow_zero, mul_one]
  rw [hR.z_four]
  simp only [mul_assoc]
  rw [(z_commute hR 1 0).eq, (z_commute hR 2 0).left_comm, (z_commute hR 3 0).left_comm,
    (z_commute hR 2 1).eq, (z_commute hR 3 1).left_comm, (z_commute hR 3 2).eq]

def Esub (hR : P1Rel x w za y z) : Subgroup H where
  carrier := {v | ∃ a₀ a₁ a₂ a₃ b : ℕ, v = Ee z za a₀ a₁ a₂ a₃ b}
  mul_mem' := by
    rintro _ _ ⟨a₀, a₁, a₂, a₃, b, rfl⟩ ⟨a₀', a₁', a₂', a₃', b', rfl⟩
    exact ⟨_, _, _, _, _, Ee_mul hR a₀ a₁ a₂ a₃ b a₀' a₁' a₂' a₃' b'⟩
  one_mem' := ⟨0, 0, 0, 0, 0, by simp [Ee]⟩
  inv_mem' := by
    rintro _ ⟨a₀, a₁, a₂, a₃, b, rfl⟩
    exact ⟨a₀, a₁, a₂, a₃, b, inv_eq_of_mul_eq_one_right (Ee_mul_self hR a₀ a₁ a₂ a₃ b)⟩

theorem mem_Esub (hR : P1Rel x w za y z) {v : H} :
    v ∈ Esub hR ↔ ∃ a₀ a₁ a₂ a₃ b : ℕ, v = Ee z za a₀ a₁ a₂ a₃ b := Iff.rfl

theorem z_mem_Esub (hR : P1Rel x w za y z) (j : Fin 5) : z j ∈ Esub hR := by
  rw [mem_Esub]
  fin_cases j
  · exact ⟨1, 0, 0, 0, 0, by simp [Ee]⟩
  · exact ⟨0, 1, 0, 0, 0, by simp [Ee]⟩
  · exact ⟨0, 0, 1, 0, 0, by simp [Ee]⟩
  · exact ⟨0, 0, 0, 1, 0, by simp [Ee]⟩
  · exact ⟨1, 1, 1, 1, 0, z_four' hR⟩

theorem za_mem_Esub (hR : P1Rel x w za y z) : za ∈ Esub hR :=
  ⟨0, 0, 0, 0, 1, by simp [Ee]⟩

end Sec9P4F95Alg

end CFSG.Quasithin.Fan86
