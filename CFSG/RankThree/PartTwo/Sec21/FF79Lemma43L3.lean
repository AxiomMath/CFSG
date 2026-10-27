module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma43KFacts
public import CFSG.LieType.SteinbergBRAutGL32

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open Matrix CFSG.LieType.SteinbergBR.AutGL32 CFSG.QuasithinUnique.Setup.Family

private abbrev M3 : Type := Matrix (Fin 3) (Fin 3) (ZMod 2)

private def mul3 (A B : M3) : M3 :=
  Matrix.of fun i j => A i 0 * B 0 j + A i 1 * B 1 j + A i 2 * B 2 j

private theorem mul3_eq (A B : M3) : mul3 A B = A * B := by
  ext i j
  simp [mul3, Matrix.mul_apply, Fin.sum_univ_three, add_assoc]

private def pow8 (M : M3) : M3 :=
  let B := mul3 M M
  let C := mul3 B B
  mul3 C C

private theorem pow8_eq (M : M3) : pow8 M = M ^ 8 := by
  have : M ^ 8 = (M * M) * (M * M) * ((M * M) * (M * M)) := by
    rw [show (8 : ℕ) = 2 + 2 + 2 + 2 by norm_num, pow_add, pow_add, pow_add, pow_two]
    simp only [mul_assoc]
  rw [this, pow8]
  simp only [mul3_eq]

private def det3 (A : M3) : ZMod 2 :=
  A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1 - A 0 1 * A 1 0 * A 2 2 + A 0 1 * A 1 2 * A 2 0
    + A 0 2 * A 1 0 * A 2 1 - A 0 2 * A 1 1 * A 2 0

private theorem det3_eq (A : M3) : det3 A = A.det := (Matrix.det_fin_three A).symm

private def adj3 (A : M3) : M3 :=
  !![A 1 1 * A 2 2 - A 1 2 * A 2 1, -(A 0 1 * A 2 2) + A 0 2 * A 2 1,
      A 0 1 * A 1 2 - A 0 2 * A 1 1;
    -(A 1 0 * A 2 2) + A 1 2 * A 2 0, A 0 0 * A 2 2 - A 0 2 * A 2 0,
      -(A 0 0 * A 1 2) + A 0 2 * A 1 0;
    A 1 0 * A 2 1 - A 1 1 * A 2 0, -(A 0 0 * A 2 1) + A 0 1 * A 2 0,
      A 0 0 * A 1 1 - A 0 1 * A 1 0]

private theorem adj3_eq (A : M3) : adj3 A = A.adjugate := (Matrix.adjugate_fin_three A).symm

private def comm3 (c k : M3) : M3 := mul3 (mul3 (mul3 c k) (adj3 c)) (adj3 k)

private def fix3 (A g : M3) : Prop := mul3 (mul3 A (adj3 g)ᵀ) (adj3 A) = g

private instance (A g : M3) : Decidable (fix3 A g) := by unfold fix3; infer_instance

private theorem fact_trivial : ∀ k : M3, det3 k = 1 → k ≠ 1 → pow8 k = 1 →
    ∃ c : M3, det3 c = 1 ∧ pow8 (comm3 c k) ≠ 1 := by
  decide +kernel

private theorem fact_inner : ∀ A β : M3, det3 A = 1 → mul3 A A = 1 → det3 β = 1 → β ≠ 1 →
    mul3 β (mul3 β β) = 1 → mul3 A β = mul3 β A → A = 1 := by
  decide +kernel

private theorem fact_outer : ∀ A : M3, det3 A = 1 → mul3 A (adj3 A)ᵀ = 1 →
    ∀ k : M3, det3 k = 1 → fix3 A k → k ≠ 1 → pow8 k = 1 →
      ∃ c : M3, det3 c = 1 ∧ fix3 A c ∧ pow8 (comm3 c k) ≠ 1 := by
  decide +kernel


private abbrev G3 : Type := GL (Fin 3) (ZMod 2)

private theorem det3_units (g : G3) : det3 (g : M3) = 1 := by
  rw [det3_eq]
  have h1 : Matrix.GeneralLinearGroup.det g = 1 := Subsingleton.elim _ _
  simpa using congrArg (fun u : (ZMod 2)ˣ => (u : ZMod 2)) h1

private theorem inv_val (g : G3) : ((g⁻¹ : G3) : M3) = adj3 (g : M3) := by
  have h1 : (g : M3) * adj3 (g : M3) = 1 := by
    rw [adj3_eq, Matrix.mul_adjugate, ← det3_eq, det3_units, one_smul]
  calc ((g⁻¹ : G3) : M3) = ((g⁻¹ : G3) : M3) * ((g : M3) * adj3 (g : M3)) := by rw [h1, mul_one]
    _ = adj3 (g : M3) := by
      rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

private def ofDet (M : M3) (h : det3 M = 1) : G3 :=
  ⟨M, adj3 M, by rw [adj3_eq, Matrix.mul_adjugate, ← det3_eq, h, one_smul],
    by rw [adj3_eq, Matrix.adjugate_mul, ← det3_eq, h, one_smul]⟩

private theorem ofDet_val (M : M3) (h : det3 M = 1) : (ofDet M h : M3) = M := rfl

private theorem comm_val (c k : G3) :
    ((c * k * c⁻¹ * k⁻¹ : G3) : M3) = comm3 (c : M3) (k : M3) := by
  simp only [comm3, mul3_eq, Units.val_mul, inv_val]

private theorem card_G3 : Nat.card G3 = 168 := card_GL32

private theorem is2El_iff (x : G3) : Is2El x ↔ pow8 (x : M3) = 1 := by
  have key : x ^ 8 = 1 ↔ pow8 (x : M3) = 1 := by
    rw [pow8_eq, ← Units.val_pow_eq_pow_val, ← Units.val_one (α := M3), Units.val_inj]
  rw [← key]
  constructor
  · rintro ⟨m, hm⟩
    have h1 : orderOf x ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm
    have h2 : orderOf x ∣ 168 := card_G3 ▸ orderOf_dvd_natCard x
    obtain ⟨j, hj, hjx⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
    have hj3 : j ≤ 3 := by
      by_contra hc
      have h16 : 2 ^ 4 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
      have := (hjx ▸ h2 : 2 ^ j ∣ 168)
      have := (h16.trans this)
      omega
    exact orderOf_dvd_iff_pow_eq_one.1
      (hjx ▸ (pow_dvd_pow 2 hj3 : 2 ^ j ∣ 2 ^ 3))
  · exact fun h => ⟨3, h⟩

private theorem outer_val (s g : G3) :
    (((MulAut.conj s * tau) g : G3) : M3) =
      mul3 (mul3 (s : M3) (adj3 (g : M3))ᵀ) (adj3 (s : M3)) := by
  simp only [MulAut.mul_apply, MulAut.conj_apply, Units.val_mul, tau_val, inv_val, mul3_eq]

theorem ff79KO2L3_holds : FF79KO2L3 := by
  intro φ hφ β hβ hβφ k hkφ hk1 hk2
  have hβ3 : β ^ 3 = 1 := by
    have := pow_orderOf_eq_one β
    rwa [hβ] at this
  have hβ1 : β ≠ 1 := fun h => by simp [h] at hβ
  have hk8 := (is2El_iff k).1 hk2
  have hk1' : (k : M3) ≠ 1 := fun h => hk1 (Units.ext h)
  rcases aut_GL32_cases φ with ⟨s, rfl⟩ | ⟨s, rfl⟩
  · have hs2 : s * s = 1 := by
      apply CFSG.LieType.SteinbergBR.AutGL32.conj_injective
      rw [map_mul, map_one]
      exact hφ
    have hsβ : s * β = β * s := by
      have := hβφ
      rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at this
      exact this
    have hs1 : s = 1 := by
      have := fact_inner (s : M3) (β : M3) (det3_units s)
        (by rw [mul3_eq, ← Units.val_mul, hs2, Units.val_one]) (det3_units β)
        (fun h => hβ1 (Units.ext h))
        (by
          rw [mul3_eq, mul3_eq]
          have := congrArg Units.val ((pow_three β).symm.trans hβ3)
          simpa only [Units.val_mul, Units.val_one] using this)
        (by rw [mul3_eq, mul3_eq, ← Units.val_mul, ← Units.val_mul, hsβ])
      exact Units.ext this
    subst hs1
    obtain ⟨c, hc, hcc⟩ := fact_trivial (k : M3) (det3_units k) hk1' hk8
    refine ⟨ofDet c hc, by simp, ?_⟩
    rw [is2El_iff, comm_val, ofDet_val]
    exact hcc
  · have hconj : MulAut.conj (s * tau s) = MulAut.conj 1 := by
      rw [map_mul, map_one]
      calc MulAut.conj s * MulAut.conj (tau s)
          = MulAut.conj s * tau * (MulAut.conj s * tau) := by
            rw [mul_assoc (MulAut.conj s) tau (MulAut.conj s * tau),
              ← mul_assoc tau (MulAut.conj s) tau, tau_mul_conj,
              mul_assoc (MulAut.conj (tau s)) tau tau, tau_mul_tau, mul_one]
        _ = 1 := hφ
    have hst : s * tau s = 1 := CFSG.LieType.SteinbergBR.AutGL32.conj_injective hconj
    have hA : mul3 (s : M3) (adj3 (s : M3))ᵀ = 1 := by
      have := congrArg Units.val hst
      simpa only [Units.val_mul, Units.val_one, tau_val, inv_val, mul3_eq] using this
    have hfix : fix3 (s : M3) (k : M3) := by
      have := congrArg Units.val hkφ
      rwa [outer_val] at this
    obtain ⟨c, hc, hcf, hcc⟩ := fact_outer (s : M3) (det3_units s) hA (k : M3) (det3_units k)
      hfix hk1' hk8
    refine ⟨ofDet c hc, Units.ext (by rw [outer_val, ofDet_val]; exact hcf), ?_⟩
    rw [is2El_iff, comm_val, ofDet_val]
    exact hcc

end CFSG.RankThree.PartTwo.Sec21.FF79
