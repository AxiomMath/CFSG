module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4B
public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4C
public import CFSG.Quasithin.Vol2.KGNatLevi
public import CFSG.Quasithin.Vol2.KGNatSp4Std

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A

open Matrix CFSG.Quasithin CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.Quasithin.Vol2.KGNat (qSp_mem_Usp nSp_mem_Usp)

variable {K : Type} [Field K]

theorem lSp_dGL_one_eq (c : Kˣ) : lSp K (dGL (1, c)) = torusHom ![1, c] := by
  apply statedSp_ext
  change mat 2 K (lSp K (dGL (1, c))) = spMat (torusHom ![1, c])
  rw [mat_lSp, spMat_torusHom, ← map_inv, coe_dGL, coe_dGL]
  ext (i | i) (k | k) <;> fin_cases i <;> fin_cases k <;> simp

theorem comm_mem_N0 {a b : StatedSp 2 K} (ha : a ∈ perfectCore (Q2 K 0)) (hb : b ∈ Q2 K 0) :
    a * b * a⁻¹ * b⁻¹ ∈ perfectCore (Q2 K 0) := by
  have h1 := (Subgroup.mem_normalizer_iff.mp (mem_normalizer_N 0 hb) a⁻¹).mp (inv_mem ha)
  rw [show a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) by group]
  exact mul_mem ha h1

variable [Finite K]

theorem mem_Q2_of_mem_Usp (j : Fin 2) {u : StatedSp 2 K} (hu : u ∈ Usp K) : u ∈ Q2 K j := by
  have hj := j.isLt
  rw [Usp_eq_unipotent] at hu
  rw [Q2_eq]
  exact borelSubgroup_le_flagStabilizer (fun x hx => by
    rw [Set.mem_singleton_iff] at hx
    omega) (unipotent_le_borelSubgroup hu)

variable [CharP K 2]

theorem usp_le_perfectCore (hK4 : ∃ s : Finset K, s.card = 4) :
    Usp K ≤ perfectCore (Q2 K 0) := by
  have hcard : 4 ≤ Nat.card K := by
    obtain ⟨s, hs⟩ := hK4
    have := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card, ← hs]
    exact Finset.card_le_univ s
  obtain ⟨c, hc⟩ : ∃ c : Kˣ, c ≠ 1 := by
    have h3 : 1 < Nat.card Kˣ := by rw [Nat.card_units]; omega
    have : Nontrivial Kˣ := Finite.one_lt_card_iff_nontrivial.mp h3
    exact exists_ne 1
  have hc1 : (c : K) - 1 ≠ 0 := sub_ne_zero.mpr fun h => hc (Units.ext h)
  have hc0 : (c : K) ≠ 0 := c.ne_zero
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hc2 : (c : K) ^ 2 - 1 ≠ 0 := by
    intro h
    apply hc1
    have : ((c : K) - 1) ^ 2 = 0 := by linear_combination h - ((c : K) - 1) * h2
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this
  have hci : (c : K)⁻¹ - 1 ≠ 0 := by
    intro h
    apply hc1
    have : (c : K)⁻¹ = 1 := sub_eq_zero.mp h
    rw [inv_eq_one] at this
    rw [this, sub_self]
  have hd : lSp K (dGL (1, c)) ∈ perfectCore (Q2 K 0) := by
    rw [lSp_dGL_one_eq]
    exact (torusHom_mem_N0_iff hK4 _).mpr rfl
  have alg : ∀ a s : K, a - 1 ≠ 0 → s = a * (s * (a - 1)⁻¹) + -(s * (a - 1)⁻¹) :=
    fun a s ha => by
      calc s = s * ((a - 1)⁻¹ * (a - 1)) := by rw [inv_mul_cancel₀ ha, mul_one]
        _ = a * (s * (a - 1)⁻¹) + -(s * (a - 1)⁻¹) := by ring
  have hn : ∀ r : K, nSp r ∈ perfectCore (Q2 K 0) := by
    intro r
    have h1 := comm_mem_N0 hd (mem_Q2_of_mem_Usp 0 (nSp_mem_Usp (r * ((c : K)⁻¹ - 1)⁻¹)))
    rw [lSp_dGL_conj_nSp, nSp_inv, ← nSp_add] at h1
    convert h1 using 2
    simp only [Units.val_one, one_mul]
    exact alg _ r hci
  have hq : ∀ y z : K, qSp 0 y z ∈ perfectCore (Q2 K 0) := by
    intro y z
    have h1 := comm_mem_N0 hd (mem_Q2_of_mem_Usp 0
      (qSp_mem_Usp 0 (y * ((c : K) - 1)⁻¹) (z * ((c : K) ^ 2 - 1)⁻¹)))
    rw [lSp_dGL_conj_qSp, qSp_inv, qSp_mul] at h1
    convert h1 using 2
    · simp
    · simp only [Units.val_one, one_mul]
      exact alg _ y hc1
    · exact alg _ z hc2
  have hqx : ∀ x : K, qSp x 0 0 ∈ perfectCore (Q2 K 0) := by
    intro x
    have h1 : nSp 1 * qSp 0 0 x * (nSp 1)⁻¹ ∈ perfectCore (Q2 K 0) :=
      mul_mem (mul_mem (hn 1) (hq 0 x)) (inv_mem (hn 1))
    rw [nSp_conj_qSp] at h1
    have h2 := mul_mem h1 (hq (-x) (-x))
    rw [qSp_mul] at h2
    convert h2 using 2 <;> ring
  rintro _ ⟨x, y, z, r, rfl⟩
  have e : qSp x y z = qSp x 0 0 * qSp 0 y z := by rw [qSp_mul]; congr 1 <;> ring
  rw [e]
  exact mul_mem (mul_mem (hqx x) (hq y z)) (hn r)

end CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
