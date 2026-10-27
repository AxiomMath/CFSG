module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixIndex
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

universe u

public theorem exists_centralizing_involution_of_even_normalized
    {G : Type u} [Group G] [Finite G]
    (D : Subgroup G) {y : G} (hy : IsInvolution y)
    (hyN : y ∈ Subgroup.normalizer (D : Set G))
    (heven : Even (Nat.card D)) :
    ∃ s : G, IsInvolution s ∧ s ∈ D ∧ s * y = y * s := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hy2 : y * y = 1 := by simpa [pow_two] using hy.2
  obtain ⟨T, hTinv⟩ := exists_invariant_sylow_two_of_involutive_normalizer_t26 D hyN hy2
  have h2dvd : 2 ∣ Nat.card D := by
    rcases heven with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  have hTcard : Nat.card (T : Subgroup D) =
      2 ^ (Nat.card D).factorization 2 := by
    simpa using T.card_eq_multiplicity
  have hfacpos : 0 < (Nat.card D).factorization 2 := by
    apply (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
      (Nat.card_pos (α := D)).ne').mp
    exact h2dvd
  have hTne : (T : Subgroup D) ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card (T : Subgroup D) = 1 := by
      rw [hbot]
      simp
    have hpone : 2 ^ (Nat.card D).factorization 2 = 1 := by
      rw [← hTcard, hcard]
    have hfaczero : (Nat.card D).factorization 2 = 0 := by
      rcases (Nat.pow_eq_one).mp hpone with h | h
      · norm_num at h
      · exact h
    omega
  let : Fintype T := Fintype.ofFinite T
  let : Nontrivial T :=
    (Subgroup.nontrivial_iff_ne_bot (T : Subgroup D)).mpr hTne
  obtain ⟨z, hzord, hzcent⟩ := BenderGlauberman.exists_central_involution T.isPGroup'
  let a : G := (z : D)
  have haD : a ∈ D := (z : D).2
  have ha2 : a * a = 1 := by
    have haord : orderOf a = 2 := by
      simpa [a] using
        (Subgroup.orderOf_coe (z : D)).trans
          ((Subgroup.orderOf_coe z).trans hzord)
    have hpow : a ^ 2 = 1 := by
      rw [← haord]
      exact pow_orderOf_eq_one a
    simpa [pow_two] using hpow
  have haI : IsInvolution a := by
    exact ⟨by
      intro ha1
      have haord : orderOf a = 2 := by simpa [a] using hzord
      rw [ha1, orderOf_one] at haord
      omega, by simpa [pow_two] using ha2⟩
  let bD : D := ⟨y * a * y⁻¹, ((Subgroup.mem_normalizer_iff.mp hyN) a).mp haD⟩
  let b : G := (bD : G)
  have hb2 : b * b = 1 := by
    dsimp [b, bD]
    calc
      (y * a * y⁻¹) * (y * a * y⁻¹) = y * (a * a) * y⁻¹ := by group
      _ = 1 := by rw [ha2]; simp
  have hbI : IsInvolution b := by
    refine ⟨?_, by simpa [pow_two] using hb2⟩
    intro hb1
    apply haI.1
    calc
      a = y⁻¹ * b * y := by
        dsimp [b, bD]
        group
      _ = 1 := by rw [hb1]; simp
  have hbT : bD ∈ T := by
    simpa [bD, b] using hTinv (z : D) z.2
  have hab : a * b = b * a := by
    have hzc' := (Subgroup.mem_center_iff.mp hzcent) ⟨bD, hbT⟩
    have habD : (z : D) * bD = bD * (z : D) :=
      congrArg (fun q : T => (q : D)) hzc'.symm
    have hab0 := congrArg (fun q : D => (q : G)) habD
    simpa [a, b] using hab0
  by_cases hw : a * b = 1
  · refine ⟨a, haI, haD, ?_⟩
    have hba : b = a := by
      calc
        b = 1 * b := by simp
        _ = (a * b) * b := by simpa [hw]
        _ = a * (b * b) := by simp [mul_assoc]
        _ = a := by rw [hb2]; simp
    have hfix : y * a * y⁻¹ = a := by simpa [b, bD, hba]
    have hfix' := congrArg (fun t : G => t * y) hfix
    have hcomm : y * a = a * y := by simpa [mul_assoc] using hfix'
    exact hcomm.symm

  · let w : G := a * b
    have hwD : w ∈ D := D.mul_mem haD bD.2
    have hw2 : w * w = 1 := by
      dsimp [w]
      calc
        (a * b) * (a * b) = a * (b * a) * b := by simp [mul_assoc]
        _ = a * (a * b) * b := by rw [hab]
        _ = a * a * (b * b) := by group
        _ = 1 := by rw [ha2, hb2]; simp
    have hwI : IsInvolution w := ⟨hw, by simpa [pow_two] using hw2⟩
    refine ⟨w, hwI, hwD, ?_⟩
    have hconj : y * w * y⁻¹ = w := by
      dsimp [w]
      have hby : y * b * y⁻¹ = a := by
        dsimp [b, bD]
        rw [show y⁻¹ = y from inv_eq_of_mul_eq_one_right hy2]
        calc
          y * (y * a * y) * y = (y * y) * a * (y * y) := by group
          _ = a := by rw [hy2]; simp
      calc
        y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
        _ = b * a := by rw [show y * a * y⁻¹ = b by rfl, hby]
        _ = a * b := hab.symm
    have hconj' := congrArg (fun t : G => t * y) hconj
    have hcomm : y * w = w * y := by simpa [mul_assoc] using hconj'
    exact hcomm.symm


end CFSG.GorensteinWalter

