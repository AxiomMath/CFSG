
module

public import CFSG.Sporadic.Schreier.J4SOdd276Base1

public import CFSG.Sporadic.Schreier.J4SOddLocal
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SFive
public import CFSG.Sporadic.Schreier.J4SPointwise
public meta import CFSG.Sporadic.J4.PrimSpec
public import Certificates.Certificate2177
public import CFSG.Sporadic.Schreier.J4SOddData
public meta import CFSG.Sporadic.Schreier.J4SOddData
public import CFSG.Sporadic.Schreier.J4SOrbits
public meta import CFSG.Sporadic.Schreier.J4SOrbits
public import CFSG.Sporadic.Schreier.J4SPrimes
public meta import CFSG.Sporadic.Schreier.J4SPrimes
public import CFSG.Sporadic.Schreier.J4SThreeDataInputs
public meta import CFSG.Sporadic.Schreier.J4SKCent
public import CFSG.Sporadic.J4.Local

public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2.Native

theorem a276_pow :
    a276 ^ 11 = 1 := by
  have h := actsBy_pow 11 a276_acts
  rw [a276_check.2.1] at h
  exact eq_one_of_actsBy_id (K.pow_mem a276_mem_K 11) h

theorem oddCore_centralizer_η14 :
    CFSG.oddCore (Subgroup.centralizer ({η 14} : Set J)) = ⊥ := by
  have ht : η 14 ∈ N := η_mem_N 14
  set C := Subgroup.centralizer ({η 14} : Set J) with hC
  set R := oddCoreImage C with hR
  apply oddCore_eq_bot_of_oddCoreImage
  have hRodd : Odd (Nat.card R) := odd_card_oddCoreImage C
  have hHt : Nat.card (H ⊓ C : Subgroup J) * 276 = Nat.card H :=
    card_H_inf_centralizer ht QT_unique_J4_local_normal_module_irreducible.2.2.2.2.1
  have hdvd := card_oddCoreImage_mul_dvd ht
  have hHt' : Nat.card (H ⊓ C : Subgroup J) = 1816657920 := by rw [card_H] at hHt; omega
  rw [hHt', card_J j4Facts] at hdvd
  have h4 : Nat.card R ∣ 4 * [3, 11, 11, 23, 29, 31, 37, 43].prod := by
    rw [mul_comm] at hdvd
    have h5 := Nat.dvd_div_of_mul_dvd hdvd
    have e : 86775571046077562880 / 1816657920 = 4 * [3, 11, 11, 23, 29, 31, 37, 43].prod := by
      norm_num
    rwa [e] at h5
  have hRL : Nat.card R ∣ [3, 11, 11, 23, 29, 31, 37, 43].prod :=
    Nat.Coprime.dvd_of_dvd_mul_left (by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact Nat.Coprime.pow_right 2 (Nat.coprime_two_right.2 hRodd)) h4
  have hcN := card_le_two_pow_length_mul_card_centralizer N_comm (fun a ha => by
    obtain ⟨i, -, rfl⟩ := exists_η_eq ha
    exact η_mul_self i) hRodd (N_conj_oddCoreImage ht) (L := [3, 11, 11, 23, 29, 31, 37, 43])
    (by decide) hRL
  set B := N ⊓ Subgroup.centralizer (R : Set J) with hB
  have hmod : Nat.card B ≡ 2 [MOD 11] := by
    have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    refine card_modEq_two_of_fixed a276_pow (fun z hz b hb => ?_)
      (Subgroup.mem_inf.2 ⟨ht, η_mem_centralizer_oddCoreImage 14⟩)
      (fun h => absurd (η_injOn (k := 0) (by norm_num) (by norm_num) (h.trans η_zero.symm))
        (by norm_num))
      (by rw [a276_acts, a276_check.2.2.1]) fun b hb h => a276_fix (Subgroup.mem_inf.1 hb).1 h
    have hzK : z ∈ K ⊓ C := (Subgroup.zpowers_le.2
      (Subgroup.mem_inf.2 ⟨a276_mem_K, a276_mem_centralizer⟩)) hz
    exact conj_mem_centralizer_oddCoreImage
      (fun n hn => conj_mem_N_of_mem_H z (K_le_H (Subgroup.mem_inf.1 hzK).1) n hn)
      (Subgroup.mem_inf.1 hzK).2 hb
  obtain ⟨k, hk, hkB⟩ := card_le_of_dvd_two_pow (inf_le_left : B ≤ N)
  rw [card_N, hkB] at hcN
  rw [hkB] at hmod
  have hk11 : k = 11 := by
    have h3 : 3 ≤ k := by
      by_contra h
      have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at hcN
      omega
    interval_cases k <;> first | rfl | (exfalso; revert hmod; decide)
  have hBN : B = N := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [card_N, hkB, hk11])
  exact oddCoreImage_eq_bot_of_le ht (hBN ▸ inf_le_right)

theorem CTU_J4_local_276_orbit_involution_centralizer_odd_core :
    ∀ t : J, (∃ g : J, ∃ k ∈ K, t = g⁻¹ * (k⁻¹ * η 14 * k) * g) →
      orderOf t = 2 ∧ CFSG.oddCore (Subgroup.centralizer ({t} : Set J)) = ⊥ := by
  intro t ht
  have hc := isConj_of_orbit ht
  exact ⟨(orderOf_of_isConj hc).trans (orderOf_η (by norm_num) (by norm_num)),
    FischerOddCore.oddCore_centralizer_eq_bot_of_isConj hc oddCore_centralizer_η14⟩

theorem CTU_J4_full_group_local_276_orbit_involution_odd_core
    {X : Type*} [Group X] [Finite X]
    (hF : IsSimpleGroup (CFSG.generalizedFitting X))
    (hnab : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a)
    (ψ : CFSG.generalizedFitting X ≃* J) (t : CFSG.generalizedFitting X)
    (ht : ∃ g : J, ∃ k ∈ K, ψ t = g⁻¹ * (k⁻¹ * η 14 * k) * g) :
    orderOf (t : X) = 2 ∧ CFSG.oddCore (Subgroup.centralizer ({(t : X)} : Set X)) = ⊥ := by
  have h := @full_group_of_local_conj X J _ _ (Subgroup.toGroup J) hF hnab ψ N
    CTU_J4_pointwise_local_binary_subgroup_automorphism_kernel_is_two_group.1 N_comm K (η 14)
    (fun k hk => conj_inv_mem_N hk (η_mem_N 14))
    CTU_J4_local_276_orbit_involution_centralizer_odd_core t ht
  exact h

end CFSG.Sporadic.J4Schreier
