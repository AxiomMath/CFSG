module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8KSeven
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8KE64
import CFSG.Quasithin.H13.NQCatSubnormalCore
import CFSG.LocalAnalysis.SteinbergBKTwoGroupAutomorphismKernels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem c8k_sq_eq_one_of_elemAbelian {X : Type*} [Group X] {N : Subgroup X}
    (h : IsElemAbelianOfRank 2 6 ↥N) : ∀ n ∈ N, n ^ 2 = 1 := by
  intro n hn
  obtain ⟨e⟩ := h
  have h2 : (⟨n, hn⟩ : ↥N) ^ 2 = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    funext i
    change (2 : ℕ) • (Multiplicative.toAdd (e ⟨n, hn⟩) i) = 0
    rw [nsmul_eq_mul, show ((2 : ℕ) : ZMod 2) = 0 by decide, zero_mul]
  simpa using h2

theorem c8k_ker_two_part {Γ : Type} [Group Γ] [Finite Γ] {B S C₀ : Subgroup Γ} {d : Γ}
    {ρ : Γ →* ↥(StatedSL 2 (ZMod 7))} {O Z : Subgroup Γ} (conf : C8KConf Γ B S C₀ d)
    (nat : C8KNat Γ d ρ O Z) (hOB : ¬ O ≤ B) :
    ∃ P : Subgroup Γ, IsPGroup 2 P ∧ P ≤ ρ.ker ∧ ρ.ker = P ⊔ O := by
  obtain ⟨Y, hYB, hYO, hYodd⟩ := conf.minimal O nat.normal hOB
  obtain ⟨P₀, instP₀, φ, hφs, hφk, hE64, -⟩ := conf.p0
  obtain ⟨N, hNn, hN64, hL3⟩ := hE64
  haveI : Finite P₀ := Finite.of_surjective φ hφs
  haveI : N.Normal := hNn
  let I : Subgroup Γ := CFSG.pPrimeCore 3 Γ
  have hkerI : ρ.ker ≤ I := nat.ker_le
  have hMn : ((I.subgroupOf B).map φ).Normal :=
    ((inferInstance : I.Normal).subgroupOf B).map φ hφs
  have hcop : Nat.Coprime 3 (Nat.card I) := CFSG.pPrimeCore_coprime_card (p := 3) (G := Γ)
  have h3 : ∀ m ∈ (I.subgroupOf B).map φ, ¬ 3 ∣ orderOf m := by
    rintro m ⟨b, hb, rfl⟩
    have hbI : (b : Γ) ∈ I := Subgroup.mem_subgroupOf.mp hb
    have hdvd : orderOf (φ b) ∣ Nat.card I := by
      refine (orderOf_map_dvd φ b).trans ?_
      rw [← Subgroup.orderOf_coe]
      exact Subgroup.orderOf_dvd_natCard I hbI
    intro h3dvd
    have h31 : (3 : ℕ) = 1 := Nat.Coprime.eq_one_of_dvd hcop (h3dvd.trans hdvd)
    exact absurd h31 (by norm_num)
  have hMN : (I.subgroupOf B).map φ ≤ N := c8_e64_le_of_no_three hL3 hMn h3
  have hNsq : ∀ n ∈ N, n ^ 2 = 1 := c8k_sq_eq_one_of_elemAbelian hN64
  have hP2 : IsPGroup 2 ↥(Y ⊓ ρ.ker) := by
    apply CFSG.LocalAnalysis.SteinbergBK.isPGroup_two_of_odd_eq_one
    intro y hy hodd
    obtain ⟨hyY, hyK⟩ := Subgroup.mem_inf.mp hy
    have hyI : y ∈ I := hkerI hyK
    have hyB : y ∈ B := hYB hyY
    have hmem : (⟨y, hyB⟩ : ↥B) ∈ I.subgroupOf B :=
      Subgroup.mem_subgroupOf.mpr hyI
    have hmemN : φ ⟨y, hyB⟩ ∈ N := hMN (Subgroup.mem_map_of_mem φ hmem)
    have hsq : (φ ⟨y, hyB⟩) ^ 2 = 1 := hNsq _ hmemN
    have hdvd2 : orderOf (φ ⟨y, hyB⟩) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    have hdvdodd : orderOf (φ ⟨y, hyB⟩) ∣ orderOf y := by
      have h := orderOf_map_dvd φ ⟨y, hyB⟩
      rwa [Subgroup.orderOf_mk] at h
    have hodd' : Odd (orderOf (φ ⟨y, hyB⟩)) := Odd.of_dvd_nat hodd hdvdodd
    have hle : orderOf (φ ⟨y, hyB⟩) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd2
    have hone : orderOf (φ ⟨y, hyB⟩) = 1 := by
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hdvd2 with h1 | h1
      · exact h1
      · exact absurd (h1 ▸ hodd') (by decide)
    have hphi1 : φ ⟨y, hyB⟩ = 1 := orderOf_eq_one_iff.mp hone
    have hker : (⟨y, hyB⟩ : ↥B) ∈ φ.ker := MonoidHom.mem_ker.mpr hphi1
    have hkerC : (⟨y, hyB⟩ : ↥B) ∈ C₀.subgroupOf B := hφk ▸ hker
    exact hYodd y hyY (Subgroup.mem_subgroupOf.mp hkerC) hodd
  refine ⟨Y ⊓ ρ.ker, hP2, inf_le_right, ?_⟩
  haveI : O.Normal := nat.normal
  apply le_antisymm
  · intro k hk
    have hkTop : k ∈ Y ⊔ O := by
      rw [hYO]
      exact Subgroup.mem_top k
    obtain ⟨y, hyY, o, hoO, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hkTop
    have hyK : y ∈ ρ.ker := by
      have h1 : y * o ∈ ρ.ker := hk
      have h2 : o⁻¹ ∈ ρ.ker := ρ.ker.inv_mem (nat.o_le_ker hoO)
      simpa using ρ.ker.mul_mem h1 h2
    exact Subgroup.mul_mem_sup ⟨hyY, hyK⟩ hoO
  · exact sup_le inf_le_right nat.o_le_ker

theorem c8k_ker_le_o_of_two_part {Γ : Type} [Group Γ] [Finite Γ] {d : Γ}
    {ρ : Γ →* ↥(StatedSL 2 (ZMod 7))} {O Z : Subgroup Γ} (nat : C8KNat Γ d ρ O Z)
    {P : Subgroup Γ} (hP : IsPGroup 2 P) (hPk : P ≤ ρ.ker) (hk : ρ.ker = P ⊔ O) :
    ρ.ker ≤ O := by
  haveI : O.Normal := nat.normal
  have hQk : CFSG.pCore 2 Γ ≤ ρ.ker := nat.q_le.trans (nat.z_le.trans nat.o_le_ker)
  have hT2 : IsPGroup 2 ↥(P ⊔ CFSG.pCore 2 Γ) :=
    hP.to_sup_of_normal_right CFSG.pCore_isPGroup
  have hTk : P ⊔ CFSG.pCore 2 Γ ≤ ρ.ker := sup_le hPk hQk
  have hcent : ∀ p ∈ P, ∀ o ∈ O, o * p * o⁻¹ ∈ P ⊔ CFSG.pCore 2 Γ := by
    intro p hp o ho
    have hpK : p ∈ ρ.ker := hPk hp
    have h7 : ¬ 7 ∣ orderOf p := by
      obtain ⟨k, hkpow⟩ := isPGroup_iff_orderOf_dvd_pow.mp hP ⟨p, hp⟩
      have hkpow' : orderOf p ∣ 2 ^ k := by
        simpa [Subgroup.orderOf_coe] using hkpow
      intro h7d
      exact (by norm_num : ¬ (7 : ℕ) ∣ 2)
        (Nat.Prime.dvd_of_dvd_pow (by norm_num) (h7d.trans hkpow'))
    have hc : p * o * p⁻¹ * o⁻¹ ∈ CFSG.pCore 2 Γ := nat.cent p hpK h7 o ho
    have hid : o * p * o⁻¹ = (p * o * p⁻¹ * o⁻¹)⁻¹ * p := by group
    rw [hid, sup_comm]
    exact Subgroup.mul_mem_sup ((CFSG.pCore 2 Γ).inv_mem hc) hp
  have hOnorm : O ≤
      normalizer ((P ⊔ CFSG.pCore 2 Γ : Subgroup Γ) : Set Γ) := by
    rw [Subgroup.le_normalizer_iff]
    intro o ho t ht
    obtain ⟨p, hp, q, hq, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp ht
    have h1 : o * p * o⁻¹ ∈ P ⊔ CFSG.pCore 2 Γ := hcent p hp o ho
    have h2 : o * q * o⁻¹ ∈ CFSG.pCore 2 Γ :=
      (inferInstance : (CFSG.pCore 2 Γ).Normal).conj_mem q hq o
    have h2' : o * q * o⁻¹ ∈ P ⊔ CFSG.pCore 2 Γ := Subgroup.mem_sup_right h2
    have hmul : (o * p * o⁻¹) * (o * q * o⁻¹) ∈ P ⊔ CFSG.pCore 2 Γ :=
      (P ⊔ CFSG.pCore 2 Γ).mul_mem h1 h2'
    have hid : o * (p * q) * o⁻¹ = (o * p * o⁻¹) * (o * q * o⁻¹) := by group
    rwa [hid]
  have hPn : P ≤
      normalizer ((P ⊔ CFSG.pCore 2 Γ : Subgroup Γ) : Set Γ) := by
    rw [Subgroup.le_normalizer_iff]
    intro p hp t ht
    exact (P ⊔ CFSG.pCore 2 Γ).mul_mem
      ((P ⊔ CFSG.pCore 2 Γ).mul_mem (Subgroup.mem_sup_left hp) ht)
      ((P ⊔ CFSG.pCore 2 Γ).inv_mem (Subgroup.mem_sup_left hp))
  have hle_norm : ρ.ker ≤
      normalizer ((P ⊔ CFSG.pCore 2 Γ : Subgroup Γ) : Set Γ) := by
    rw [hk]
    exact sup_le hPn hOnorm
  have hTn : ((P ⊔ CFSG.pCore 2 Γ).subgroupOf ρ.ker).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTk).mpr hle_norm
  have hle_pcore : (P ⊔ CFSG.pCore 2 Γ).subgroupOf ρ.ker ≤ CFSG.pCore 2 ↥ρ.ker := by
    apply le_sSup
    exact ⟨hTn, hT2.comap_subtype⟩
  have hmap : (CFSG.pCore 2 ↥ρ.ker).map ρ.ker.subtype ≤ CFSG.pCore 2 Γ :=
    CFSG.Quasithin.H13.NQCat.map_pCore_le_pCore_of_isSubnormal'
      (X := ρ.ker) (MonoidHom.normal_ker ρ).isSubnormal
  have hTle : P ⊔ CFSG.pCore 2 Γ ≤ CFSG.pCore 2 Γ := by
    calc P ⊔ CFSG.pCore 2 Γ
        = ((P ⊔ CFSG.pCore 2 Γ).subgroupOf ρ.ker).map ρ.ker.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hTk).symm
      _ ≤ (CFSG.pCore 2 ↥ρ.ker).map ρ.ker.subtype := Subgroup.map_mono hle_pcore
      _ ≤ CFSG.pCore 2 Γ := hmap
  have hPle : P ≤ O := le_sup_left.trans (hTle.trans (nat.q_le.trans nat.z_le))
  rw [hk]
  exact sup_le hPle le_rfl

theorem c8k_ker_eq_o {Γ : Type} [Group Γ] [Finite Γ] {B S C₀ : Subgroup Γ} {d : Γ}
    {ρ : Γ →* ↥(StatedSL 2 (ZMod 7))} {O Z : Subgroup Γ} (conf : C8KConf Γ B S C₀ d)
    (nat : C8KNat Γ d ρ O Z) : ρ.ker = O := by
  obtain ⟨P, hP, hPk, hk⟩ := c8k_ker_two_part conf nat (c8k_not_o_le_b conf nat)
  exact le_antisymm (c8k_ker_le_o_of_two_part nat hP hPk hk) nat.o_le_ker

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
