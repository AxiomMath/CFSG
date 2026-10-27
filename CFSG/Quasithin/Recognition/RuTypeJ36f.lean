module

public import CFSG.Quasithin.Recognition.RuTypeJ36e
public import CFSG.RankThree.PGroups.SolvableTrivialComplementCore

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

namespace RuDataM

variable (M : RuDataM G) [Finite G]

section Five

variable {M} {b : G} (hbH : b ∈ ruH M.T) (hb5 : orderOf b = 5)
include hbH hb5

omit hbH hb5 in
theorem P5_le_NB5 : P5 b ≤ NB5 b := fun _ hx => G5_le_normalizer (P5_le_G5 b hx)

theorem eq_one_of_two_elt_centralizes_P5
    {x : G} (hx : ∀ y ∈ P5 b, x * y = y * x) {k : ℕ}
    (hk : x ^ 2 ^ k = 1) : x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxG : x ∈ G5 b := mem_G5.mpr (hx b (b_mem_P5 hb5))
  have hp : IsPGroup 2 (Subgroup.zpowers (⟨x, hxG⟩ : G5 b)) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers]
    have h1 : (⟨x, hxG⟩ : G5 b) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h1)
    exact ⟨j, hj⟩
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (G5 b) S (T5syl hbH hb5)
  have hmem : g * ⟨x, hxG⟩ * g⁻¹ ∈ (T5syl hbH hb5 : Subgroup (G5 b)) := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact ⟨⟨x, hxG⟩, hS (Subgroup.mem_zpowers _), by simp [MulAut.conj_apply]⟩
  rw [coe_T5syl, Subgroup.mem_subgroupOf] at hmem
  set y : G := (g : G) * x * (g : G)⁻¹ with hy
  have hyT : y ∈ M.T5 b := by simpa using hmem
  have hyc : ∀ p ∈ P5 b, y * p = p * y := by
    intro p hp
    have hgp : (g : G)⁻¹ * p * g ∈ P5 b := by
      have := conj_mem_P5 (inv_mem g.2) hp
      simpa using this
    have h1 := hx _ hgp
    calc y * p = (g : G) * (x * ((g : G)⁻¹ * p * g)) * (g : G)⁻¹ := by rw [hy]; group
      _ = (g : G) * (((g : G)⁻¹ * p * g) * x) * (g : G)⁻¹ := by rw [h1]
      _ = p * y := by rw [hy]; group
  by_contra hx1
  have hy1 : y ≠ 1 := by
    intro h
    apply hx1
    calc x = (g : G)⁻¹ * y * g := by rw [hy]; group
      _ = 1 := by rw [h]; group
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (z_mem_zpowers_T5 hbH hb5 hyT hy1)
  obtain ⟨xz, hxz, hxzc⟩ := exists_P5_not_comm_z hbH hb5
  apply hxzc
  rw [← hj]
  exact ((Commute.zpow_left (show Commute y xz from hyc xz hxz) j)).eq.symm

theorem pCore_two_NB5
    : CFSG.pCore 2 (NB5 b) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hPn : ((P5 b).subgroupOf (NB5 b)).Normal :=
    ⟨fun y hy g => by
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      exact conj_mem_P5_of_normalizes g.2 hy⟩
  have hO := CFSG.pCore_normal (p := 2) (G := NB5 b)
  have hxc : ∀ y ∈ P5 b, (x : G) * y = y * x := by
    intro y hy
    have hyN : y ∈ NB5 b := P5_le_NB5 hy
    set yN : NB5 b := ⟨y, hyN⟩
    have hyP : yN ∈ (P5 b).subgroupOf (NB5 b) := Subgroup.mem_subgroupOf.mpr hy
    have hc1 : x * yN * x⁻¹ * yN⁻¹ ∈ CFSG.pCore 2 (NB5 b) := by
      have := hO.conj_mem x⁻¹ (inv_mem hx) yN
      rw [show x * yN * x⁻¹ * yN⁻¹ = x * (yN * x⁻¹ * yN⁻¹) by group]
      exact mul_mem hx this
    have hc2 : x * yN * x⁻¹ * yN⁻¹ ∈ (P5 b).subgroupOf (NB5 b) :=
      mul_mem (hPn.conj_mem yN hyP x) (inv_mem hyP)
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := NB5 b) ⟨_, hc1⟩
    have hk' : (x * yN * x⁻¹ * yN⁻¹ : NB5 b) ^ 2 ^ k = 1 := by
      simpa using congrArg Subtype.val hk
    have h125 : orderOf (x * yN * x⁻¹ * yN⁻¹ : NB5 b) ∣ 125 := by
      have := Subgroup.orderOf_dvd_natCard _ hc2
      rwa [card_subgroupOf_of_le P5_le_NB5, card_P5_eq_125 hbH hb5] at this
    have h1 : x * yN * x⁻¹ * yN⁻¹ = 1 :=
      orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
        (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 125))
        (orderOf_dvd_of_pow_eq_one hk') h125)
    have h2 : x * yN = yN * x := by
      calc x * yN = (x * yN * x⁻¹ * yN⁻¹) * yN * x := by group
        _ = yN * x := by rw [h1, one_mul]
    exact congrArg Subtype.val h2
  obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := NB5 b) ⟨x, hx⟩
  have hk' : (x : G) ^ 2 ^ k = 1 := by
    have := congrArg (fun y : CFSG.pCore 2 (NB5 b) => ((y : NB5 b) : G)) hk
    simpa using this
  exact Subtype.ext (eq_one_of_two_elt_centralizes_P5 hbH hb5 hxc hk')

theorem generalizedFitting_NB5
    : (generalizedFitting (NB5 b)).map (NB5 b).subtype = P5 b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set N := NB5 b
  set P' : Subgroup N := (P5 b).subgroupOf N with hP'
  have hPn : P'.Normal :=
    ⟨fun y hy g => by
      rw [hP', Subgroup.mem_subgroupOf] at hy ⊢
      exact conj_mem_P5_of_normalizes g.2 hy⟩
  have hN : Nat.card N = 4000 := card_normalizer_B5 hbH hb5
  have hPc : Nat.card P' = 125 := by
    rw [hP', card_subgroupOf_of_le P5_le_NB5, card_P5_eq_125 hbH hb5]
  have hPp : IsPGroup 5 P' := by
    rw [IsPGroup.iff_card, hPc]
    exact ⟨3, by norm_num⟩
  have hQc : Nat.card (N ⧸ P') = 32 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup P'
    rw [hN, hPc] at h
    omega
  have hQp : IsPGroup 2 (N ⧸ P') := by
    rw [IsPGroup.iff_card, hQc]
    exact ⟨5, by norm_num⟩
  have : Group.IsNilpotent P' := hPp.isNilpotent
  have : Group.IsNilpotent (N ⧸ P') := hQp.isNilpotent
  have : Group.IsSolvable N :=
    Group.isSolvable_of_ker_le_range P'.subtype (QuotientGroup.mk' P') (by
      rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  rw [CFSG.RankThree.PGroups.generalizedFitting_eq_fittingSubgroup_of_isSolvable]
  have hF : CFSG.fittingSubgroup N = P' := by
    refine le_antisymm ?_ (CFSG.LocalCores.fitting_characteristic.2.2 P' hPn inferInstance)
    rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
    refine iSup_le fun ⟨p, hpm⟩ => ?_
    show CFSG.pCore p N ≤ P'
    have hpp := Nat.prime_of_mem_primeFactors hpm
    have hpd := Nat.dvd_of_mem_primeFactors hpm
    rw [hN] at hpd
    have hp25 : p = 2 ∨ p = 5 := by
      rw [show (4000 : ℕ) = 2 ^ 5 * 5 ^ 3 by norm_num] at hpd
      rcases (Nat.Prime.dvd_mul hpp).mp hpd with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow h))
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_five).mp (hpp.dvd_of_dvd_pow h))
    rcases hp25 with h | h
    · rw [h, pCore_two_NB5 hbH hb5]
      exact bot_le
    · rw [h]
      let S : Sylow 5 N := Sylow.ofCard P' (by
        rw [hPc, hN, show (4000 : ℕ) = 5 ^ 3 * 32 by norm_num,
          Nat.factorization_mul (by norm_num) (by norm_num), Nat.Prime.factorization_pow
          Nat.prime_five]
        simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 5 ∣ 32 by norm_num)])
      exact (CFSG.pCore_isPGroup (p := 5) (G := N)).le_sylow_of_normal S
  rw [hF, hP', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr P5_le_NB5]

theorem lemma_J36 :
    (generalizedFitting (NB5 b)).map (NB5 b).subtype = P5 b ∧
    (Nat.card (P5 b) = 5 ^ 3 ∧ (∀ x ∈ P5 b, x ^ 5 = 1) ∧
      ¬ ∀ x ∈ P5 b, ∀ y ∈ P5 b, x * y = y * x) ∧
    (∃ S : Sylow 5 G, (S : Subgroup G) = P5 b) ∧
    ∃ R : Subgroup G, R ≤ ruH M.T ∧ P5 b ⊔ R = NB5 b ∧ P5 b ⊓ R = ⊥ ∧
      Nonempty (R ≃* GL25.W42) ∧ M.z ∈ R ∧ ∀ r ∈ R, r * M.z = M.z * r := by
  refine ⟨generalizedFitting_NB5 hbH hb5, ⟨by rw [card_P5_eq_125 hbH hb5]; norm_num,
    fun x hx => pow_five_eq_one_P5 hbH hb5 hx, not_comm_P5 hbH hb5⟩, exists_sylow_P5 hbH hb5,
    RB5 hbH hb5, RB5_le_H hbH hb5, ?_, ?_, nonempty_RB5_W42 hbH hb5, z_mem_RB5 hbH hb5,
    fun r hr => (M.mem_H_iff_comm.mp (RB5_le_H hbH hb5 hr)).symm⟩
  ·
    have hle : P5 b ⊔ RB5 hbH hb5 ≤ NB5 b := sup_le P5_le_NB5 (RB5_le_normalizer hbH hb5)
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [card_normalizer_B5 hbH hb5]
    have h1 : 125 ∣ Nat.card (P5 b ⊔ RB5 hbH hb5 : Subgroup G) := by
      have := Subgroup.card_dvd_of_le (le_sup_left : P5 b ≤ P5 b ⊔ RB5 hbH hb5)
      rwa [card_P5_eq_125 hbH hb5] at this
    have h2 : 32 ∣ Nat.card (P5 b ⊔ RB5 hbH hb5 : Subgroup G) := by
      have := Subgroup.card_dvd_of_le (le_sup_right : RB5 hbH hb5 ≤ P5 b ⊔ RB5 hbH hb5)
      rwa [card_RB5 hbH hb5] at this
    have h3 : 125 * 32 ∣ Nat.card (P5 b ⊔ RB5 hbH hb5 : Subgroup G) :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h2
    exact Nat.le_of_dvd Nat.card_pos (by simpa using h3)
  · rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact eq_one_of_mem_coprime (P := P5 b) (R := RB5 hbH hb5)
      (by rw [card_P5_eq_125 hbH hb5, card_RB5 hbH hb5]; norm_num) hx.1 hx.2

end Five

end RuDataM

end CFSG.Quasithin.RuType
