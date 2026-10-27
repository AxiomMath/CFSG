module

import CFSG.Goldschmidt.Steps.AxB
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.RankThree.PerfectCover.CentralQuotientPrimeSupport
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
import CFSG.GH74.GLS.AssemblyComponents
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.RankThree.PartTwo.KFacts.KS44OutSz
import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.GH74.GLS

namespace Res2LBal

open CFSG.RankThree.PartOne.EmbeddingFixedResidual
  (ne_bot_inSubgroup_perfectResidual_of_not_isSolvable isPerfect_inSubgroup_perfectResidual)

variable {X : Type} [Group X]

theorem eq_one_of_mem_of_pow {P : Subgroup X} (hP3 : ¬ 3 ∣ Nat.card P) {w : X} (hw : w ∈ P)
    {m : ℕ} (hwm : w ^ 3 ^ m = 1) : w = 1 := by
  have h1 : orderOf w ∣ Nat.card P := Subgroup.orderOf_dvd_natCard P hw
  have h2 : orderOf w ∣ 3 ^ m := orderOf_dvd_of_pow_eq_one hwm
  have hcop : Nat.Coprime (orderOf w) 3 :=
    Nat.Coprime.coprime_dvd_left h1
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hP3).symm
  have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right m hcop) h2
  exact orderOf_eq_one_iff.mp this

theorem pow_mul_eq_one_of_commute {x y : X} (hxy : Commute x y) {i j : ℕ} (hx : x ^ 3 ^ i = 1)
    (hy : y ^ 3 ^ j = 1) : (x * y) ^ 3 ^ (i + j) = 1 := by
  rw [hxy.mul_pow, pow_add, pow_mul, hx, one_pow, one_mul, mul_comm, pow_mul, hy, one_pow]

theorem conj_pow_eq_one {x : X} (g : X) {i : ℕ} (hx : x ^ 3 ^ i = 1) :
    (g * x * g⁻¹) ^ 3 ^ i = 1 := by
  rw [conj_pow, hx, mul_one, mul_inv_cancel]

theorem commutator_mem {P : Subgroup X} {n y : X} (hn : n ∈ P)
    (hy : y ∈ Subgroup.normalizer (P : Set X)) : n * y * n⁻¹ * y⁻¹ ∈ P := by
  have h1 : y * n⁻¹ * y⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hy n⁻¹).mp (inv_mem hn)
  have : n * y * n⁻¹ * y⁻¹ = n * (y * n⁻¹ * y⁻¹) := by group
  rw [this]
  exact mul_mem hn h1

theorem isComponent_conj {K : Subgroup X} (hK : IsComponent K) (g : X) :
    IsComponent (K.map (MulAut.conj g).toMonoidHom) :=
  CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hK

theorem conj_mem_map {K : Subgroup X} {k : X} (hk : k ∈ K) (g : X) :
    g * k * g⁻¹ ∈ K.map (MulAut.conj g).toMonoidHom :=
  ⟨k, hk, by simp [MulAut.conj_apply]⟩

theorem map_conj_map_conj (K : Subgroup X) (g h : X) :
    (K.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      K.map (MulAut.conj (g * h)).toMonoidHom := by
  rw [Subgroup.map_map, map_mul]
  rfl

theorem map_conj_one (K : Subgroup X) : K.map (MulAut.conj (1 : X)).toMonoidHom = K := by
  rw [map_one]
  exact Subgroup.map_id K

theorem commute_of_ne [Finite X] {K L : Subgroup X} (hK : IsComponent K) (hL : IsComponent L)
    (hKL : K ≠ L)
    {x y : X} (hx : x ∈ K) (hy : y ∈ L) : Commute x y := by
  rcases CFSG.LocalCores.distinct_components_commute hK hL with h | h
  · exact absurd h hKL
  · have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hx
    exact (Subgroup.mem_centralizer_iff.mp this y hy).symm

theorem mem_centralizer_of_mem_of_ne [Finite X] {K L : Subgroup X} (hK : IsComponent K)
    (hL : IsComponent L)
    (hKL : K ≠ L) {y : X} (hyL : y ∈ L) : y ∈ Subgroup.centralizer (K : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact commute_of_ne hK hL hKL hk hyL

theorem exists_three_elem [Finite X] {K : Subgroup X} (hX : CFSG.pPrimeCore 3 X = ⊥)
    (hK : IsComponent K) :
    ∃ y ∈ K, y ∉ Subgroup.centralizer (K : Set X) ∧ ∃ m : ℕ, y ^ 3 ^ m = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKp : Group.IsPerfect K := hK.1.1
  have hKnt : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
  have h3Q : 3 ∣ Nat.card (K ⧸ Subgroup.center K) := by
    by_contra h3
    have hS : ∀ S : Sylow 3 K, (S : Subgroup K) = ⊥ := fun S =>
      CFSG.RankThree.PerfectCover.sylow_eq_bot_of_not_dvd_card_quotient_center S h3
    have h3K : ¬ 3 ∣ Nat.card K := by
      intro h3K
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) 3 h3K
      have hpg : IsPGroup 3 (Subgroup.zpowers x) := by
        rw [IsPGroup.iff_card, Nat.card_zpowers, hx]
        exact ⟨1, by norm_num⟩
      obtain ⟨S, hS'⟩ := hpg.exists_le_sylow
      have hxS : x ∈ (S : Subgroup K) := hS' (Subgroup.mem_zpowers x)
      rw [hS S, Subgroup.mem_bot] at hxS
      rw [hxS, orderOf_one] at hx
      exact absurd hx (by norm_num)
    have hle : K ≤ CFSG.pPrimeCore 3 X :=
      le_pPrimeCore_of_subnormal 3 hK.2
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3K)
    rw [hX, le_bot_iff] at hle
    have : Nontrivial (⊥ : Subgroup X) := hle ▸ hKnt
    exact not_nontrivial (⊥ : Subgroup X) this
  obtain ⟨xbar, hxbar⟩ := exists_prime_orderOf_dvd_card' (G := K ⧸ Subgroup.center K) 3 h3Q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xbar
  have hord : orderOf x ≠ 0 := (orderOf_pos x).ne'
  obtain ⟨e, r, hr3, hr⟩ := Nat.exists_eq_pow_mul_and_not_dvd hord 3 (by norm_num)
  refine ⟨((x ^ r : K) : X), (x ^ r).2, ?_, e, ?_⟩
  · intro hc
    have hcen : x ^ r ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro z
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact Subgroup.mem_centralizer_iff.mp hc z z.2
    have h1 : ((x : K ⧸ Subgroup.center K)) ^ r = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hcen
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hxbar] at h2
    exact hr3 h2
  · rw [← Subgroup.coe_pow, ← pow_mul, mul_comm, ← hr, pow_orderOf_eq_one]
    rfl

theorem isPGroup_zpowers {b : X} (hb3 : b ^ 3 = 1) : IsPGroup 3 (Subgroup.zpowers b) := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
  rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm,
    zpow_mul, show ((3 : ℕ) : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, hb3, one_zpow]

theorem le_centralizer_zpowers {b : X} {P : Subgroup X} (hPb : P ≤ Subgroup.centralizer {b}) :
    P ≤ Subgroup.centralizer (Subgroup.zpowers b : Set X) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  rintro h hh
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  have hxb : Commute b x := (Subgroup.mem_centralizer_singleton_iff.mp (hPb hx)).symm
  exact (hxb.zpow_left k).eq

theorem le_centralizer_pCore [Finite X] {b : X} (hb3 : b ^ 3 = 1) {P : Subgroup X}
    (hPb : P ≤ Subgroup.centralizer {b})
    (hPN : Subgroup.centralizer {b} ≤ Subgroup.normalizer (P : Set X)) (hP3 : ¬ 3 ∣ Nat.card P) :
    P ≤ Subgroup.centralizer (CFSG.pCore 3 X : Set X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hO : IsPGroup 3 (CFSG.pCore 3 X) := CFSG.pCore_isPGroup
  have hON : (CFSG.pCore 3 X).Normal := CFSG.pCore_normal
  have hcop : Nat.Coprime (Nat.card P) 3 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hP3).symm
  have hRN : P ≤ Subgroup.normalizer (CFSG.pCore 3 X : Set X) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hON]
    exact le_top
  have hBN : Subgroup.zpowers b ≤ Subgroup.normalizer (CFSG.pCore 3 X : Set X) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hON]
    exact le_top
  have hRB : ⁅P, Subgroup.zpowers b⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_zpowers hPb)
  have hfix : CFSG.pCore 3 X ⊓ Subgroup.centralizer (Subgroup.zpowers b : Set X) ≤
      Subgroup.centralizer (P : Set X) := by
    rintro r ⟨hrO, hrb⟩
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have hrb' : r ∈ Subgroup.centralizer {b} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hrb b (Subgroup.mem_zpowers b)).symm
    have hcP : n * r * n⁻¹ * r⁻¹ ∈ P := commutator_mem hn (hPN hrb')
    have hcO : n * r * n⁻¹ * r⁻¹ ∈ CFSG.pCore 3 X := by
      have h1 : n * r * n⁻¹ ∈ CFSG.pCore 3 X := hON.conj_mem r hrO n
      exact mul_mem h1 (inv_mem hrO)
    obtain ⟨m, hm⟩ := hO ⟨_, hcO⟩
    have hm' : (n * r * n⁻¹ * r⁻¹) ^ 3 ^ m = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    have h1 := eq_one_of_mem_of_pow hP3 hcP hm'
    have h2 : n * r = r * n := by
      calc n * r = (n * r * n⁻¹ * r⁻¹) * (r * n) := by group
        _ = r * n := by rw [h1, one_mul]
    exact h2
  have := CFSG.Goldschmidt.N10 X (CFSG.pCore 3 X) P (Subgroup.zpowers b) hO hcop
    (isPGroup_zpowers hb3) hRN hBN hRB hfix
  exact Subgroup.le_centralizer_iff.mp this

theorem eq_bot_of_le_centralizer [Finite X] {P : Subgroup X} (hPp : Group.IsPerfect P)
    (hF : P ≤ Subgroup.centralizer (CFSG.fittingSubgroup X : Set X))
    (hE : ∀ K : Subgroup X, IsComponent K → P ≤ Subgroup.centralizer (K : Set X)) : P = ⊥ := by
  have hCF : P ≤ Subgroup.centralizer (generalizedFitting X : Set X) := by
    rw [Subgroup.le_centralizer_iff, generalizedFitting]
    refine sup_le (Subgroup.le_centralizer_iff.mp hF) ?_
    exact sSup_le fun K hK => Subgroup.le_centralizer_iff.mp (hE K hK)
  have hPF : P ≤ generalizedFitting X := hCF.trans (CFSG.centralizer_generalizedFitting_le X)
  have hcomm : ⁅P, P⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    (hCF.trans (Subgroup.centralizer_le hPF))
  rw [← (Subgroup.isPerfect_iff).mp hPp]
  exact hcomm

theorem pow_eq_pow_mod {b : X} (hb3 : b ^ 3 = 1) (j : ℕ) : b ^ j = b ^ (j % 3) := by
  conv_lhs => rw [← Nat.div_add_mod j 3, pow_add, pow_mul, hb3, one_pow, one_mul]

theorem eq_map_conj_of_map_conj_eq {b : X} (hb3 : b ^ 3 = 1) {H K : Subgroup X} {i j : ℕ}
    (h : H.map (MulAut.conj (b ^ i)).toMonoidHom = K.map (MulAut.conj (b ^ j)).toMonoidHom) :
    H = K.map (MulAut.conj (b ^ (j + 2 * i))).toMonoidHom := by
  have h1 := congrArg (fun L : Subgroup X => L.map (MulAut.conj (b ^ (2 * i))).toMonoidHom) h
  simp only [map_conj_map_conj] at h1
  rw [← pow_add, ← pow_add, show 2 * i + i = 3 * i by ring, pow_mul, hb3, one_pow,
    map_conj_one, add_comm] at h1
  exact h1

theorem orbit_ne {b : X} (hb3 : b ^ 3 = 1) {K : Subgroup X}
    (hbK : b ∉ Subgroup.normalizer (K : Set X)) :
    K ≠ K.map (MulAut.conj (b ^ 1)).toMonoidHom ∧ K ≠ K.map (MulAut.conj (b ^ 2)).toMonoidHom ∧
      K.map (MulAut.conj (b ^ 1)).toMonoidHom ≠ K.map (MulAut.conj (b ^ 2)).toMonoidHom := by
  have h1 : K ≠ K.map (MulAut.conj (b ^ 1)).toMonoidHom := by
    intro h
    apply hbK
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change K.map (MulAut.conj b).toMonoidHom = K
    rw [pow_one] at h
    exact h.symm
  refine ⟨h1, fun h => ?_, fun h => ?_⟩
  ·
    apply h1
    have h' := eq_map_conj_of_map_conj_eq hb3 (H := K) (K := K) (i := 2) (j := 0)
      (by rw [pow_zero, map_conj_one]; exact h.symm)
    rw [pow_eq_pow_mod hb3 (0 + 2 * 2), show (0 + 2 * 2) % 3 = 1 by norm_num] at h'
    exact h'
  ·
    apply h1
    have h' := eq_map_conj_of_map_conj_eq hb3 (H := K) (K := K) (i := 1) (j := 2) h
    rw [pow_eq_pow_mod hb3 (2 + 2 * 1), show (2 + 2 * 1) % 3 = 1 by norm_num] at h'
    exact h'

theorem conj_conj_pow_comm {n b : X} (hnb : n * b = b * n) (y : X) (i : ℕ) :
    n * (b ^ i * y * (b ^ i)⁻¹) * n⁻¹ = b ^ i * (n * y * n⁻¹) * (b ^ i)⁻¹ := by
  have h : n * b ^ i = b ^ i * n := (Commute.pow_right hnb i).eq
  calc n * (b ^ i * y * (b ^ i)⁻¹) * n⁻¹ = (n * b ^ i) * y * (n * b ^ i)⁻¹ := by group
    _ = (b ^ i * n) * y * (b ^ i * n)⁻¹ := by rw [h]
    _ = b ^ i * (n * y * n⁻¹) * (b ^ i)⁻¹ := by group

theorem diag_mul {b k k' : X} (h1 : Commute k' (b ^ 1 * k * (b ^ 1)⁻¹))
    (h2 : Commute k' (b ^ 2 * k * (b ^ 2)⁻¹))
    (h3 : Commute (b ^ 1 * k' * (b ^ 1)⁻¹) (b ^ 2 * k * (b ^ 2)⁻¹)) :
    (k * k') * (b ^ 1 * (k * k') * (b ^ 1)⁻¹) * (b ^ 2 * (k * k') * (b ^ 2)⁻¹) =
      (k * (b ^ 1 * k * (b ^ 1)⁻¹) * (b ^ 2 * k * (b ^ 2)⁻¹)) *
        (k' * (b ^ 1 * k' * (b ^ 1)⁻¹) * (b ^ 2 * k' * (b ^ 2)⁻¹)) := by
  have e : ∀ i : ℕ, b ^ i * (k * k') * (b ^ i)⁻¹ =
      (b ^ i * k * (b ^ i)⁻¹) * (b ^ i * k' * (b ^ i)⁻¹) := fun i => by group
  rw [e 1, e 2]
  generalize b ^ 1 * k * (b ^ 1)⁻¹ = a₁ at h1 h2 h3 ⊢
  generalize b ^ 2 * k * (b ^ 2)⁻¹ = a₂ at h1 h2 h3 ⊢
  generalize b ^ 1 * k' * (b ^ 1)⁻¹ = c₁ at h1 h2 h3 ⊢
  generalize b ^ 2 * k' * (b ^ 2)⁻¹ = c₂ at h1 h2 h3 ⊢
  calc k * k' * (a₁ * c₁) * (a₂ * c₂) = k * (k' * a₁) * c₁ * a₂ * c₂ := by group
    _ = k * (a₁ * k') * c₁ * a₂ * c₂ := by rw [h1.eq]
    _ = k * a₁ * k' * (c₁ * a₂) * c₂ := by group
    _ = k * a₁ * k' * (a₂ * c₁) * c₂ := by rw [h3.eq]
    _ = k * a₁ * (k' * a₂) * c₁ * c₂ := by group
    _ = k * a₁ * (a₂ * k') * c₁ * c₂ := by rw [h2.eq]
    _ = k * a₁ * a₂ * (k' * c₁ * c₂) := by group

theorem diag_mem_centralizer {b : X} (hb3 : b ^ 3 = 1) {k : X}
    (h01 : Commute k (b ^ 1 * k * (b ^ 1)⁻¹)) (h02 : Commute k (b ^ 2 * k * (b ^ 2)⁻¹)) :
    k * (b ^ 1 * k * (b ^ 1)⁻¹) * (b ^ 2 * k * (b ^ 2)⁻¹) ∈ Subgroup.centralizer {b} := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have e1 : b * k * b⁻¹ = b ^ 1 * k * (b ^ 1)⁻¹ := by group
  have e2 : b * (b ^ 1 * k * (b ^ 1)⁻¹) * b⁻¹ = b ^ 2 * k * (b ^ 2)⁻¹ := by group
  have e3 : b * (b ^ 2 * k * (b ^ 2)⁻¹) * b⁻¹ = k := by
    rw [show b * (b ^ 2 * k * (b ^ 2)⁻¹) * b⁻¹ = b ^ 3 * k * (b ^ 3)⁻¹ by group, hb3]
    group
  have e : b * (k * (b ^ 1 * k * (b ^ 1)⁻¹) * (b ^ 2 * k * (b ^ 2)⁻¹)) * b⁻¹ =
      k * (b ^ 1 * k * (b ^ 1)⁻¹) * (b ^ 2 * k * (b ^ 2)⁻¹) := by
    calc b * (k * (b ^ 1 * k * (b ^ 1)⁻¹) * (b ^ 2 * k * (b ^ 2)⁻¹)) * b⁻¹ =
        (b * k * b⁻¹) * (b * (b ^ 1 * k * (b ^ 1)⁻¹) * b⁻¹) *
          (b * (b ^ 2 * k * (b ^ 2)⁻¹) * b⁻¹) := by group
      _ = (b ^ 1 * k * (b ^ 1)⁻¹) * (b ^ 2 * k * (b ^ 2)⁻¹) * k := by rw [e1, e2, e3]
      _ = k * (b ^ 1 * k * (b ^ 1)⁻¹) * (b ^ 2 * k * (b ^ 2)⁻¹) := by
        rw [((h01.mul_right h02).symm).eq, ← mul_assoc]
  calc k * (b ^ 1 * k * (b ^ 1)⁻¹) * (b ^ 2 * k * (b ^ 2)⁻¹) * b =
      b * (k * (b ^ 1 * k * (b ^ 1)⁻¹) * (b ^ 2 * k * (b ^ 2)⁻¹)) * b⁻¹ * b := by rw [e]
    _ = b * (k * (b ^ 1 * k * (b ^ 1)⁻¹) * (b ^ 2 * k * (b ^ 2)⁻¹)) := by group

theorem diag_conj {b g : X} (hgb : g * b = b * g) (k : X) :
    (g * k * g⁻¹) * (b ^ 1 * (g * k * g⁻¹) * (b ^ 1)⁻¹) * (b ^ 2 * (g * k * g⁻¹) * (b ^ 2)⁻¹) =
      g * (k * (b ^ 1 * k * (b ^ 1)⁻¹) * (b ^ 2 * k * (b ^ 2)⁻¹)) * g⁻¹ := by
  rw [← conj_conj_pow_comm hgb k 1, ← conj_conj_pow_comm hgb k 2]
  group

end Res2LBal

open Res2LBal

end CFSG.RankThree.PartTwo.Sec14
