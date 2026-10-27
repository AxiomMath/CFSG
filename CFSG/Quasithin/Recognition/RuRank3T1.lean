module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Pipe
public import CFSG.Quasithin.Recognition.RuRank3T1CertInputs
public import CFSG.Quasithin.Recognition.RuRank3RuAut
public import CFSG.Sporadic.Schreier.TitsIso
public import CFSG.Sporadic.Schreier.TitsPrim
public import Certificates.Certificate7088
import Certificates.Kernel.RuT1.Data
import Certificates.Data.Kernel.TitsOver.Check
import Certificates.Kernel.Sporadic.Tits.Words2264
import Certificates.Kernel.MaxD2.TitsD.Data
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.MaxD2.Basic
import CFSG.Certificates.Kernel.TitsOver.Base
import CFSG.Certificates.Kernel.Spor.TextAtSound
import Certificates.Kernel.TitsOver.TitsBase
import CFSG.LocalAnalysis.StandardType.TitsGeneratorsBase
import Mathlib.Tactic.IntervalCases
public import Certificates.Certificate2247
public import Certificates.Certificate2249
public import Certificates.Certificate2253
public import Certificates.Certificate2264
public import Certificates.Certificate7045
public import Certificates.Certificate7046
public import Certificates.Certificate7047
public import Certificates.Certificate7050
public import CFSG.Foundations
public import CFSG.LocalAnalysis.QuasithinUnique.K1.Interface

public section

namespace CFSG.Quasithin.RuRank3

open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.K1.SporadicPerm
open scoped Pointwise

@[expose] noncomputable def t1Inc : titsD →* titsA := Subgroup.inclusion titsD_le_titsA

theorem t1Inc_apply (g : titsD) : ((t1Inc g : titsA) : Equiv.Perm (Fin 1755)) = g := rfl

theorem t1Inc_injective : Function.Injective t1Inc := Subgroup.inclusion_injective _

theorem mem_titsD_of_pow_eq_one {x : titsA} (hx : x ^ 25 = 1) :
    (x : Equiv.Perm (Fin 1755)) ∈ titsD := by
  have h2 := Subgroup.mul_self_mem_of_index_two titsD_index x
  have h26 : (x * x) ^ 13 ∈ titsD.subgroupOf titsA := pow_mem h2 13
  have e : (x * x) ^ 13 = x := by
    rw [← pow_two, ← pow_mul, show 2 * 13 = 25 + 1 by norm_num, pow_succ, hx, one_mul]
  rw [e, Subgroup.mem_subgroupOf] at h26
  exact h26

theorem card_le_two_mul_comap (K : Subgroup titsA) :
    Nat.card K ≤ 2 * Nat.card (K.comap t1Inc) := by
  have hN : (titsD.subgroupOf titsA).Normal := Subgroup.normal_of_index_eq_two titsD_index
  have hrel := Subgroup.relIndex_dvd_index_of_normal (titsD.subgroupOf titsA) K
  rw [titsD_index] at hrel
  have hle : (titsD.subgroupOf titsA).relIndex K ≤ 2 := Nat.le_of_dvd (by norm_num) hrel
  have hmul := Subgroup.card_mul_index ((titsD.subgroupOf titsA).subgroupOf K)
  have hinj : Nat.card ((titsD.subgroupOf titsA).subgroupOf K) ≤ Nat.card (K.comap t1Inc) := by
    refine Nat.card_le_card_of_injective (fun y => ⟨⟨((y : K) : titsA), ?_⟩, ?_⟩) ?_
    · have := y.2
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at this
      exact this
    · show t1Inc _ ∈ K
      exact (y : K).2
    · intro y z hyz
      apply Subtype.ext
      apply Subtype.ext
      have := congrArg (fun w : K.comap t1Inc => ((w : titsD) : Equiv.Perm (Fin 1755))) hyz
      exact Subtype.ext this
  rw [← hmul]
  calc Nat.card ((titsD.subgroupOf titsA).subgroupOf K) *
        ((titsD.subgroupOf titsA).subgroupOf K).index ≤
        Nat.card (K.comap t1Inc) * 2 :=
      Nat.mul_le_mul hinj hle
    _ = 2 * Nat.card (K.comap t1Inc) := mul_comm _ _

theorem t1_comap_facts {K : Subgroup titsA}
    (hidx : K.index ≤ 2304) (hA : K ≠ ⊤) (hD : K ≠ titsD.subgroupOf titsA) :
    15600 ≤ Nat.card K ∧ 7800 ≤ Nat.card (K.comap t1Inc) ∧ K.comap t1Inc ≠ ⊤ := by
  have hKcard : 15600 ≤ Nat.card K := by
    have h := Subgroup.card_mul_index K
    rw [card_titsA] at h
    by_contra hlt
    rw [not_le] at hlt
    have : Nat.card K * K.index < 15600 * 2304 :=
      Nat.mul_lt_mul_of_lt_of_le hlt hidx (by norm_num)
    omega
  set K₀ := K.comap t1Inc with hK₀
  refine ⟨hKcard, ?_, ?_⟩
  · have h2 : Nat.card K ≤ 2 * Nat.card K₀ := card_le_two_mul_comap K
    omega
  · intro htop
    have hDK : titsD.subgroupOf titsA ≤ K := by
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      have : (⟨(x : Equiv.Perm (Fin 1755)), hx⟩ : titsD) ∈ K₀ := htop ▸ Subgroup.mem_top _
      exact this
    have hdvd : K.index ∣ 2 := titsD_index ▸ Subgroup.index_dvd_of_le hDK
    have hcases : K.index = 1 ∨ K.index = 2 := by
      have := Nat.le_of_dvd (by norm_num) hdvd
      have h0 : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      omega
    rcases hcases with h1 | h2
    · exact hA (Subgroup.index_eq_one.1 h1)
    · apply hD
      symm
      refine Subgroup.eq_of_le_of_card_ge hDK ?_
      have e1 := Subgroup.card_mul_index K
      have e2 := Subgroup.card_mul_index (titsD.subgroupOf titsA)
      rw [h2] at e1
      rw [titsD_index] at e2
      omega

theorem t1_dvd_card_comap {K : Subgroup titsA}
    (h25 : 25 ∣ Nat.card K) : 25 ∣ Nat.card (K.comap t1Inc) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨X, hX⟩ := Sylow.exists_subgroup_card_pow_prime 5 (n := 2) (by simpa using h25)
  set X' : Subgroup titsD := (X.map K.subtype).comap t1Inc with hX'
  have hX'card : Nat.card X' = 25 := by
    have hrange : X.map K.subtype ≤ t1Inc.range := by
      rintro _ ⟨y, hy, rfl⟩
      have hy25 : y ^ 25 = 1 := by
        have h1 := orderOf_dvd_natCard (⟨y, hy⟩ : X)
        rw [hX] at h1
        have h2 := orderOf_dvd_iff_pow_eq_one.1 h1
        have := congrArg (fun z : X => (z : K)) h2
        simpa using this
      have hmemD := mem_titsD_of_pow_eq_one (x := ((y : K) : titsA)) (by
        have := congrArg (fun z : K => (z : titsA)) hy25
        simpa using this)
      exact ⟨⟨_, hmemD⟩, rfl⟩
    have hmap : X'.map t1Inc = X.map K.subtype := by
      rw [hX', Subgroup.map_comap_eq, inf_of_le_right hrange]
    rw [← Subgroup.card_map_of_injective t1Inc_injective, hmap,
      Subgroup.card_map_of_injective K.subtype_injective, hX]
    norm_num
  have hXK : X' ≤ K.comap t1Inc := by
    intro x hx
    obtain ⟨y, -, hy⟩ := (show t1Inc x ∈ X.map K.subtype from hx)
    show t1Inc x ∈ K
    rw [← hy]
    exact (y : K).2
  have h := Subgroup.card_dvd_of_le hXK
  rwa [hX'card] at h

theorem titsA_sylow_five_overgroup
    {K : Subgroup titsA} (h25 : 25 ∣ Nat.card K) (hidx : K.index ≤ 2304) (hA : K ≠ ⊤)
    (hD : K ≠ titsD.subgroupOf titsA) :
    ∃ c : titsA, K = ruE0.map (MulAut.conj c).toMonoidHom := by
  obtain ⟨hKcard, hK₀card, hK₀top⟩ := t1_comap_facts hidx hA hD
  set K₀ := K.comap t1Inc with hK₀
  set K₁ : Subgroup (Equiv.Perm (Fin 1755)) := K₀.map titsD.subtype with hK₁
  have hc₁ : Nat.card K₁ = Nat.card K₀ := Subgroup.card_map_of_injective titsD.subtype_injective
  have htop₁ : K₁ ≠ titsD := by
    intro heq
    apply hK₀top
    have htop : (⊤ : Subgroup titsD).map titsD.subtype = titsD := by
      rw [Subgroup.map_top titsD.subtype, Subgroup.range_subtype]
    exact (Subgroup.map_subtype_inj (H := titsD)).mp (heq.trans htop.symm)
  obtain ⟨d, hdD, hd⟩ := Certificates.certificate7088 K₁ (Subgroup.map_subtype_le _)
    (hc₁ ▸ t1_dvd_card_comap h25) (hc₁ ▸ hK₀card) htop₁
  have hdA : d ∈ titsA := titsD_le_titsA hdD
  have hmemK₁ : ∀ y : Equiv.Perm (Fin 1755), y ∈ K₁ ↔ d⁻¹ * y * d ∈ titsK0 := by
    intro y
    rw [hd]
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [mul_assoc] using hz
    · intro hy
      exact ⟨d⁻¹ * y * d, hy, by simp [mul_assoc]⟩
  have hnorm : ∀ k ∈ K, ∀ y : Equiv.Perm (Fin 1755), y ∈ K₁ →
      ((k : titsA) : Equiv.Perm (Fin 1755)) * y * ((k : titsA) : Equiv.Perm (Fin 1755))⁻¹ ∈ K₁ := by
    intro k hk y hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hzD : ((k : titsA) : Equiv.Perm (Fin 1755)) * z * ((k : titsA) : Equiv.Perm (Fin 1755))⁻¹ ∈
        titsD := by
      have hnD : (titsD.subgroupOf titsA).Normal := Subgroup.normal_of_index_eq_two titsD_index
      have := hnD.conj_mem (t1Inc z) (by rw [Subgroup.mem_subgroupOf]; exact z.2) k
      rw [Subgroup.mem_subgroupOf] at this
      simpa [t1Inc_apply] using this
    refine ⟨⟨_, hzD⟩, ?_, rfl⟩
    show t1Inc ⟨_, hzD⟩ ∈ K
    have e : t1Inc ⟨_, hzD⟩ = k * t1Inc z * k⁻¹ := by
      apply Subtype.ext
      simp [t1Inc_apply]
    rw [e]
    exact mul_mem (mul_mem hk hz) (inv_mem hk)
  set dA : titsA := ⟨d, hdA⟩ with hdA'
  have hle : K ≤ ruE0.map (MulAut.conj dA).toMonoidHom := by
    intro k hk
    refine ⟨dA⁻¹ * k * dA, ?_, by simp [mul_assoc]⟩
    apply mem_ruE0_of_normalizes
    intro j
    have hk' := hnorm k hk
    have hki := hnorm k⁻¹ (inv_mem hk)
    constructor
    · intro hj
      have h1 : d * j * d⁻¹ ∈ K₁ := (hmemK₁ _).2 (by simpa [mul_assoc] using hj)
      have h2 := hk' _ h1
      rw [hmemK₁] at h2
      simpa [mul_assoc, hdA'] using h2
    · intro hj
      have h1 : d * ((dA⁻¹ * k * dA : titsA) : Equiv.Perm (Fin 1755)) * j *
          ((dA⁻¹ * k * dA : titsA) : Equiv.Perm (Fin 1755))⁻¹ * d⁻¹ ∈ K₁ :=
        (hmemK₁ _).2 (by simpa [mul_assoc] using hj)
      have h2 := hki _ h1
      rw [hmemK₁] at h2
      simpa [mul_assoc, hdA'] using h2
  refine ⟨dA, Subgroup.eq_of_le_of_card_ge hle ?_⟩
  rw [Subgroup.card_map_of_injective (MulAut.conj dA).injective, card_ruE0]
  exact hKcard

end CFSG.Quasithin.RuRank3
