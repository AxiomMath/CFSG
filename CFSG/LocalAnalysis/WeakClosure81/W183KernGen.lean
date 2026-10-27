module

public import CFSG.LocalAnalysis.WeakClosure81.W18KernGroup

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup
open scoped commutatorElement

variable {Y : Type*} [Group Y] [Finite Y]

namespace KernSetting

variable {Kk F P : Subgroup Y}

theorem le_centralizer_of_odd_of_ne_bot (h : KernSetting Kk F P) {A₀ Fo : Subgroup Y}
    (hA2 : IsPGroup 2 ↥A₀) (hA0 : A₀ ≠ ⊥) (hC : A₀ ≤ centralizer (Fo : Set Y))
    (hFo : Fo.Normal) (hFoK : Fo ≤ Kk) (hodd : Odd (Nat.card ↥Fo))
    (hself : ∀ y ∈ Kk, (∀ f ∈ Fo, y * f = f * y) → y ∈ Fo) :
    P ≤ centralizer (Fo : Set Y) := by
  have hA0K : A₀ ⊓ Kk = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyA0, hyK⟩ := Subgroup.mem_inf.mp hy
    have hyFo : y ∈ Fo := hself y hyK fun f hf => (mem_centralizer_iff.mp (hC hyA0) f hf).symm
    have horder_dvd : orderOf y ∣ Nat.card ↥Fo := Subgroup.orderOf_dvd_natCard Fo hyFo
    have hyodd : Odd (orderOf y) := hodd.of_dvd_nat horder_dvd
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := hA2.exists_orderOf_eq_pow ⟨y, hyA0⟩
    have hk' : orderOf y = 2 ^ k := (Subgroup.orderOf_coe (⟨y, hyA0⟩ : ↥A₀)).trans hk
    have hk0 : k = 0 := by
      by_contra hk0
      have h2dvd : 2 ∣ 2 ^ k := dvd_pow_self 2 hk0
      exact Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr h2dvd) (hk' ▸ hyodd)
    rw [Subgroup.mem_bot]
    exact orderOf_eq_one_iff.mp (by rw [hk', hk0, pow_zero])
  have hA0notK : ¬ A₀ ≤ Kk := by
    intro hle
    have : A₀ = ⊥ := by
      rw [← hA0K]
      exact (inf_eq_left.mpr hle).symm
    exact hA0 this
  let N : Subgroup Y := Subgroup.normalClosure (A₀ : Set Y)
  have hNnorm : N.Normal := Subgroup.normalClosure_normal
  have hNnotK : ¬ N ≤ Kk := fun hle =>
    hA0notK (Subgroup.subset_normalClosure.trans hle)
  have hPN : P ≤ N := h.le_of_not_le N hNnorm hNnotK
  have hNC : N ≤ centralizer (Fo : Set Y) := by
    haveI : Fo.Normal := hFo
    haveI : (centralizer (Fo : Set Y)).Normal := inferInstance
    exact Subgroup.normalClosure_le_normal fun x hx => hC hx
  exact hPN.trans hNC

theorem kern_eq_centralizer_of_ne_bot (h : KernSetting Kk F P)
    (hA : ∀ N : Subgroup Y, N.Normal → N ≤ Kk → Odd (Nat.card ↥N) →
      ∃ A₀ : Subgroup Y, IsPGroup 2 ↥A₀ ∧ A₀ ≠ ⊥ ∧ A₀ ≤ centralizer (N : Set Y)) :
    ⁅P, P⁆ = P ∧ P = F ∧ Kk ≤ P ∧ Kk = centralizer (P : Set Y) ∧ Odd (Nat.card ↥Kk) := by
  obtain ⟨hperf, hPF⟩ := h.perfect_core
  obtain ⟨Fo, hFoN, hFoK, hFoodd, hself⟩ := h.exists_odd_normal
  obtain ⟨A₀, hA2, hA0, hAC⟩ := hA Fo hFoN hFoK hFoodd
  have hFoP : Fo ≤ P := h.le_of_odd hFoodd
  have hPC : P ≤ centralizer (Fo : Set Y) :=
    h.le_centralizer_of_odd_of_ne_bot hA2 hA0 hAC hFoN hFoK hFoodd hself
  have hKP : Kk ⊓ P ≤ Fo := fun y hy =>
    hself y hy.1 fun f hf => (mem_centralizer_iff.1 (hPC hy.2) f hf).symm
  have hFoC : Fo ≤ centralizer (P : Set Y) := fun f hf =>
    mem_centralizer_iff.2 fun p hp => (mem_centralizer_iff.1 (hPC hp) f hf).symm
  have hKC : Kk ≤ centralizer (P : Set Y) := h.le_centralizer_of_inf_le hperf hKP hFoC
  have hCP : centralizer (P : Set Y) ≤ P := h.centralizer_le
  have hZK : P ⊓ centralizer (P : Set Y) ≤ Kk := h.inf_centralizer_le hPF
  have hKP' : Kk ≤ P := hKC.trans hCP
  have hKFo : Kk = Fo := le_antisymm (fun y hy => hKP ⟨hy, hKP' hy⟩) hFoK
  exact ⟨hperf, ((sup_eq_left.2 hKP').symm.trans hPF), hKP',
    le_antisymm hKC fun y hy => hZK ⟨hCP hy, hy⟩, hKFo ▸ hFoodd⟩

end KernSetting

end CFSG.LocalAnalysis.WeakClosure81

end
