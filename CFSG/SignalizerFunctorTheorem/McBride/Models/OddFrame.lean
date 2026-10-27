module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.Frame
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Proposition12
import CFSG.SignalizerFunctorTheorem.McBride.Models.FrameItems
public import CFSG.SignalizerFunctorTheorem.McBride.Models.OddFrame.Core

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride

namespace OddFrame

variable {ℓ : ℕ} {X : Type*} [Group X] [Finite X]

theorem exists_core (f : MulAut X) (hℓ : ℓ = 3 ∨ ℓ = 5)
    (hC : Nat.card (signalizerFixedSubgroup f) = ℓ * (ℓ - 1))
    (hA : ∀ u : X, orderOf u = 2 → IsPGroup 2 (Subgroup.centralizer ({u} : Set X))) :
    ∃ c t : X, Core ℓ (signalizerFixedSubgroup f) c t ∧
      fixedFitting f = Subgroup.zpowers c := by
  have hodd := OddPrime.of_three_or_five hℓ
  have := Fact.mk hodd.prime
  obtain ⟨c, hcC, hcord, hnorm⟩ := exists_normal_zpowers hodd hC
  have h2C : 2 ∣ Nat.card (signalizerFixedSubgroup f) := by
    rw [hC]
    exact Dvd.dvd.mul_left hodd.two_dvd ℓ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t', ht'⟩ := exists_prime_orderOf_dvd_card' (G := signalizerFixedSubgroup f) 2 h2C
  have core : Core ℓ (signalizerFixedSubgroup f) c (t' : X) :=
    { odd := hodd
      invCent := hA
      card := hC
      mem_c := hcC
      ord_c := hcord
      norm := hnorm
      mem_t := t'.2
      ord_t := by rw [Subgroup.orderOf_coe, ht'] }
  have hcF : c ∈ fixedFitting f := by
    refine FrameItems.le_fittingSubgroupOf_of_normal_subgroupOf (N := Subgroup.zpowers c)
      core.zpowers_le ?_ core.zpowers_isPGroup.isNilpotent (Subgroup.mem_zpowers c)
    rw [Subgroup.normal_subgroupOf_iff core.zpowers_le]
    intro n y hn hy
    exact conj_mem_zpowers_of_conj (core.norm y hy) hn
  refine ⟨c, t', core, core.eq_zpowers_of_no_involution (fixedFitting_le f) hcF ?_⟩
  intro u hu hu2
  have hnil : Group.IsNilpotent (fixedFitting f) := CFSG.fittingSubgroupOf_isNilpotent _
  have hcop : (orderOf (⟨u, hu⟩ : fixedFitting f)).Coprime
      (orderOf (⟨c, hcF⟩ : fixedFitting f)) := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hu2, hcord]
    exact (Nat.coprime_primes Nat.prime_two hodd.prime).mpr (Ne.symm hodd.ne_two)
  have hcomm := Group.IsNilpotent.commute_of_orderOf_coprime hcop
  exact core.not_commute_c hu2 (congrArg Subtype.val hcomm.eq)

end OddFrame

open OddFrame in
theorem fixedCore1_eq_of_odd {ℓ : ℕ} {X : Type*} [Group X] [Finite X] (f : MulAut X)
    (hℓ : ℓ = 3 ∨ ℓ = 5) (hC : Nat.card (signalizerFixedSubgroup f) = ℓ * (ℓ - 1))
    (hA : ∀ u : X, orderOf u = 2 → IsPGroup 2 (Subgroup.centralizer ({u} : Set X))) :
    fixedCore1 f = signalizerFixedSubgroup f := by
  obtain ⟨c, t, core, hFit⟩ := exists_core f hℓ hC hA
  refine le_antisymm (fun x hx => hx.1) fun x hx => ⟨hx, fun y hy => ?_⟩
  rw [hFit, commutatorElement_def]
  exact core.commutator_mem hx hy

open OddFrame in
theorem eq_one_of_commute_fixed_of_odd {ℓ : ℕ} {X : Type*} [Group X] [Finite X] (f : MulAut X)
    (hℓ : ℓ = 3 ∨ ℓ = 5) (hC : Nat.card (signalizerFixedSubgroup f) = ℓ * (ℓ - 1))
    (hA : ∀ u : X, orderOf u = 2 → IsPGroup 2 (Subgroup.centralizer ({u} : Set X))) {x : X}
    (hx : ∀ y ∈ signalizerFixedSubgroup f, x * y = y * x) : x = 1 := by
  obtain ⟨c, t, core, -⟩ := exists_core f hℓ hC hA
  have hxZ : x ∈ Core.Z c := Core.mem_Z.mpr (hx c core.mem_c)
  exact eq_one_of_commute_of_odd (core.invCent t core.ord_t) (core.odd_orderOf_of_mem_Z hxZ)
    (hx t core.mem_t).symm

open OddFrame in
theorem Frame.of_odd {p ℓ : ℕ} {X : Type*} [Group X] [Finite X] (f : MulAut X)
    (hp : p.Prime) (hℓ : ℓ = 3 ∨ ℓ = 5) (hord : orderOf f = p)
    (hcop : Nat.Coprime p (Nat.card X)) (hsimple : IsSimpleGroup X)
    (hC : Nat.card (signalizerFixedSubgroup f) = ℓ * (ℓ - 1))
    (hsol : Group.IsSolvable (signalizerFixedSubgroup f))
    (hℓ2 : ¬ ℓ ^ 2 ∣ Nat.card X)
    (hA : ∀ u : X, orderOf u = 2 → IsPGroup 2 (Subgroup.centralizer ({u} : Set X)))
    (hB : ∀ S : Subgroup X, S ≠ ⊥ → IsPGroup 2 S →
      ¬ ℓ ∣ Nat.card (Subgroup.normalizer (S : Set X)))
    (hD : ∀ H : Subgroup X, H ≠ ⊤ → Group.IsSolvable H) : Frame p ℓ f := by
  obtain ⟨c, t, core, hFit⟩ := exists_core f hℓ hC hA
  have hodd := core.odd
  have hnab : ∃ a b : X, a * b ≠ b * a := by
    refine ⟨t, c, fun hcomm => ?_⟩
    have h2 : t * c * t⁻¹ = c := by rw [hcomm]; group
    have h3 : c * c = 1 := mul_eq_one_iff_eq_inv.mpr (h2.symm.trans core.conj_t)
    have h4 : ℓ ∣ 2 := core.ord_c ▸ orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
    have := Nat.le_of_dvd two_pos h4
    have := hodd.three_le
    omega
  have hZ : Subgroup.centralizer (fixedFitting f : Set X) = Core.Z c := by
    rw [hFit]
    exact centralizer_zpowers_eq c
  have hC0 : fixedFitting f ≠ signalizerFixedSubgroup f := by
    rw [hFit]
    intro heq
    have h1 := core.zpowers_card
    rw [heq, hC] at h1
    have h3 := hodd.three_le
    have h2 : ℓ * (ℓ - 1) = ℓ * 1 := by rw [mul_one]; exact h1
    have := Nat.eq_of_mul_eq_mul_left hodd.prime.pos h2
    omega
  refine
    { prime := hp
      prime_ℓ := hodd.prime
      ord := hord
      coprime := hcop
      simple := hsimple
      nonabelian := hnab
      fixed_solvable := hsol
      C0_ne_bot := ?_
      C0_pgroup := ?_
      C0_comm := ?_
      C0_sylow := ?_
      C0_ne := hC0
      C1_ne := ?_
      minimal := ?_
      centralizer_comm := ?_
      fpf := ?_
      normalizer_le := ?_
      overgroup := ?_ }
  · rw [hFit]
    intro hb
    exact core.c_ne_one (Subgroup.zpowers_eq_bot.mp hb)
  · rw [hFit]
    exact core.zpowers_isPGroup
  · rw [hFit]
    infer_instance
  · intro P hP hle
    rw [hFit] at hle ⊢
    exact core.sylow_max hℓ2 hP hle
  · rw [fixedCore1_eq_of_odd f hℓ hC hA]
    exact fun h => hC0 h.symm
  · intro N hNC hNn hN0
    rw [hFit]
    exact core.zpowers_le_of_normal hNC
      (fun n hn y hy => (Subgroup.normal_subgroupOf_iff hNC).mp hNn n y hn hy) hN0
  · rw [hZ]
    exact ⟨⟨fun a b => Subtype.ext (core.comm_Z a.2 b.2)⟩⟩
  · intro v hv hvP z hz hvz
    rw [hFit] at hvP
    rw [hFit, centralizer_zpowers_eq] at hz
    exact core.fpf hv hvP hz hvz
  · intro x hx
    rw [fixedNormalizer, hFit] at hx
    obtain ⟨z, hz, y, hy, rfl⟩ := core.normalizer_decomp hx
    exact ⟨z, by rw [hFit, centralizer_zpowers_eq]; exact hz, y, hy, rfl⟩
  · intro H hCH hH
    rw [fixedNormalizer, hFit]
    exact core.overgroup hB hD hℓ2 hCH hH

end CFSG.SignalizerFunctorTheorem.McBride
