module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralSylowTransferDerived

public section

namespace CFSG.RankThree.CentralExtension

open Subgroup
open scoped commutatorElement

universe u

section Reduction

variable {E : Type*} [Group E]

@[expose] def primeComplOfCentral (p : ℕ) (C : Subgroup E) (hC : C ≤ center E) : Subgroup E where
  carrier := {c | c ∈ C ∧ (orderOf c).Coprime p}
  one_mem' := ⟨C.one_mem, by rw [orderOf_one]; exact Nat.coprime_one_left p⟩
  mul_mem' := fun {a b} ha hb => by
    refine ⟨C.mul_mem ha.1 hb.1, Nat.Coprime.coprime_dvd_left ?_
      (Nat.coprime_mul_iff_left.2 ⟨ha.2, hb.2⟩)⟩
    have hab : Commute a b := (mem_center_iff.1 (hC hb.1) a)
    exact (hab.orderOf_mul_dvd_lcm).trans (Nat.lcm_dvd_mul _ _)
  inv_mem' := fun {a} ha => ⟨C.inv_mem ha.1, by rw [orderOf_inv]; exact ha.2⟩

theorem sylow_ker_eq_bot_of_pKernel {p : ℕ} [hp : Fact p.Prime] {S : Type*} [Group S]
    {E : Type u} [Group E] [Finite E] [Group.IsPerfect E] (π : E →* S)
    (hπ : Function.Surjective π) (hC : π.ker ≤ center E)
    (h : ∀ (E' : Type u) [Group E'] [Finite E'] [Group.IsPerfect E'] (π' : E' →* S),
      Function.Surjective π' → π'.ker ≤ center E' → IsPGroup p π'.ker → π'.ker = ⊥)
    (Cp : Sylow p π.ker) : (Cp : Subgroup π.ker) = ⊥ := by
  set K := primeComplOfCentral p π.ker hC with hKdef
  have hKker : K ≤ π.ker := fun c hc => hc.1
  have : K.Normal := normal_of_le_center (hKker.trans hC)
  let π' : E ⧸ K →* S := QuotientGroup.lift K π hKker
  have hπ' : Function.Surjective π' := fun s => by
    obtain ⟨e, rfl⟩ := hπ s
    exact ⟨QuotientGroup.mk e, rfl⟩
  have hker' : π'.ker = π.ker.map (QuotientGroup.mk' K) := QuotientGroup.ker_lift K π hKker
  have hcent : π'.ker ≤ center (E ⧸ K) := by
    rw [hker']
    rintro _ ⟨c, hc, rfl⟩
    refine mem_center_iff.2 fun g => ?_
    induction g using QuotientGroup.induction_on with
    | H g =>
      change (QuotientGroup.mk g : E ⧸ K) * QuotientGroup.mk c =
        QuotientGroup.mk c * QuotientGroup.mk g
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.1 (hC hc) g]
  have hpgrp : IsPGroup p π'.ker := by
    rintro ⟨x, hx⟩
    rw [hker'] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    set a := (orderOf c).factorization p with ha
    have hord0 : orderOf c ≠ 0 := (isOfFinOrder_of_finite c).orderOf_pos.ne'
    have hdvd : p ^ a ∣ orderOf c := Nat.ordProj_dvd _ _
    have hcop : (orderOf (c ^ p ^ a)).Coprime p := by
      rw [orderOf_pow_of_dvd (pow_ne_zero _ hp.out.ne_zero) hdvd]
      exact (Nat.coprime_ordCompl hp.out hord0).symm
    refine ⟨a, Subtype.ext ?_⟩
    change (QuotientGroup.mk' K c) ^ p ^ a = 1
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨π.ker.pow_mem hc _, hcop⟩
  have hbot := h (E ⧸ K) π' hπ' hcent hpgrp
  have hcop : ∀ c ∈ π.ker, (orderOf c).Coprime p := by
    intro c hc
    have h1 : QuotientGroup.mk' K c ∈ π'.ker := by rw [hker']; exact ⟨c, hc, rfl⟩
    rw [hbot, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1.2
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨k, hk⟩ := Cp.isPGroup' ⟨x, hx⟩
  have hk' : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcopx : (orderOf x).Coprime p := by
    rw [← Subgroup.orderOf_coe]
    exact hcop _ x.2
  have h1 : orderOf x = 1 :=
    Nat.Coprime.eq_one_of_dvd (hcopx.pow_right k) (orderOf_dvd_of_pow_eq_one hk')
  rw [orderOf_eq_one_iff] at h1
  rw [h1]
  exact one_mem _

end Reduction

section Endgame

theorem isCyclic_range_of_isPGroup {G K : Type*} [Group G] [Group K] {p : ℕ}
    (hG : IsPGroup p G) (hK : ∀ P : Sylow p K, IsCyclic P) (f : G →* K) : IsCyclic f.range := by
  have hR : IsPGroup p f.range := hG.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨P, hP⟩ := hR.exists_le_sylow
  have := hK P
  exact isCyclic_of_le hP

theorem eq_bot_of_complement_of_cyclic_quotient {E : Type*} [Group E] [Finite E]
    [Group.IsPerfect E] {p : ℕ} [hp : Fact p.Prime] {C U D : Subgroup E} (hCZ : C ≤ center E)
    (hCp : IsPGroup p C) (hCU : ∀ u ∈ U, ∃ c ∈ C, c⁻¹ * u ∈ D) (hCD : C ⊓ D = ⊥)
    (T : Sylow p E) (hTD : ∀ t ∈ (T : Subgroup E), ∀ d ∈ D, t * d * t⁻¹ ∈ D)
    {K : Type*} [Group K] (f : (T : Subgroup E) →* K) [IsCyclic f.range]
    (hfU : ∀ t : (T : Subgroup E), f t = 1 → (t : E) ∈ U)
    (hfD : ∀ t : (T : Subgroup E), (t : E) ∈ D → f t = 1) : C = ⊥ := by
  have hCnorm : C.Normal := normal_of_le_center hCZ
  have hCT : C ≤ (T : Subgroup E) := hCp.le_sylow_of_normal T
  have hNnorm : (D.subgroupOf (T : Subgroup E)).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    exact hTD g g.2 n hn⟩
  have hNf : D.subgroupOf (T : Subgroup E) ≤ f.ker := fun n hn => MonoidHom.mem_ker.2 (hfD n hn)
  let F : (T : Subgroup E) ⧸ D.subgroupOf (T : Subgroup E) →* K := QuotientGroup.lift _ f hNf
  have hF : ∀ t : (T : Subgroup E), F (QuotientGroup.mk t) = f t := fun _ => rfl
  have hFrange : F.range = f.range := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      induction x using QuotientGroup.induction_on with
      | H t => exact ⟨t, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨QuotientGroup.mk t, rfl⟩
  have : IsCyclic F.range := by rw [hFrange]; infer_instance
  have hkerF : F.rangeRestrict.ker ≤ center ((T : Subgroup E) ⧸ D.subgroupOf (T : Subgroup E)) := by
    rw [MonoidHom.ker_rangeRestrict]
    intro x hx
    induction x using QuotientGroup.induction_on with
    | H t =>
      rw [MonoidHom.mem_ker, hF] at hx
      obtain ⟨c, hc, hcd⟩ := hCU t (hfU t hx)
      have hmk : (QuotientGroup.mk t : (T : Subgroup E) ⧸ D.subgroupOf (T : Subgroup E)) =
          QuotientGroup.mk (⟨c, hCT hc⟩ : (T : Subgroup E)) := by
        rw [QuotientGroup.eq, mem_subgroupOf]
        simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
        have h1 := D.inv_mem hcd
        rwa [mul_inv_rev, inv_inv] at h1
      rw [hmk]
      refine mem_center_iff.2 fun g => ?_
      induction g using QuotientGroup.induction_on with
      | H s =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        exact Subtype.ext (mem_center_iff.1 (hCZ hc) s)
  have hcomm := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center F.rangeRestrict hkerF
  have hder : ⁅(T : Subgroup E), (T : Subgroup E)⁆ ≤ D := by
    rw [commutator_le]
    intro a ha b hb
    have h1 : (QuotientGroup.mk ⁅(⟨a, ha⟩ : (T : Subgroup E)), ⟨b, hb⟩⁆ :
        (T : Subgroup E) ⧸ D.subgroupOf (T : Subgroup E)) = 1 := by
      change (QuotientGroup.mk' (D.subgroupOf (T : Subgroup E)))
        ⁅(⟨a, ha⟩ : (T : Subgroup E)), ⟨b, hb⟩⁆ = 1
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm.is_comm.comm _ _
    rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
    exact h1
  have hCder := (CFSG.ShultStronglyClosedTI.MiscAlgebra.central_sylow_transfer_derived T C hCZ
    hCp).1
  rw [eq_bot_iff, ← hCD]
  exact le_inf le_rfl (hCder.trans hder)

end Endgame

end CFSG.RankThree.CentralExtension
