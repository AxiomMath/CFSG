module

public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofReeConj
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofSU3Kind
public import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
public import CFSG.RankThree.PartTwo.KFacts.K71IdentPSU3
public import CFSG.RankThree.PartTwo.Sec8.Item82Res2ProofSLThree
public import CFSG.RankThree.PartTwo.Sec8.Item87ProofGamma

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof

open CFSG CFSG.RankThree.PartTwo CFSG.LieType.Ree
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

section Center

variable {M : Type*} [Group M] [Finite M]

theorem exists_fixed_mem_center {S : Subgroup M} {α : MulAut M} (hα3 : α ^ 3 = 1)
    (hS : ∀ s ∈ S, α s ∈ S) (hZ : Nat.card (Subgroup.center S) = 3) :
    ∃ z ∈ S, (∀ s ∈ S, z * s = s * z) ∧ orderOf z = 3 ∧ α z = z := by
  classical
  have hS' : ∀ s ∈ S, α⁻¹ s ∈ S := by
    intro s hs
    have hα2 : α⁻¹ = α ^ 2 := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, hα3]
    rw [hα2, sq, MulAut.mul_apply]
    exact hS _ (hS _ hs)
  set αS : S ≃* S :=
    { toFun := fun s => ⟨α s, hS s s.2⟩
      invFun := fun s => ⟨α⁻¹ s, hS' s s.2⟩
      left_inv := fun s => Subtype.ext (by simp)
      right_inv := fun s => Subtype.ext (by simp)
      map_mul' := fun s t => Subtype.ext (by simp) } with hαS
  have hαS3 : ∀ s : S, αS (αS (αS s)) = s := by
    intro s
    apply Subtype.ext
    change α (α (α s)) = s
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← pow_three', hα3, MulAut.one_apply]
  obtain ⟨z₀, hz₀1⟩ : ∃ z₀ : Subgroup.center S, z₀ ≠ 1 := by
    by_contra h
    push Not at h
    have : Subsingleton (Subgroup.center S) := ⟨fun x y => by rw [h x, h y]⟩
    have h1 := Nat.card_unique (α := Subgroup.center S)
    rw [hZ] at h1
    norm_num at h1
  have hord : orderOf z₀ = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hdvd : orderOf z₀ ∣ 3 := hZ ▸ orderOf_dvd_natCard z₀
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz₀1
    · exact h
  have hzp : Subgroup.zpowers z₀ = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hord, hZ]
  have hz₀c : (z₀ : S) ∈ Subgroup.center S := z₀.2
  have hαz : αS z₀ ∈ Subgroup.center S := (MulEquivClass.apply_mem_center_iff αS).2 hz₀c
  obtain ⟨j, hj⟩ := (Subgroup.mem_zpowers_iff (g := z₀)).mp
    (hzp ▸ Subgroup.mem_top (⟨αS z₀, hαz⟩ : Subgroup.center S))
  have hj' : (z₀ : S) ^ (j % 3) = αS z₀ := by
    have h1 := congrArg Subtype.val hj
    rw [← zpow_mod_orderOf, hord] at h1
    simpa using h1
  have hz3 : (z₀ : S) ^ 3 = 1 := by
    have := pow_orderOf_eq_one z₀
    rw [hord] at this
    exact congrArg Subtype.val this
  have hzne : (z₀ : S) ≠ 1 := fun h => hz₀1 (Subtype.ext h)
  have hfix : αS z₀ = z₀ := by
    have hr : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
    rcases hr with h | h | h
    · exfalso
      rw [h, zpow_zero] at hj'
      apply hzne
      have h2 := congrArg αS.symm hj'
      rw [map_one, MulEquiv.symm_apply_apply] at h2
      exact h2.symm
    · rw [h, zpow_one] at hj'
      exact hj'.symm
    · exfalso
      rw [h] at hj'
      have hsq : αS z₀ = (z₀ : S) ^ 2 := by rw [← hj']; norm_cast
      have h1 : αS (αS z₀) = z₀ := by
        rw [hsq, map_pow, hsq, ← pow_mul]
        rw [show (z₀ : S) ^ (2 * 2) = (z₀ : S) ^ 3 * z₀ by rw [← pow_succ]]
        rw [hz3, one_mul]
      have h2 := hαS3 z₀
      rw [h1, hsq] at h2
      apply hzne
      have h3 : (z₀ : S) * z₀ = z₀ * 1 := by rw [mul_one, ← sq, h2]
      exact mul_left_cancel h3
  refine ⟨((z₀ : S) : M), (z₀ : S).2, fun s hs => ?_, ?_, ?_⟩
  · have := Subgroup.mem_center_iff.mp hz₀c ⟨s, hs⟩
    exact (congrArg Subtype.val this).symm
  · rw [orderOf_submonoid, orderOf_submonoid, hord]
  · exact congrArg Subtype.val hfix

end Center


section Map

variable {M N : Type*} [Group M] [Group N]

theorem map_centralizer_singleton (e : M ≃* N) (z : M) :
    (Subgroup.centralizer ({z} : Set M)).map e.toMonoidHom =
      Subgroup.centralizer ({e z} : Set N) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, hx]
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hy]

theorem card_centralizer_singleton_eq (e : M ≃* N) (z : M) :
    Nat.card (Subgroup.centralizer ({z} : Set M)) =
      Nat.card (Subgroup.centralizer ({e z} : Set N)) := by
  rw [← map_centralizer_singleton e z,
    Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]

end Map

theorem card_center_statedSU_three {f : ℕ} (hf : Odd f) (hf2 : 2 ≤ f) {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = (2 ^ f) ^ 2) :
    Nat.card (Subgroup.center (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ f) F)) = 3 := by
  have hf1 : 1 ≤ f := hf.pos
  have h : UnitaryFieldData 2 f F := ⟨Nat.prime_two, hf1, by rw [hF, ← pow_mul, mul_comm]⟩
  have : CharP F 2 := h.charP
  have hdvd : Nat.card (Subgroup.center (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ f) F)) ∣ 3 :=
    (Item87Proof.isQuasisimple_statedSU_three hF hf2).2
  obtain ⟨ω, hω, hbar⟩ := CFSG.RankThree.PartOne.SEITZQ1.q1_exists_omega h hf
  obtain ⟨x₀, hx₀⟩ := ReeF4Cent2Proof.exists_scalar_unitarySU h hω hbar
  have hx₀c : x₀ ∈ Subgroup.center (unitarySU 2 f F 3) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    apply Units.ext
    change ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * ((x₀ : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = ((x₀ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
    rw [hx₀]
    exact (Matrix.scalar_commute ω (fun _ => Commute.all _ _) _).symm
  have hx₀1 : x₀ ≠ 1 := by
    intro h1
    have h2 := congrArg (fun x : unitarySU 2 f F 3 =>
      ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0) h1
    simp only [hx₀, Matrix.scalar_apply, Matrix.diagonal_apply_eq, Subgroup.coe_one,
      Units.val_one, Matrix.one_apply_eq] at h2
    rw [h2] at hω
    have h2F : (2 : F) = 0 := CharTwo.two_eq_zero
    have : (1 : F) = 0 := by linear_combination hω - h2F
    exact one_ne_zero this
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exfalso
    have : Subsingleton (Subgroup.center (unitarySU 2 f F 3)) :=
      (Nat.card_eq_one_iff_unique.mp h1).1
    have := Subsingleton.elim (⟨x₀, hx₀c⟩ : Subgroup.center (unitarySU 2 f F 3)) 1
    exact hx₀1 (congrArg Subtype.val this)
  · exact h3


section Core



theorem exists_fixed_pow_four_of_ree {M : Type} [Group M] [Finite M] {k : ℕ} (hk : 1 ≤ k)
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * k + 1))
    (e : M ≃* ReeTag.F4.reeGamma K k) {α : MulAut M} (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1)
    {b : ℕ} {k' : Type} [Field k'] [Finite k'] [CharP k' ReeTag.F4.prime]
    (hk' : Nat.card k' = 2 ^ (2 * b + 1)) (φ : Sec4.autFix α ≃* ReeTag.F4.reeGamma k' b)
    {S : Subgroup M} (hS : ∀ s ∈ S, α s ∈ S) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ (2 * k + 1)) ^ 2)
    (ψ : S ≃* CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ (2 * k + 1)) F) :
    (∃ s ∈ S, α s ≠ s) ∧ ∃ u ∈ S, α u = u ∧ u ^ 4 = 1 ∧ u ^ 2 ≠ 1 := by
  classical
  have hodd : Odd (2 * k + 1) := odd_two_mul_add_one k
  have hU : UnitaryFieldData 2 (2 * k + 1) F :=
    ⟨Nat.prime_two, by omega, by rw [hF, ← pow_mul, mul_comm]⟩
  have hZ : Nat.card (Subgroup.center S) = 3 := by
    rw [Nat.card_congr (Subgroup.centerCongr ψ).toEquiv]
    exact card_center_statedSU_three hodd (by omega) hF
  obtain ⟨z, hzS, hzc, hz3, hαz⟩ := exists_fixed_mem_center hα3 hS hZ
  have hcardS : Nat.card S = Nat.card (unitarySU 2 (2 * k + 1) F 3) :=
    Nat.card_congr ψ.toEquiv
  have hez : orderOf (e z) = 3 := by rw [MulEquiv.orderOf_eq, hz3]
  obtain ⟨ι⟩ := centralizer_mulEquiv_unitarySU k K hK (e z) hez
  have hcardC : Nat.card (Subgroup.centralizer ({z} : Set M)) =
      Nat.card (unitarySU 2 (2 * k + 1) (GaloisField 2 (2 * (2 * k + 1))) 3) := by
    rw [card_centralizer_singleton_eq e z]
    exact Nat.card_congr ι.toEquiv
  have hK'' : UnitaryFieldData 2 (2 * k + 1) (GaloisField 2 (2 * (2 * k + 1))) :=
    ⟨Nat.prime_two, by omega, GaloisField.card 2 _ (by omega)⟩
  have hle : S ≤ Subgroup.centralizer ({z} : Set M) := by
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hzc s hs).symm
  have hSC : S = Subgroup.centralizer ({z} : Set M) := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hcardC, hcardS, KFacts.card_unitarySU_three hU, KFacts.card_unitarySU_three hK'']
  have hzF : z ∈ Sec4.autFix α := hαz
  set zF : Sec4.autFix α := ⟨z, hzF⟩
  have hφz : orderOf (φ zF) = 3 := by
    rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact hz3
  obtain ⟨ι'⟩ := centralizer_mulEquiv_unitarySU b k' hk' (φ zF) hφz
  have hb' : UnitaryFieldData 2 (2 * b + 1) (GaloisField 2 (2 * (2 * b + 1))) :=
    ⟨Nat.prime_two, by omega, GaloisField.card 2 _ (by omega)⟩
  set CF := Subgroup.centralizer ({zF} : Set (Sec4.autFix α)) with hCF
  have hCFmap : CF.map φ.toMonoidHom = Subgroup.centralizer ({φ zF} : Set _) :=
    map_centralizer_singleton φ zF
  set ιF : CF ≃* unitarySU 2 (2 * b + 1) (GaloisField 2 (2 * (2 * b + 1))) 3 :=
    ((CF.equivMapOfInjective φ.toMonoidHom φ.injective).trans
      (MulEquiv.subgroupCongr hCFmap)).trans ι' with hιF
  have hsplit : ∃ u : M, u ∈ S ∧ α u = u ∧ u ^ 4 = 1 ∧ u ^ 2 ≠ 1 := by
    obtain ⟨u₀, hu₀4, hu₀2⟩ := exists_unitarySU_pow_four hb' (odd_two_mul_add_one b)
    set u₁ : CF := ιF.symm u₀
    set u : M := ((u₁ : Sec4.autFix α) : M)
    have hu₁4 : u₁ ^ 4 = 1 := by rw [← map_pow, hu₀4, map_one]
    have hu₁2 : u₁ ^ 2 ≠ 1 := by
      intro h1
      apply hu₀2
      have := congrArg ιF h1
      rwa [map_pow, MulEquiv.apply_symm_apply, map_one] at this
    refine ⟨u, ?_, (u₁ : Sec4.autFix α).2, ?_, ?_⟩
    · rw [hSC, Subgroup.mem_centralizer_singleton_iff]
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp u₁.2
      exact congrArg Subtype.val h1
    · have h1 := congrArg (fun x : CF => ((x : Sec4.autFix α) : M)) hu₁4
      simpa using h1
    · intro h1
      apply hu₁2
      apply Subtype.ext
      apply Subtype.ext
      simpa using h1
  refine ⟨?_, hsplit⟩
  by_contra hfixall
  push Not at hfixall
  have hSF : ∀ s ∈ S, s ∈ Sec4.autFix α := fun s hs => hfixall s hs
  have hdvd1 : Nat.card S ∣ Nat.card CF := by
    have hle' : S.subgroupOf (Sec4.autFix α) ≤ CF := by
      intro x hx
      rw [hCF, Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      exact (hzc x hx).symm
    have h1 := Subgroup.card_dvd_of_le hle'
    have h2 : Nat.card (S.subgroupOf (Sec4.autFix α)) = Nat.card S :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSF).toEquiv
    rwa [h2] at h1
  have hv1 : 3 * (2 * k + 1) ≤ 3 * (2 * b + 1) := by
    have e1 : padicValNat 2 (Nat.card S) = 3 * (2 * k + 1) := by
      rw [Nat.card_congr ψ.toEquiv]
      exact Item82Proof.padicValNat_card_statedSU_three (by omega) hF
    have e2 : padicValNat 2 (Nat.card CF) = 3 * (2 * b + 1) := by
      rw [Nat.card_congr ιF.toEquiv]
      exact Item82Proof.padicValNat_card_statedSU_three (by omega) (by
        rw [GaloisField.card 2 _ (by omega), ← pow_mul, mul_comm])
    have hCF0 : Nat.card CF ≠ 0 := Nat.card_pos.ne'
    rw [← e1, ← e2]
    exact (padicValNat_dvd_iff_le hCF0).mp ((pow_padicValNat_dvd).trans hdvd1)
  have hcardRee : ∀ (c : ℕ) (k₀ : Type) [Field k₀] [Finite k₀] [CharP k₀ ReeTag.F4.prime],
      Nat.card k₀ = 2 ^ (2 * c + 1) → padicValNat 2 (Nat.card (ReeTag.F4.reeGamma k₀ c)) =
        (2 * c + 1) * 12 := by
    intro c k₀ _ _ _ hk₀
    rw [(LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion c k₀ hk₀).1]
    obtain ⟨r, hr, hr'⟩ := KFacts.exists_two_part_ree (q := 2 ^ (2 * c + 1)) (f := 2 * c + 1) rfl
      (by omega)
    rw [hr']
    rw [padicValNat.mul (pow_ne_zero _ (by norm_num)) hr.pos.ne', padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (fun h2 => (Nat.not_even_iff_odd.mpr hr)
        (even_iff_two_dvd.mpr h2)), add_zero]
  have hdvd2 : Nat.card (Sec4.autFix α) ∣ Nat.card M := Subgroup.card_subgroup_dvd_card _
  have hv2 : (2 * b + 1) * 12 ≤ (2 * k + 1) * 12 := by
    rw [← hcardRee b k' hk', ← hcardRee k K hK, ← Nat.card_congr φ.toEquiv,
      ← Nat.card_congr e.toEquiv]
    exact (padicValNat_dvd_iff_le Nat.card_pos.ne').mp ((pow_padicValNat_dvd).trans hdvd2)
  have hbk : b = k := by omega
  subst hbk
  have hcardeq : Nat.card (Sec4.autFix α) = Nat.card M := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_congr e.toEquiv,
      (LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion b k' hk').1,
      (LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion b K hK).1]
  have htop : Sec4.autFix α = ⊤ := Subgroup.eq_top_of_card_eq _ hcardeq
  apply hα1
  ext x
  have hx : x ∈ Sec4.autFix α := htop ▸ Subgroup.mem_top x
  exact hx

end Core

end CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof
