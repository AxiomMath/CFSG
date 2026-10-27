module

public import CFSG.RankThree.PartOne.KC.UnitaryNoninnerPlaneGeneral
public import CFSG.RankThree.PartOne.FOC.Assemble
public import CFSG.RankThree.PartOne.S11c.Sec66TFamily

public section

namespace CFSG.RankThree.PartOne.FOC

open Subgroup CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.Sec66T (fixSub innerAut fixSubEquiv congr_self_eq)
open CFSG.RankThree.Classical

theorem outerComp_psu {ℓ f n p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
    (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) (hp : p.Prime) (hp5 : 5 ≤ p) (hpℓ : p ≠ ℓ)
    (hZ : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1))
    [Finite (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))] :
    OuterComp p (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  intro _ β hβp hβout _ y hβy hyp E hE
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hfinK : Finite K := h.finite
  have hβ1 : β ≠ 1 := fun h1 => hβout (h1 ▸ (innerAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))).one_mem)
  have hord : orderOf β = p := orderOf_eq_prime hβp hβ1
  have hC1 : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  set σ := primeFormFieldFactor h hC1 hn hne β with hσdef
  have hσp : σ ^ p = 1 := by rw [hσdef, ← map_pow, hβp, map_one]
  have hσ1 : σ ≠ 1 := by
    intro hσ1
    have hD : β ∈ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      rw [← ker_primeFormFieldFactor h hC1 hn hne]
      exact hσ1
    exact hβout (pElement_mem_inner_of_not_dvd_gcd h hn hne hp hZ hD hβp)
  have hσord : orderOf σ = p := orderOf_eq_prime hσp hσ1
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn hne hp hp2 hpℓ β hord σ
      hσdef.symm hσord
  have hZ' : ¬ p ∣ Nat.card (normOneScalars h
      (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n) := by
    rw [card_normOneScalars_one h (by omega)]
    exact hZ
  obtain ⟨-, -, -, -, -, -, -, -, -, hsimp, hexc⟩ :=
    prime_subfield_fixed_group_package h hp hp2 hσord n hn hne hZ'
  set u := primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) M with hu
  set fσ := primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ with hfσ
  have hβu : β = u * fσ * u⁻¹ := by
    have : u⁻¹ * β * u = fσ := hM
    rw [← this]
    group
  have hcongr : MulAut.congr (u : (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ≃* (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) fσ = β := (congr_self_eq u fσ).trans hβu.symm
  have e1 : ↥(fixSub fσ) ≃* ↥(fixSub β) :=
    (fixSubEquiv (u : (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ≃* (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) fσ).trans (MulEquiv.subgroupCongr (congrArg fixSub hcongr))
  by_cases hq0 : n = 3 ∧ ℓ ^ (f / p) = 2
  ·
    obtain ⟨-, hord72⟩ := hexc hq0 (by omega)
    have hyfix : ((e1.symm ⟨y, hβy⟩ : ↥(fixSub fσ)) : (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) ∈ fieldFixedPSU h n σ :=
      (e1.symm ⟨y, hβy⟩).2
    have hy'p : ((e1.symm ⟨y, hβy⟩ : ↥(fixSub fσ)) : (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) ^ p = 1 := by
      have : (⟨y, hβy⟩ : ↥(fixSub β)) ^ p = 1 := Subtype.ext (by simpa using hyp)
      have h2 := congrArg (fun z => (e1.symm z : ↥(fixSub fσ))) this
      simpa [map_pow] using congrArg Subtype.val h2
    have hy'1 : ((e1.symm ⟨y, hβy⟩ : ↥(fixSub fσ)) : (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) = 1 := by
      by_contra hne1
      apply hord72 _ hyfix
      exact orderOf_eq_prime hy'p hne1
    have : (⟨y, hβy⟩ : ↥(fixSub β)) = 1 := by
      apply e1.symm.injective
      apply Subtype.ext
      rw [map_one]
      exact hy'1
    have hy1 : y = 1 := congrArg Subtype.val this
    rw [hy1]
    exact E.one_mem
  · obtain ⟨hsimple, -⟩ := hsimp hq0
    have : IsSimpleGroup ↥(fixSub fσ) := hsimple
    have : IsSimpleGroup ↥(fixSub β) := e1.symm.isSimpleGroup
    rw [eq_of_isComponentOf_simple hE]
    exact hβy

end CFSG.RankThree.PartOne.FOC
