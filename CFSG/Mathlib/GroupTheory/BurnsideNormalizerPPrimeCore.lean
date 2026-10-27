module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.GroupTheory.BurnsideNormalComplement
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.GroupTheory

open Subgroup

variable {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]

omit [Finite X] [Fact (Nat.Prime p)] in
theorem normalizer_subgroupOf_le_centralizer_of_isSylowOf {Q P : Subgroup X}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P Q)
    (hNC : Subgroup.normalizer (P : Set X) ⊓ Q ≤ Subgroup.centralizer (P : Set X)) :
    Subgroup.normalizer ((P.subgroupOf Q) : Set ↥Q) ≤
      Subgroup.centralizer ((P.subgroupOf Q) : Set ↥Q) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  apply Subtype.ext
  have hxN : (x : X) ∈ Subgroup.normalizer (P : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have hzQ : z ∈ Q := hP.le hz
      have hzP : (⟨z, hzQ⟩ : ↥Q) ∈ P.subgroupOf Q := hz
      have hconj := (Subgroup.mem_normalizer_iff.mp hx ⟨z, hzQ⟩).mp hzP
      rw [Subgroup.mem_subgroupOf] at hconj
      simpa using hconj
    · intro hz
      have hzQ : z ∈ Q := by
        have hxq : (x : X) ∈ Q := x.2
        have hzx : (x : X) * z * (x : X)⁻¹ ∈ Q := hP.le hz
        rw [show z = (x : X)⁻¹ * ((x : X) * z * (x : X)⁻¹) * (x : X) by group]
        exact Q.mul_mem (Q.mul_mem (Q.inv_mem hxq) hzx) hxq
      have hxinv : x⁻¹ ∈ Subgroup.normalizer ((P.subgroupOf Q) : Set ↥Q) :=
        Subgroup.inv_mem _ hx
      have hzP : (⟨(x : X) * z * (x : X)⁻¹, hP.le hz⟩ : ↥Q) ∈ P.subgroupOf Q := hz
      have hconj := (Subgroup.mem_normalizer_iff.mp hxinv
        ⟨(x : X) * z * (x : X)⁻¹, hP.le hz⟩).mp hzP
      have hmem : (⟨z, hzQ⟩ : ↥Q) ∈ P.subgroupOf Q := by
        convert hconj using 1
        ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [Subgroup.mem_subgroupOf] at hmem
      simpa using hmem
  have hyP : (y : X) ∈ P := hy
  have := Subgroup.mem_centralizer_iff.mp
    (hNC (Subgroup.mem_inf.mpr ⟨hxN, x.2⟩)) (y : X) hyP
  simpa using this

theorem le_sup_pPrimeCore_of_isSylowOf_normalizer_le_centralizer {Q P : Subgroup X}
    [Q.Normal] (hP : CFSG.ABGLocalTools.IsSylowOf p P Q)
    (hNC : Subgroup.normalizer (P : Set X) ⊓ Q ≤ Subgroup.centralizer (P : Set X)) :
    Q ≤ P ⊔ CFSG.pPrimeCore p X := by
  classical
  obtain ⟨P', hP'⟩ := hP.exists_sylow_eq_subgroupOf
  have hNC' : Subgroup.normalizer ((P' : Subgroup ↥Q) : Set ↥Q) ≤
      Subgroup.centralizer ((P' : Subgroup ↥Q) : Set ↥Q) := by
    simpa [hP'] using
      normalizer_subgroupOf_le_centralizer_of_isSylowOf (p := p) hP hNC
  obtain ⟨K, hKnormal, hKp, -, -, hKchar, -, hKsup, -, -, -⟩ :=
    CFSG.GroupTheory.burnside_normal_complement P' hNC'
  set K₀ : Subgroup X := K.map Q.subtype with hK₀def
  have hK₀normal : K₀.Normal := by
    rw [hK₀def]
    let : K.Characteristic := hKchar
    exact ConjAct.normal_of_characteristic_of_normal (H := Q) (K := K)
  have hcard : Nat.card K₀ = Nat.card K := by
    rw [hK₀def]
    exact Subgroup.card_map_of_injective Q.subtype_injective
  have hcop : Nat.Coprime p (Nat.card K₀) := by
    rw [hcard]
    exact ((Fact.out : Nat.Prime p).coprime_iff_not_dvd).mpr hKp
  have hK₀le : K₀ ≤ CFSG.pPrimeCore p X :=
    CFSG.le_pPrimeCore_of_normal_coprime hK₀normal hcop
  have hsup : K₀ ⊔ P = Q := by
    have hmap : (P' : Subgroup ↥Q).map Q.subtype = P := by
      rw [hP', Subgroup.map_subgroupOf_eq_of_le hP.le]
    rw [hK₀def, ← hmap, ← Subgroup.map_sup, hKsup, Subgroup.map_top,
      Subgroup.range_subtype]
  rw [← hsup]
  exact sup_le (hK₀le.trans le_sup_right) le_sup_left

end CFSG.GroupTheory

end
