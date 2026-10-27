module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34ModelL34
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs2
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs517
public import CFSG.RankThree.PartTwo.KFacts.L34Aut
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.KFacts.L34
open CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourOuter (diagGL)
open scoped commutatorElement

section Sylow

variable {k : Type} [Field k]

theorem exists_sylow_three_mulAut (hk : Nat.card k = 4) :
    ∃ R : Subgroup (MulAut (projectiveSL 3 k)),
      Nat.card R = 3 ^ (Nat.card (MulAut (projectiveSL 3 k))).factorization 3 ∧
        ∀ g ∈ R, g ^ 3 = 1 := by
  obtain ⟨u, hu⟩ := exists_units_ne_one hk
  set x := LinearFlag.conjAut 3 k (diagGL u)
  set y := (MulAut.conj (bP : projectiveSL 3 k) : MulAut (projectiveSL 3 k))
  have h3 := LinearThreeFourOuter.units_pow_three hk u
  have hx3 : x ^ 3 = 1 := by
    rw [← map_pow, pow_three, LinearThreeFourOuter.diagGL_mul, LinearThreeFourOuter.diagGL_mul,
      ← pow_three, h3, LinearThreeFourOuter.diagGL_one, map_one]
  have hy3 : y ^ 3 = 1 := by
    rw [← map_pow, pow_three_of_mem_eZero hk bP_mem_eZero, map_one]
  have hab : aP u * bP = bP * aP u := commute_of_mem_eZero hk aP_mem_eZero bP_mem_eZero
  have hxa : x (aP u)⁻¹ = (aP u)⁻¹ := by rw [map_inv, conjAut_diagGL_aP]
  have hz : ⁅x, y⁆ = MulAut.conj (aP u)⁻¹ := by
    rw [commutatorElement_def, CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv,
      conjAut_diagGL_bP hk hu, ← map_inv, ← map_mul]
    congr 1
    calc bP * (aP u)⁻¹ * bP⁻¹ = bP * ((aP u)⁻¹ * bP⁻¹) := by group
      _ = bP * (bP⁻¹ * (aP u)⁻¹) := by
          rw [show (aP u)⁻¹ * bP⁻¹ = (bP * aP u)⁻¹ by group, ← hab]
          group
      _ = (aP u)⁻¹ := by group
  have hzx : Commute ⁅x, y⁆ x := by
    rw [hz]
    show MulAut.conj (aP u)⁻¹ * x = x * MulAut.conj (aP u)⁻¹
    have := CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv x (aP u)⁻¹
    rw [hxa] at this
    calc MulAut.conj (aP u)⁻¹ * x = x * MulAut.conj (aP u)⁻¹ * x⁻¹ * x := by rw [this]
      _ = x * MulAut.conj (aP u)⁻¹ := by group
  have hzy : Commute ⁅x, y⁆ y := by
    rw [hz]
    show MulAut.conj (aP u)⁻¹ * MulAut.conj bP = MulAut.conj bP * MulAut.conj (aP u)⁻¹
    rw [← map_mul, ← map_mul]
    congr 1
    calc (aP u)⁻¹ * bP = (aP u)⁻¹ * (bP * aP u) * (aP u)⁻¹ := by group
      _ = (aP u)⁻¹ * (aP u * bP) * (aP u)⁻¹ := by rw [hab]
      _ = bP * (aP u)⁻¹ := by group
  have hz1 : ⁅x, y⁆ ≠ 1 := by
    rw [hz]
    intro h
    exact aP_ne_one hk hu (inv_eq_one.mp (conj_injective hk (h.trans (map_one _).symm)))
  have : Finite (MulAut (projectiveSL 3 k)) :=
    Nat.finite_of_card_ne_zero (by rw [card_mulAut hk]; norm_num)
  have hL : (Nat.card (MulAut (projectiveSL 3 k))).factorization 3 = 3 := by
    rw [card_mulAut hk]
    exact CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
      (show 241920 = 3 ^ 3 * 8960 by norm_num) (by norm_num)
  exact ⟨Subgroup.closure {x, y},
    CFSG.RankThree.Asc83Table.ex27_card_sylow hx3 hy3 hzx hzy hz1 hL,
    fun g hg => CFSG.RankThree.Asc83Table.pow_three_eq_one_of_mem hx3 hzx hzy hy3 hg⟩

theorem pow_three_eq_one_of_pow_nine (hk : Nat.card k = 4) {α : MulAut (projectiveSL 3 k)}
    (hα : α ^ 9 = 1) : α ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (MulAut (projectiveSL 3 k)) :=
    Nat.finite_of_card_ne_zero (by rw [card_mulAut hk]; norm_num)
  obtain ⟨R, hR, hR3⟩ := exists_sylow_three_mulAut hk
  have hB : IsPGroup 3 (Subgroup.zpowers α) := by
    rintro ⟨g, hg⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨2, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    rw [show ((3 ^ 2 : ℕ) : ℤ) = ((9 : ℕ) : ℤ) by norm_num, zpow_natCast, hα, one_zpow]
  obtain ⟨g, hg⟩ := CFSG.RankThree.Asc83Table.exists_map_conj_le hR hB
  have hmem : (MulAut.conj g).toMonoidHom α ∈ R := hg ⟨α, Subgroup.mem_zpowers α, rfl⟩
  have h3 : ((MulAut.conj g).toMonoidHom α) ^ 3 = 1 := hR3 _ hmem
  have h4 : (MulAut.conj g) (α ^ 3) = 1 := by
    rw [map_pow]
    exact h3
  exact (MulAut.conj g).injective (h4.trans (map_one (MulAut.conj g)).symm)

end Sylow

theorem l34AutNoNineFact : L34AutNoNineFact := by
  intro X _ hX α hα
  obtain ⟨k, _, _, hk, ⟨e⟩⟩ := exists_mulEquiv_projectiveSL_of_lieModel hX
  have h9 : (MulAut.congr e α) ^ 9 = 1 := by rw [← map_pow, hα, map_one]
  have h3 := pow_three_eq_one_of_pow_nine hk h9
  rw [← map_pow] at h3
  exact (MulAut.congr e).injective (h3.trans (map_one _).symm)

theorem l34SylowNormFact : L34SylowNormFact := by
  intro X _ _ hX S hS φ hφS hcop
  obtain ⟨k, _, _, hk, ⟨e⟩⟩ := exists_mulEquiv_projectiveSL_of_lieModel hX
  have : CharP k 2 :=
    CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.char_two_of_card (n := 2)
      (by rw [hk]; norm_num)
  have hσ : ∀ a, frobeniusEquiv k 2 a = a ^ 2 := fun a => frobeniusEquiv_apply k 2 a
  obtain ⟨Ψ, hΨ⟩ := LinearThreeFourOuter.exists_outerHom hσ hk
  have hker := LinearThreeFourOuter.ker_eq_range_conj hσ hk hΨ
  have hcardT : Nat.card (kˣ ⋊[LinearThreeFourOuter.inversionAction kˣ]
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) = 12 := by
    rw [SemidirectProduct.card, LinearThreeFourOuter.card_units_eq_three hk, Nat.card_prod]
    simp
  set φ' := MulAut.congr e φ with hφ'
  have hord' : orderOf φ' = orderOf φ := orderOf_injective (MulAut.congr e).toMonoidHom
    (MulAut.congr e).injective φ
  have hΨ1 : Ψ φ' = 1 := by
    have h1 : orderOf (Ψ φ') ∣ orderOf φ' := orderOf_map_dvd Ψ φ'
    have h2 : orderOf (Ψ φ') ∣ 12 := by
      have : Finite (kˣ ⋊[LinearThreeFourOuter.inversionAction kˣ]
          (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) :=
        Nat.finite_of_card_ne_zero (by rw [hcardT]; norm_num)
      rw [← hcardT]
      exact orderOf_dvd_natCard _
    have hc12 : Nat.Coprime (orderOf φ') 12 := by
      rw [hord']
      have h12 : (12 : ℕ) = 6 * 2 := by norm_num
      rw [h12]
      exact Nat.Coprime.mul_right hcop (Nat.Coprime.coprime_dvd_right (by norm_num) hcop)
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hc12) h2
    exact orderOf_eq_one_iff.mp this
  have hmem : φ' ∈ Ψ.ker := hΨ1
  rw [hker] at hmem
  obtain ⟨x', hx'⟩ := hmem
  set x := e.symm x' with hxdef
  have hφx : φ = MulAut.conj x := by
    apply (MulAut.congr e).injective
    rw [← hφ', ← hx', CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, hxdef,
      e.apply_symm_apply]
  have hxN : x ∈ Subgroup.normalizer (S : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · intro hs
      have : φ s ∈ S.map φ.toMonoidHom := ⟨s, hs, rfl⟩
      rw [hφS, hφx, MulAut.conj_apply] at this
      exact this
    · intro hs
      have : x * s * x⁻¹ ∈ S.map φ.toMonoidHom := by rw [hφS]; exact hs
      obtain ⟨t, ht, hts⟩ := this
      have : t = s := by
        rw [hφx] at hts
        simpa using hts
      rwa [← this]
  have hle : Subgroup.zpowers x ≤ Subgroup.normalizer (S : Set X) :=
    Subgroup.zpowers_le.mpr hxN
  have hZ : Function.Injective (MulAut.conj : X →* MulAut X) := by
    have hc := conj_injective hk
    intro a b hab
    apply e.injective
    apply hc
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.congr_conj,
      ← CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, hab]
  have hordx : orderOf x = orderOf φ := by
    rw [hφx]
    exact (orderOf_injective MulAut.conj hZ x).symm
  have hodd : Odd (Nat.card (Subgroup.zpowers x)) := by
    rw [Nat.card_zpowers, hordx]
    exact Nat.coprime_two_right.mp (Nat.Coprime.coprime_dvd_right (by norm_num) hcop)
  have h3 := l34BorelFact X hX S _ hS hle hodd
  rw [Nat.card_zpowers, hordx] at h3
  have h1 : orderOf φ = 1 := Nat.Coprime.eq_one_of_dvd
    (Nat.Coprime.coprime_dvd_right (by norm_num) hcop) h3
  exact orderOf_eq_one_iff.mp h1

end CFSG.Quasithin.H13
