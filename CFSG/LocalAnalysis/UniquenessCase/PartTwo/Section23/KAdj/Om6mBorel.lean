module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusCuts
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailUnipotentGroup
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelCoordinates
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.Hall
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.AGLEmbedding.LeviBlock (OrthCuts orthParab)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

private abbrev Om6mV (K : Type) : Type := (Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K)

instance finite_orthElementaryGroup_quadTail_minus {r : ℕ} :
    Finite ↥(orthElementaryGroup (quadTail r (minusTailForm K b c))) := by
  haveI : Finite (((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin r ⊕ Fin r → K) × (Fin 2 → K))) :=
    CFSG.AGLEmbedding.LeviBlock.finite_orthLinearEquiv
  infer_instance

theorem om6m_orthCuts_zero_two : OrthCuts 2 ![0, 2] where
  mono := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;> decide
  zero := rfl
  last := by decide

private theorem mem_tailQZero_iff_D07 {K : Type} [Field K] {b c : K}
    (x : ↥(orthElementaryGroup (quadTail 2 (minusTailForm K b c)))) :
    x ∈ orthParab 2 (minusTailForm K b c) ![0, 1] ↔
      (tailFlag K (Fin 2 → K) 2 1).map (x : Om6mV K →ₗ[K] Om6mV K) =
        tailFlag K (Fin 2 → K) 2 1 := by
  rw [CFSG.AGLEmbedding.LeviBlock.mem_orthParab]
  constructor
  · intro h
    simpa using h 1
  · intro h j
    fin_cases j
    · simp [tailFlag_zero]
    · simpa using h

private theorem mem_tailQAlpha_iff_D07 {K : Type} [Field K] {b c : K}
    (x : ↥(orthElementaryGroup (quadTail 2 (minusTailForm K b c)))) :
    x ∈ orthParab 2 (minusTailForm K b c) ![0, 2] ↔
      (tailFlag K (Fin 2 → K) 2 2).map (x : Om6mV K →ₗ[K] Om6mV K) =
        tailFlag K (Fin 2 → K) 2 2 := by
  rw [CFSG.AGLEmbedding.LeviBlock.mem_orthParab]
  constructor
  · intro h
    simpa using h 1
  · intro h j
    fin_cases j
    · simp [tailFlag_zero]
    · simpa using h

theorem om6m_orthParab_inf_eq_tailBorel :
    orthParab 2 (minusTailForm K b c) ![0, 1] ⊓ orthParab 2 (minusTailForm K b c) ![0, 2] =
      (tailBorel 2 (minusTailForm K b c)).subgroupOf
        (orthElementaryGroup (quadTail 2 (minusTailForm K b c))) := by
  ext x
  rw [Subgroup.mem_inf, mem_tailQZero_iff_D07, mem_tailQAlpha_iff_D07,
    Subgroup.mem_subgroupOf, mem_tailBorel]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by simpa using x.2, fun i hi1 hi2 => ?_⟩
    rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl
    · exact h1
    · exact h2
  · rintro ⟨-, h⟩
    exact ⟨h 1 le_rfl (by norm_num), h 2 (by norm_num) (by norm_num)⟩

private theorem pow_orderOf_eq_one_of_mul_mem_tailUnipotent_D07 {K : Type} [Field K]
    {A : Type} [AddCommGroup A] [Module K A] [FiniteDimensional K A] {r : ℕ}
    {qA : QuadraticForm K A} (hani : qA.Anisotropic)
    {τ υ : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)}
    (hτ : τ ∈ tailTorus r qA) (hυ : υ ∈ tailUnipotent r qA)
    {t : ↥(orthElementaryGroup (quadTail r qA))}
    (ht : (t : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) = τ * υ) :
    τ ^ orderOf t = 1 := by
  let Bo : Subgroup (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) :=
    tailBorel r qA
  let N : Subgroup Bo := (tailUnipotent r qA).subgroupOf Bo
  haveI hN : N.Normal := tailUnipotent_normal hani
  have htBo : (t : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) ∈ Bo := by
    rw [ht]
    exact mul_mem (tailTorus_le_tailBorel hτ) (tailUnipotent_le_tailBorel hani hυ)
  let tB : Bo := ⟨(t : _), htBo⟩
  let τB : Bo := ⟨τ, tailTorus_le_tailBorel hτ⟩
  let υB : Bo := ⟨υ, tailUnipotent_le_tailBorel hani hυ⟩
  have hυN : υB ∈ N := Subgroup.mem_subgroupOf.mpr hυ
  have htB_eq : tB = τB * υB := by
    apply Subtype.ext
    simpa [tB, τB, υB, Subgroup.coe_mul] using ht
  have hπ : QuotientGroup.mk' N τB = QuotientGroup.mk' N tB := by
    have h1 : QuotientGroup.mk' N υB = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hυN
    rw [htB_eq, map_mul, h1, mul_one]
  have htBord : orderOf tB = orderOf t := by
    calc orderOf tB = orderOf (tB : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K]
            ((Fin r ⊕ Fin r → K) × A)) := (Subgroup.orderOf_coe tB).symm
      _ = orderOf (t : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K]
            ((Fin r ⊕ Fin r → K) × A)) := rfl
      _ = orderOf t := Subgroup.orderOf_coe t
  have htBpow : tB ^ orderOf t = 1 := by
    rw [← htBord]
    exact pow_orderOf_eq_one tB
  have hpow : QuotientGroup.mk' N (τB ^ orderOf t) = 1 := by
    rw [map_pow, hπ, ← map_pow, htBpow, map_one]
  have hτN : τB ^ orderOf t ∈ N := by
    rw [← QuotientGroup.eq_one_iff (N := N) (τB ^ orderOf t)]
    simpa only [QuotientGroup.mk'_apply] using hpow
  have hτU : τ ^ orderOf t ∈ tailUnipotent r qA := by
    have := Subgroup.mem_subgroupOf.mp hτN
    simpa [τB] using this
  have hinf : τ ^ orderOf t ∈ tailTorus r qA ⊓ tailUnipotent r qA :=
    Subgroup.mem_inf.mpr ⟨pow_mem hτ _, hτU⟩
  rw [tailTorus_inf_tailUnipotent hani] at hinf
  simpa using hinf

theorem om6m_exists_conj_mem_tailTorus (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {t : ↥(orthElementaryGroup (quadTail 2 (minusTailForm K b c)))}
    (ht : t ∈ (tailBorel 2 (minusTailForm K b c)).subgroupOf
      (orthElementaryGroup (quadTail 2 (minusTailForm K b c))))
    (hodd : ¬ 2 ∣ orderOf t) :
    ∃ e ∈ (tailUnipotent 2 (minusTailForm K b c)).subgroupOf
        (orthElementaryGroup (quadTail 2 (minusTailForm K b c))),
      e * t * e⁻¹ ∈ (tailTorus 2 (minusTailForm K b c)).subgroupOf
        (orthElementaryGroup (quadTail 2 (minusTailForm K b c))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hani : (minusTailForm K b c).Anisotropic := anisotropic_minusTailForm hirr
  obtain ⟨τ, hτ, υ, hυ, hb⟩ := exists_tailTorus_mul_tailUnipotent (r := 2)
    (qA := minusTailForm K b c) hani (Subgroup.mem_subgroupOf.mp ht)
  let τ' : ↥(orthElementaryGroup (quadTail 2 (minusTailForm K b c))) :=
    ⟨τ, tailTorus_le hτ⟩
  let υ' : ↥(orthElementaryGroup (quadTail 2 (minusTailForm K b c))) :=
    ⟨υ, tailUnipotent_le hυ⟩
  have ht_eq : t = τ' * υ' := by
    apply Subtype.ext
    simpa [τ', υ', Subgroup.coe_mul] using hb
  have hdvdτ : orderOf τ ∣ orderOf t :=
    orderOf_dvd_iff_pow_eq_one.mpr
      (pow_orderOf_eq_one_of_mul_mem_tailUnipotent_D07 hani hτ hυ hb)
  have hdvd : orderOf τ' ∣ orderOf t := by
    simpa [τ'] using hdvdτ
  have hT : ¬ 2 ∣ Nat.card (Subgroup.zpowers τ') := by
    rw [Nat.card_zpowers]
    exact fun h => hodd (dvd_trans h hdvd)
  have hET : Subgroup.zpowers τ' ≤ Subgroup.normalizer
      (((tailUnipotent 2 (minusTailForm K b c)).subgroupOf
        (orthElementaryGroup (quadTail 2 (minusTailForm K b c)))) : Set _) := by
    rw [normalizer_tailUnipotent (r := 2) (qA := minusTailForm K b c) hani
      ⟨fun _ => 1, fun h => one_ne_zero (congrFun h 0)⟩]
    exact Subgroup.zpowers_le.mpr
      (Subgroup.mem_subgroupOf.mpr (tailTorus_le_tailBorel hτ))
  have hE : IsPGroup 2 ((tailUnipotent 2 (minusTailForm K b c)).subgroupOf
      (orthElementaryGroup (quadTail 2 (minusTailForm K b c)))) :=
    isPGroup_tailUnipotent (p := 2) (r := 2) (qA := minusTailForm K b c) hani
  have ht' : t ∈ (tailUnipotent 2 (minusTailForm K b c)).subgroupOf
      (orthElementaryGroup (quadTail 2 (minusTailForm K b c))) ⊔ Subgroup.zpowers τ' := by
    rw [ht_eq, sup_comm]
    exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers τ') (Subgroup.mem_subgroupOf.mpr hυ)
  obtain ⟨e, he, hconj⟩ := exists_conj_mem_of_mem_sup
    (G := ↥(orthElementaryGroup (quadTail 2 (minusTailForm K b c))))
    (p := 2) hET hE hT ht' hodd
  exact ⟨e, he, (Subgroup.zpowers_le.mpr (Subgroup.mem_subgroupOf.mpr hτ)) hconj⟩

theorem om6m_tailUnipotent_le_orthParab (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (tailUnipotent 2 (minusTailForm K b c)).subgroupOf
        (orthElementaryGroup (quadTail 2 (minusTailForm K b c))) ≤
      orthParab 2 (minusTailForm K b c) ![0, 1] ⊓ orthParab 2 (minusTailForm K b c) ![0, 2] := by
  rw [om6m_orthParab_inf_eq_tailBorel]
  exact fun x hx => Subgroup.mem_subgroupOf.mpr
    (tailUnipotent_le_tailBorel (anisotropic_minusTailForm hirr)
      (Subgroup.mem_subgroupOf.mp hx))

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
