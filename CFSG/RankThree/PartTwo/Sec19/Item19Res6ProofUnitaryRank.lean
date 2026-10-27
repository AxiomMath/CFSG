module

public import CFSG.RankThree.PartTwo.Sec19.Item19Res5ProofFaithRank
public import CFSG.RankThree.PartTwo.Sec14.Item148RankProofField

public section

namespace CFSG.RankThree.PartTwo.Sec19.Item19Res6Proof

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}

theorem mem_psuConj_range_of_isInnerAut {α : MulAut (unitaryPSU h 3)} (hα : IsInnerAut α) :
    α ∈ (psuConj h).range :=
  (stdPinnedPSU3 h).inn_le hα

theorem exists_scalar_of_psuConj_eq_one {A : unitaryIsom3 h} (hA : psuConj h A = 1) :
    ∃ c : Kˣ, (A : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) c := by
  obtain ⟨-, c, -, hc⟩ := eq_one_of_psuConj_mul_psuField_eq_one A 1 (by rw [map_one, mul_one, hA])
  exact ⟨c, hc⟩

theorem psuField_not_mem_psuConj_range {σ : K ≃+* K} (hσ : σ ≠ 1) :
    psuField h σ ∉ (psuConj h).range :=
  fun hmem => hσ (psuField_mem_range_psuConj_iff.1 hmem)

theorem not_isInnerAut_psuField {σ : K ≃+* K} (hσ : σ ≠ 1) : ¬ IsInnerAut (psuField h σ) :=
  fun hin => psuField_not_mem_psuConj_range hσ (mem_psuConj_range_of_isInnerAut hin)

theorem card_le_nine_of_le_psuConj_range [Finite K] (hK3 : 3 ∣ Nat.card K - 1)
    (B : Subgroup (MulAut (unitaryPSU h 3))) (hBD : B ≤ (psuConj h).range)
    (hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hB3 : ∀ x ∈ B, x ^ 3 = 1) :
    Nat.card B ≤ 9 := by
  classical
  set φ : unitaryIsom3 h →* MulAut (projectiveSL 3 K) :=
    (conjAut 3 K).comp (unitaryIsom3 h).subtype with hφ
  set Bt : Subgroup (unitaryIsom3 h) := B.comap (psuConj h) with hBt
  set B' : Subgroup (MulAut (projectiveSL 3 K)) := Bt.map φ with hB'
  have hker : ∀ A : unitaryIsom3 h, psuConj h A = 1 → φ A = 1 := by
    intro A hA
    obtain ⟨c, hc⟩ := exists_scalar_of_psuConj_eq_one hA
    rw [hφ, MonoidHom.comp_apply, Subgroup.coe_subtype, hc]
    exact conjAut_scalar c
  have hker' : ∀ A : unitaryIsom3 h, φ A = 1 → psuConj h A = 1 := by
    intro A hA
    obtain ⟨u, hu⟩ := (ProjectivePlane.conjAut_eq_one_iff le_rfl (A : GL (Fin 3) K)).1 hA
    have hmem : GeneralLinearGroup.scalar (Fin 3) u ∈ unitaryIsom3 h := hu ▸ A.2
    have hA' : A = ⟨_, hmem⟩ := Subtype.ext hu
    rw [hA']
    exact psuConj_scalar hmem
  have hB'D : B' ≤ linearAutGroup 3 K := by
    rintro _ ⟨A, -, rfl⟩
    exact conjAut_mem_linearAutGroup _
  have hB'ab : ∀ x ∈ B', ∀ y ∈ B', x * y = y * x := by
    rintro _ ⟨A, hA, rfl⟩ _ ⟨A', hA', rfl⟩
    have h1 : psuConj h (A * A' * A⁻¹ * A'⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hBab _ hA _ hA']
      group
    have h2 := hker _ h1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    calc φ A * φ A' = (φ A * φ A' * (φ A)⁻¹ * (φ A')⁻¹) * (φ A' * φ A) := by group
      _ = φ A' * φ A := by rw [h2, one_mul]
  have hB'3 : ∀ x ∈ B', x ^ 3 = 1 := by
    rintro _ ⟨A, hA, rfl⟩
    rw [← map_pow]
    exact hker _ (by rw [map_pow]; exact hB3 _ hA)
  have hle := Item19Res5Proof.card_le_nine_of_le_linearAutGroup hK3 B' hB'D hB'ab hB'3
  have hsurj : Function.Surjective (fun b' : B' =>
      (⟨psuConj h b'.2.choose, b'.2.choose_spec.1⟩ : B)) := by
    rintro ⟨β, hβ⟩
    obtain ⟨A, hA⟩ := hBD hβ
    have hAB : A ∈ Bt := by
      show psuConj h A ∈ B
      rw [hA]
      exact hβ
    refine ⟨⟨φ A, A, hAB, rfl⟩, Subtype.ext ?_⟩
    change psuConj h (⟨φ A, A, hAB, rfl⟩ : B').2.choose = β
    set A' := (⟨φ A, A, hAB, rfl⟩ : B').2.choose with hA'
    have hφA' : φ A' = φ A := (⟨φ A, A, hAB, rfl⟩ : B').2.choose_spec.2
    have h1 : psuConj h (A'⁻¹ * A) = 1 :=
      hker' _ (by rw [map_mul, map_inv, hφA', inv_mul_cancel])
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    rw [h1, hA]
  exact (Nat.card_le_card_of_surjective _ hsurj).trans hle

theorem not_mem_psuConj_range_of_E27 (hQ : p ^ f % 3 = 2) (hQ2 : 2 < p ^ f)
    (B : Subgroup (MulAut (unitaryPSU h 3))) (hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hB3 : ∀ x ∈ B, x ^ 3 = 1) (hB27 : Nat.card B = 27) {c : MulAut (unitaryPSU h 3)}
    (hcB : c ∈ B) (hc : ¬ IsInnerAut c) : c ∉ (psuConj h).range := by
  intro hcD
  have := h.finite
  have hBD : B ≤ (psuConj h).range := by
    intro β hβ
    obtain ⟨j, hj⟩ := Sec14.Item148Rank.exists_isInnerAut_mul_pow_unitary148 (h := h) hQ hQ2
      (hB3 c hcB) (hB3 β hβ) (hBab _ hcB _ hβ) hc
    have h1 : β * c ^ j ∈ (psuConj h).range := mem_psuConj_range_of_isInnerAut hj
    have h2 : β = β * c ^ j * (c ^ j)⁻¹ := by group
    rw [h2]
    exact mul_mem h1 (inv_mem (pow_mem hcD j))
  have hK3 : 3 ∣ Nat.card K - 1 := by
    rw [h.card]
    have hpow : p ^ (2 * f) = (p ^ f) ^ 2 := by rw [pow_mul']
    rw [hpow]
    have h1 : (p ^ f) ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hQ]
    have h2 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have hle := card_le_nine_of_le_psuConj_range hK3 B hBD hBab hB3
  omega

end CFSG.RankThree.PartTwo.Sec19.Item19Res6Proof
