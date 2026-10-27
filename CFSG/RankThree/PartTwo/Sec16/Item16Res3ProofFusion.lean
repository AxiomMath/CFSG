module

public import CFSG.RankThree.PartTwo.Sec16.Item16Res3ProofModel
public import CFSG.RankThree.PartTwo.Sec16.Item163ResProofU35
public import CFSG.Sporadic.McL.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec16.Res3U35

open CFSG.RankThree.PartOne.HNB CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.KFacts CFSG.Quasithin.H13 Matrix
open CFSG.Assembly.RankThreeEven (projSU)

@[expose] def uMat : Fin 3 → Fin 3 → Matrix (Fin 3) (Fin 3) F25 := ![![
  !![fe 1 0, fe 0 0, fe 0 0; fe 0 0, fe 1 0, fe 0 0; fe 0 0, fe 0 0, fe 1 0],
  !![fe 2 4, fe 3 4, fe 0 2; fe 3 4, fe 3 4, fe 3 4; fe 0 2, fe 3 4, fe 2 4],
  !![fe 0 3, fe 0 3, fe 0 3; fe 3 1, fe 2 1, fe 0 3; fe 2 1, fe 3 1, fe 0 3]], ![
  !![fe 1 0, fe 0 0, fe 0 0; fe 0 0, fe 1 0, fe 0 0; fe 0 0, fe 0 0, fe 1 0],
  !![fe 2 4, fe 2 4, fe 0 2; fe 3 4, fe 2 4, fe 3 4; fe 2 4, fe 3 4, fe 3 4],
  !![fe 3 1, fe 3 1, fe 2 1; fe 3 1, fe 2 1, fe 3 1; fe 0 3, fe 2 1, fe 2 1]], ![
  !![fe 4 0, fe 0 0, fe 0 0; fe 0 0, fe 0 0, fe 4 0; fe 0 0, fe 4 0, fe 0 0],
  !![fe 3 4, fe 3 4, fe 0 2; fe 3 4, fe 2 4, fe 2 4; fe 2 4, fe 3 4, fe 2 4],
  !![fe 3 1, fe 2 1, fe 2 1; fe 2 1, fe 3 1, fe 2 1; fe 3 1, fe 3 1, fe 0 3]]]

@[expose] def c1 : Fin 3 → Fin 3 → F25 :=
  ![![fe 1 0, fe 2 3, fe 2 2], ![fe 1 0, fe 1 0, fe 1 0], ![fe 1 0, fe 2 3, fe 2 2]]

@[expose] def c2 : Fin 3 → Fin 3 → F25 :=
  ![![fe 1 0, fe 2 3, fe 1 0], ![fe 1 0, fe 2 2, fe 1 0], ![fe 1 0, fe 2 3, fe 2 3]]

@[expose] def i2 : Fin 3 → Fin 3 → Fin 3 := ![![0, 2, 1], ![0, 1, 2], ![0, 1, 2]]

@[expose] def j2 : Fin 3 → Fin 3 → Fin 3 := ![![1, 0, 0], ![1, 2, 2], ![2, 1, 1]]

theorem uMat_facts : ∀ a b : Fin 3, (a, b) ≠ (0, 0) →
    det3 (uMat a b) = 1 ∧ ((uMat a b).map (· ^ (5 ^ 1)))ᵀ * uMat a b = 1 ∧
      uMat a b * U35A6.dMat om =
        c1 a b • (U35A6.dMat om ^ (a : ℕ) * U35A6.cMat ^ (b : ℕ) * uMat a b) ∧
      uMat a b * U35A6.cMat =
        c2 a b • (U35A6.dMat om ^ (i2 a b : ℕ) * U35A6.cMat ^ (j2 a b : ℕ) * uMat a b) := by
  decide +kernel

@[expose] noncomputable def uSU (a b : Fin 3) (hab : (a, b) ≠ (0, 0)) : SU5 :=
  mkSU (uMat a b) (by rw [det_eq_det3]; exact (uMat_facts a b hab).1) (uMat_facts a b hab).2.1

noncomputable abbrev uPU (a b : Fin 3) (hab : (a, b) ≠ (0, 0)) : PU5 := (uSU a b hab : PU5)

theorem uPU_mul_x1 (a b : Fin 3) (hab : (a, b) ≠ (0, 0)) :
    uPU a b hab * x1 = x1 ^ (a : ℕ) * x2 ^ (b : ℕ) * uPU a b hab := by
  have h := mk_eq_mk_of_smul (g := uSU a b hab * g1)
    (k := g1 ^ (a : ℕ) * g2 ^ (b : ℕ) * uSU a b hab) (c := c1 a b) (by
      rw [coe_mul, coe_mul, coe_mul, coe_pow, coe_pow, uSU, coe_mkSU, coe_g1, coe_g2]
      exact (uMat_facts a b hab).2.2.1)
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_pow,
    QuotientGroup.mk_pow] at h
  exact h

theorem uPU_mul_x2 (a b : Fin 3) (hab : (a, b) ≠ (0, 0)) :
    uPU a b hab * x2 = x1 ^ (i2 a b : ℕ) * x2 ^ (j2 a b : ℕ) * uPU a b hab := by
  have h := mk_eq_mk_of_smul (g := uSU a b hab * g2)
    (k := g1 ^ (i2 a b : ℕ) * g2 ^ (j2 a b : ℕ) * uSU a b hab) (c := c2 a b) (by
      rw [coe_mul, coe_mul, coe_mul, coe_pow, coe_pow, uSU, coe_mkSU, coe_g1, coe_g2]
      exact (uMat_facts a b hab).2.2.2)
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_pow,
    QuotientGroup.mk_pow] at h
  exact h

theorem mem_normalizer_E0 {u : PU5} (h1 : u * x1 * u⁻¹ ∈ E0) (h2 : u * x2 * u⁻¹ ∈ E0) :
    u ∈ Subgroup.normalizer (E0 : Set PU5) := by
  refine Subgroup.mem_normalizer_fintype fun e he => ?_
  obtain ⟨i, j, rfl⟩ := exists_eq_of_mem_E0 he
  have e1 : u * (x1 ^ (i : ℕ) * x2 ^ (j : ℕ)) * u⁻¹ =
      (u * x1 * u⁻¹) ^ (i : ℕ) * (u * x2 * u⁻¹) ^ (j : ℕ) := by
    rw [conj_pow, conj_pow]
    group
  rw [e1]
  exact E0.mul_mem (E0.pow_mem h1 _) (E0.pow_mem h2 _)

theorem exists_conj_x1 {y : PU5} (hy : y ∈ E0) (hy1 : y ≠ 1) :
    ∃ u ∈ Subgroup.normalizer (E0 : Set PU5), u * x1 * u⁻¹ = y := by
  obtain ⟨a, b, rfl⟩ := exists_eq_of_mem_E0 hy
  have hab : (a, b) ≠ (0, 0) := by
    rintro h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact hy1 (by simp)
  have e1 : uPU a b hab * x1 * (uPU a b hab)⁻¹ = x1 ^ (a : ℕ) * x2 ^ (b : ℕ) := by
    rw [uPU_mul_x1, mul_inv_cancel_right]
  have e2 : uPU a b hab * x2 * (uPU a b hab)⁻¹ = x1 ^ (i2 a b : ℕ) * x2 ^ (j2 a b : ℕ) := by
    rw [uPU_mul_x2, mul_inv_cancel_right]
  refine ⟨uPU a b hab, mem_normalizer_E0 ?_ ?_, e1⟩
  · rw [e1]
    exact mem_E0 _ _
  · rw [e2]
    exact mem_E0 _ _

theorem exists_conj_E0 {x y : PU5} (hx : x ∈ E0) (hy : y ∈ E0) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    ∃ u ∈ Subgroup.normalizer (E0 : Set PU5), u * x * u⁻¹ = y := by
  obtain ⟨u₁, hu₁, h₁⟩ := exists_conj_x1 hx hx1
  obtain ⟨u₂, hu₂, h₂⟩ := exists_conj_x1 hy hy1
  refine ⟨u₂ * u₁⁻¹, Subgroup.mul_mem _ hu₂ (Subgroup.inv_mem _ hu₁), ?_⟩
  rw [← h₁, ← h₂]
  group

theorem exists_conj_of_card_nine {E : Subgroup PU5} (hE : Nat.card E = 9) {x y : PU5} (hx : x ∈ E)
    (hy : y ∈ E) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    ∃ u ∈ Subgroup.normalizer (E : Set PU5), u * x * u⁻¹ = y := by
  obtain ⟨g, hg⟩ := exists_conj_eq_E0 hE
  have hx' : g * x * g⁻¹ ≠ 1 := fun h => hx1 (by
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group)
  have hy' : g * y * g⁻¹ ≠ 1 := fun h => hy1 (by
    calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group)
  obtain ⟨v, hv, hvxy⟩ := exists_conj_E0 ((hg x).mp hx) ((hg y).mp hy) hx' hy'
  refine ⟨g⁻¹ * v * g, Subgroup.mem_normalizer_fintype fun z hz => ?_, ?_⟩
  · rw [SetLike.mem_coe, hg]
    have h1 : g * z * g⁻¹ ∈ E0 := (hg z).mp hz
    have h2 : v * (g * z * g⁻¹) * v⁻¹ ∈ E0 :=
      (Subgroup.mem_normalizer_iff.mp hv _).mp h1
    convert h2 using 1
    group
  · calc g⁻¹ * v * g * x * (g⁻¹ * v * g)⁻¹ = g⁻¹ * (v * (g * x * g⁻¹) * v⁻¹) * g := by group
      _ = g⁻¹ * (g * y * g⁻¹) * g := by rw [hvxy]
      _ = y := by group

theorem ks163U35Fusion : KS163U35Fusion := by
  intro _ E hE x hx y hy hx1 hy1
  have : Finite ↥(projSU 3 5 1) := Finite.of_equiv _ equivPU.symm.toEquiv
  set φ := equivPU with hφ
  set E' := E.map φ.toMonoidHom with hE'
  have hE'9 : Nat.card E' = 9 := by
    rw [hE', Subgroup.card_map_of_injective φ.injective, hE]
  have hne : ∀ {z : ↥(projSU 3 5 1)}, z ≠ 1 → φ z ≠ 1 := fun hz h1 =>
    hz (φ.injective (h1.trans (map_one φ).symm))
  obtain ⟨u, hu, hux⟩ := exists_conj_of_card_nine hE'9 ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ (hne hx1)
    (hne hy1)
  refine ⟨φ.symm u, Subgroup.mem_normalizer_fintype fun z hz => ?_, ?_⟩
  · have h1 : φ z ∈ E' := ⟨z, hz, rfl⟩
    have h2 := (Subgroup.mem_normalizer_iff.mp hu _).mp h1
    obtain ⟨w, hw, hwz⟩ := h2
    have : w = φ.symm u * z * (φ.symm u)⁻¹ := by
      apply φ.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact hwz
    rw [← this]
    exact hw
  · apply φ.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hux

end CFSG.RankThree.PartTwo.Sec16.Res3U35
