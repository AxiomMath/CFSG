module

public import CFSG.RankThree.PartOne.KFR4.Defs
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusSixUnitary
public import CFSG.ClassicalInvolution.Phan.Standard

public section

namespace CFSG.RankThree.PartOne.KFR4

open CFSG.RankThree.PartOne.KCOrthogonal CFSG.LieType.Universal.Unitary Matrix
open scoped commutatorElement

namespace UGen

section Generation

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E]

open CFSG.LieType.Steinberg in
theorem embPair_mulVec_single (c : Fin 3) (B : Matrix (Fin 2) (Fin 2) E) :
    embPair c B *ᵥ Pi.single c 1 = Pi.single c 1 := by
  fin_cases c <;> funext i <;> fin_cases i <;> simp [embPair]

open CFSG.ClassicalInvolution.Phan CFSG.LieType.Steinberg CFSG.LieType.BorelTits in
theorem SUid_le_sup (D : EvenNormPlane K E) (hq : Nat.card K ≠ 2) :
    SUid D.σ.toRingEquiv 3 ≤ suSupp D 0 1 ⊔ suSupp D 1 2 := by
  obtain ⟨f, -, hK, -⟩ := D.exists_unitaryFieldData
  have : CharP E 2 := charP_two_of_algebra (K := K)
  have : Finite E := D.finite_E
  have hE : Nat.card E = (2 ^ f) ^ 2 := by rw [D.card_E, hK]
  have hσ : D.σ.toRingEquiv = unitaryInvolution E 2 f :=
    RingEquiv.ext fun z => by
      rw [unitaryInvolution_apply, ← hK]
      exact D.sigma_eq_pow z
  have hq' : 2 ^ f ≠ 2 := by rwa [← hK]
  intro N hN
  rw [hσ] at hN
  have hmem : (⟨N, hN⟩ : Su E 2 f 3) ∈ B12 E 2 f ⊔ B23 E 2 f := by
    rw [B12_sup_B23 hE hq']
    exact Subgroup.mem_top _
  have h1 : (B12 E 2 f).map (SUid (unitaryInvolution E 2 f) 3).subtype ≤ suSupp D 0 1 := by
    rintro _ ⟨_, ⟨B, rfl⟩, rfl⟩
    refine ⟨?_, fun k hk0 hk1 => ?_⟩
    · rw [hσ]
      exact (embSUid (unitaryInvolution E 2 f) 2 B).2
    · fin_cases k
      · exact absurd rfl hk0
      · exact absurd rfl hk1
      · exact embPair_mulVec_single 2 _
  have h2 : (B23 E 2 f).map (SUid (unitaryInvolution E 2 f) 3).subtype ≤ suSupp D 1 2 := by
    rintro _ ⟨_, ⟨B, rfl⟩, rfl⟩
    refine ⟨?_, fun k hk1 hk2 => ?_⟩
    · rw [hσ]
      exact (embSUid (unitaryInvolution E 2 f) 0 B).2
    · fin_cases k
      · exact embPair_mulVec_single 0 _
      · exact absurd rfl hk1
      · exact absurd rfl hk2
  have h3 := Subgroup.mem_map_of_mem (SUid (unitaryInvolution E 2 f) 3).subtype hmem
  rw [Subgroup.map_sup] at h3
  exact sup_le_sup h1 h2 h3

end Generation

section Commutator

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E]

theorem commutator_mem_SUid {D : EvenNormPlane K E} {M₁ M₂ : GL (Fin 3) E} (h₁ : M₁ ∈ Uni D)
    (h₂ : M₂ ∈ Uni D) : ⁅M₁, M₂⁆ ∈ SUid D.σ.toRingEquiv 3 := by
  have hd : ∀ M : GL (Fin 3) E, (M : Matrix (Fin 3) (Fin 3) E).det *
      ((M⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E).det = 1 := fun M => by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  refine ⟨?_, ?_⟩
  · rw [commutatorElement_def]
    simp only [Units.val_mul, Matrix.det_mul]
    linear_combination ((M₂ : Matrix (Fin 3) (Fin 3) E).det *
      ((M₂⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E).det) * hd M₁ + hd M₂
  · have h : ⁅M₁, M₂⁆ ∈ Uni D := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
    exact h

theorem commutator_mulVec_eq {n : ℕ} {M₁ M₂ : GL (Fin n) E} {v : Fin n → E} (hv : v ≠ 0)
    {c₁ c₂ : E} (h₁ : (M₁ : Matrix (Fin n) (Fin n) E) *ᵥ v = c₁ • v)
    (h₂ : (M₂ : Matrix (Fin n) (Fin n) E) *ᵥ v = c₂ • v) :
    ((⁅M₁, M₂⁆ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ v = v := by
  have hinv : ∀ (M : GL (Fin n) E) (c : E), (M : Matrix (Fin n) (Fin n) E) *ᵥ v = c • v →
      c ≠ 0 ∧ ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ v = c⁻¹ • v := by
    intro M c h
    have key : ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ (c • v) = v := by
      rw [← h, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    have hc : c ≠ 0 := by
      rintro rfl
      rw [zero_smul, Matrix.mulVec_zero] at key
      exact hv key.symm
    refine ⟨hc, ?_⟩
    rw [Matrix.mulVec_smul] at key
    calc ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ v
        = c⁻¹ • (c • ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ v) := by
          rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      _ = c⁻¹ • v := by rw [key]
  obtain ⟨hc₁, hi₁⟩ := hinv M₁ c₁ h₁
  obtain ⟨hc₂, hi₂⟩ := hinv M₂ c₂ h₂
  rw [commutatorElement_def]
  simp only [Units.val_mul, ← Matrix.mulVec_mulVec, hi₂, Matrix.mulVec_smul, hi₁, h₂, h₁,
    smul_smul]
  convert one_smul E v using 2
  field_simp

end Commutator

section Classes

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E] {p : ℕ}

theorem mulVec_single_eq {D : EvenNormPlane K E} {A : AddSubgroup (Fin 3 → ZMod p)}
    {M : GL (Fin 3) E} (hM : UniBdP D A M) {k : Fin 3}
    (hk : ∀ j, j ≠ k → ∃ a ∈ A, a k ≠ a j) :
    (M : Matrix (Fin 3) (Fin 3) E) *ᵥ Pi.single k 1 =
      (M : Matrix (Fin 3) (Fin 3) E) k k • Pi.single k 1 := by
  funext j
  rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hj : j = k
  · subst hj
    simp
  · rw [hM.2.2 k j (hk j hj), Pi.single_eq_of_ne hj, mul_zero]

theorem exists_ne_of_not {A : AddSubgroup (Fin 3 → ZMod p)} {i j : Fin 3}
    (h : ¬ ∀ a ∈ A, a i = a j) : ∃ a ∈ A, a j ≠ a i := by
  by_contra hc
  exact h fun a ha => by_contra fun hne => hc ⟨a, ha, Ne.symm hne⟩

theorem dot_m12 (a : Fin 3 → ZMod p) : Root.m12.vecp p ⬝ᵥ a = a 0 - a 1 := by
  simp [Root.vecp, Root.vec, dotProduct, Fin.sum_univ_three]
  ring

theorem dot_m13 (a : Fin 3 → ZMod p) : Root.m13.vecp p ⬝ᵥ a = a 0 - a 2 := by
  simp [Root.vecp, Root.vec, dotProduct, Fin.sum_univ_three]
  ring

theorem dot_m23 (a : Fin 3 → ZMod p) : Root.m23.vecp p ⬝ᵥ a = a 1 - a 2 := by
  simp [Root.vecp, Root.vec, dotProduct, Fin.sum_univ_three]
  ring

end Classes

end UGen

theorem unitary_commutator_mem {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E]
    [Algebra K E] [Module.Finite K E] {p : ℕ} (S : StdData K E p)
    (A : AddSubgroup (Fin 3 → ZMod p)) (M₁ M₂ : GL (Fin 3) E)
    (h₁ : UniBdP S.D A M₁) (h₂ : UniBdP S.D A M₂) :
    matToG K ⁅M₁, M₂⁆ ∈ ⨆ ρ : {ρ : Root // vanishes A ρ}, Block S.D ρ.1 := by
  set H := ⨆ ρ : {ρ : Root // vanishes A ρ}, Block S.D ρ.1
  have hSU := UGen.commutator_mem_SUid h₁.1 h₂.1
  have hblk : ∀ (ρ : Root) (i j : Fin 3), vanishes A ρ → Block S.D ρ = longBlock S.D i j →
      ∀ M ∈ suSupp S.D i j, matToG K M ∈ H := by
    intro ρ i j hρ hB M hM
    exact Subgroup.mem_iSup_of_mem (⟨ρ, hρ⟩ : {ρ : Root // vanishes A ρ})
      (by rw [hB]; exact ⟨M, hM, rfl⟩)
  have v12 : (∀ a ∈ A, a 0 = a 1) → vanishes A .m12 := fun h a ha => by
    rw [UGen.dot_m12, h a ha, sub_self]
  have v13 : (∀ a ∈ A, a 0 = a 2) → vanishes A .m13 := fun h a ha => by
    rw [UGen.dot_m13, h a ha, sub_self]
  have v23 : (∀ a ∈ A, a 1 = a 2) → vanishes A .m23 := fun h a ha => by
    rw [UGen.dot_m23, h a ha, sub_self]
  have hfix : ∀ k : Fin 3, (∀ j, j ≠ k → ∃ a ∈ A, a k ≠ a j) →
      ((⁅M₁, M₂⁆ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *ᵥ Pi.single k 1 =
        Pi.single k 1 := fun k hk =>
    UGen.commutator_mulVec_eq (fun h => by simpa using congrFun h k)
      (UGen.mulVec_single_eq h₁ hk) (UGen.mulVec_single_eq h₂ hk)
  have hq : Nat.card K ≠ 2 := by
    intro h
    have h3 := S.hpq
    rw [h] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    have := S.hp5
    omega
  by_cases r01 : ∀ a ∈ A, a 0 = a 1 <;> by_cases r12 : ∀ a ∈ A, a 1 = a 2 <;>
    by_cases r02 : ∀ a ∈ A, a 0 = a 2
  ·
    have hle : suSupp S.D 0 1 ⊔ suSupp S.D 1 2 ≤ H.comap (matToG K) :=
      sup_le (fun M hM => hblk .m12 0 1 (v12 r01) rfl M hM)
        (fun M hM => hblk .m23 1 2 (v23 r12) rfl M hM)
    exact hle (UGen.SUid_le_sup S.D hq hSU)
  · exact absurd (fun a ha => (r01 a ha).trans (r12 a ha)) r02
  · exact absurd (fun a ha => (r01 a ha).symm.trans (r02 a ha)) r12
  ·
    have hk : ∀ j, j ≠ (2 : Fin 3) → ∃ a ∈ A, a 2 ≠ a j := by
      intro j hj
      fin_cases j
      · exact UGen.exists_ne_of_not r02
      · exact UGen.exists_ne_of_not r12
      · exact absurd rfl hj
    refine hblk .m12 0 1 (v12 r01) rfl _ ⟨hSU, fun k hk0 hk1 => ?_⟩
    fin_cases k
    · exact absurd rfl hk0
    · exact absurd rfl hk1
    · exact hfix 2 hk
  · exact absurd (fun a ha => (r02 a ha).trans (r12 a ha).symm) r01
  ·
    have hk : ∀ j, j ≠ (0 : Fin 3) → ∃ a ∈ A, a 0 ≠ a j := by
      intro j hj
      fin_cases j
      · exact absurd rfl hj
      · obtain ⟨a, ha, hne⟩ := UGen.exists_ne_of_not r01
        exact ⟨a, ha, Ne.symm hne⟩
      · obtain ⟨a, ha, hne⟩ := UGen.exists_ne_of_not r02
        exact ⟨a, ha, Ne.symm hne⟩
    refine hblk .m23 1 2 (v23 r12) rfl _ ⟨hSU, fun k hk1 hk2 => ?_⟩
    fin_cases k
    · exact hfix 0 hk
    · exact absurd rfl hk1
    · exact absurd rfl hk2
  ·
    have hk : ∀ j, j ≠ (1 : Fin 3) → ∃ a ∈ A, a 1 ≠ a j := by
      intro j hj
      fin_cases j
      · exact UGen.exists_ne_of_not r01
      · exact absurd rfl hj
      · obtain ⟨a, ha, hne⟩ := UGen.exists_ne_of_not r12
        exact ⟨a, ha, Ne.symm hne⟩
    refine hblk .m13 0 2 (v13 r02) rfl _ ⟨hSU, fun k hk0 hk2 => ?_⟩
    fin_cases k
    · exact absurd rfl hk0
    · exact hfix 1 hk
    · exact absurd rfl hk2
  ·
    have hk : ∀ k j : Fin 3, j ≠ k → ∃ a ∈ A, a k ≠ a j := by
      intro k j hj
      fin_cases k <;> fin_cases j
      all_goals first
        | exact absurd rfl hj
        | exact UGen.exists_ne_of_not r01
        | exact UGen.exists_ne_of_not r02
        | exact UGen.exists_ne_of_not r12
        | (obtain ⟨a, ha, hne⟩ := UGen.exists_ne_of_not r01; exact ⟨a, ha, Ne.symm hne⟩)
        | (obtain ⟨a, ha, hne⟩ := UGen.exists_ne_of_not r02; exact ⟨a, ha, Ne.symm hne⟩)
        | (obtain ⟨a, ha, hne⟩ := UGen.exists_ne_of_not r12; exact ⟨a, ha, Ne.symm hne⟩)
    have h1 : (⁅M₁, M₂⁆ : GL (Fin 3) E) = 1 :=
      Units.ext (Matrix.ext_of_mulVec_single fun k => by
        rw [hfix k (hk k), Units.val_one, Matrix.one_mulVec])
    rw [h1, map_one]
    exact one_mem H

end CFSG.RankThree.PartOne.KFR4
