module

public import CFSG.RankThree.CentralLift.ClassicalScalarCover
public import CFSG.RankThree.CentralLift.ClassicalTailModels
public import CFSG.RankThree.CentralLift.CrossUnitary
public import CFSG.RankThree.CentralLift.CrossOrthogonalTail

public section

namespace CFSG.RankThree.CentralLift

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LieType.Universal.Spin
  CFSG.LocalAnalysis.ComponentInitial.NormTail
open CFSG.RankThree.CentralLiftU (forall_section_of_mulEquiv)

universe u

section Split

variable {p ℓ f : ℕ}

theorem statedSU_forall_section (hp : p.Prime) (hp3 : 3 < p) (hℓ : ℓ.Prime) (hℓodd : Odd ℓ)
    (hf : 1 ≤ f) {K : Type} [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) {n : ℕ} (hn : 3 ≤ n)
    (hcase : p ≠ ℓ ∨ Even n ∨ n = 3) {E : Type*} [Group E] [Finite E]
    (π : E →* StatedSU n (ℓ ^ f) K) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hCp : IsPGroup p π.ker) :
    ∃ s : StatedSU n (ℓ ^ f) K →* E, ∀ x, π (s x) = x := by
  by_cases hpℓ : p = ℓ
  · refine statedSU_forall_section_of_three_or_defining hp hp3 hℓ hℓodd hf hK hn ?_ π hπ hC hCp
    rcases hcase with h | h | h
    · exact absurd hpℓ h
    · exact Or.inr ⟨hpℓ, h⟩
    · exact Or.inl h
  have h : UnitaryFieldData ℓ f K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨e⟩ := nonempty_statedSU_mulEquiv_sesq h n
  refine forall_section_of_mulEquiv e (fun ρ hρ hρC hρp => ?_) π hπ hC hCp
  obtain ⟨⟨s, hs, -⟩, -⟩ := unitary_cross_splitting hp hp3 h hℓodd hpℓ
    (gramForm_isSymm h (by rw [Matrix.map_one _ (map_zero h.bar) (map_one h.bar),
      Matrix.transpose_one]))
    (gramForm_separatingLeft h (by rw [Matrix.det_one]; exact one_ne_zero))
    (by rw [Module.finrank_fin_fun]; exact hn) ρ hρ hρC hρp
  exact ⟨s, DFunLike.congr_fun hs⟩

theorem statedOmegaOdd_forall_section (hp : p.Prime) (hp3 : 3 < p) (hℓ : ℓ.Prime)
    (hℓodd : Odd ℓ) (hpℓ : p ≠ ℓ) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) {n : ℕ} (hn : 3 ≤ n) {E : Type*} [Group E] [Finite E]
    (π : E →* StatedOmega (StatedQuadOdd n K)) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hCp : IsPGroup p π.ker) :
    ∃ s : StatedOmega (StatedQuadOdd n K) →* E, ∀ x, π (s x) = x := by
  have hK2 : ringChar K ≠ 2 := CFSG.LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hℓ
    (hℓodd.ne_two_of_dvd_nat (dvd_refl ℓ)) hK
  obtain ⟨T, -, ⟨e⟩⟩ := nonempty_statedOmegaOdd_mulEquiv_normTail hK2 hn
  refine forall_section_of_mulEquiv e (fun ρ hρ hρC hρp => ?_) π hπ hC hCp
  obtain ⟨⟨s, hs, -⟩, -⟩ := tail_orthogonal_cross_splitting hp hp3 hℓ hℓodd hpℓ hf hK T
    (Or.inl (Module.finrank_self K)) hn ρ hρ hρC hρp
  exact ⟨s, DFunLike.congr_fun hs⟩

theorem statedOmegaMinus_forall_section (hp : p.Prime) (hp3 : 3 < p) (hℓ : ℓ.Prime)
    (hℓodd : Odd ℓ) (hpℓ : p ≠ ℓ) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) {n : ℕ} (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {E : Type*} [Group E] [Finite E]
    (π : E →* StatedOmega (StatedQuadMinus n K b c)) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hCp : IsPGroup p π.ker) :
    ∃ s : StatedOmega (StatedQuadMinus n K b c) →* E, ∀ x, π (s x) = x := by
  have hK2 : ringChar K ≠ 2 := CFSG.LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hℓ
    (hℓodd.ne_two_of_dvd_nat (dvd_refl ℓ)) hK
  obtain ⟨L, _, _, T, hL, -, ⟨e⟩⟩ := nonempty_statedOmegaMinus_mulEquiv_normTail hK2 hn hirr
  refine forall_section_of_mulEquiv e (fun ρ hρ hρC hρp => ?_) π hπ hC hCp
  obtain ⟨⟨s, hs, -⟩, -⟩ := tail_orthogonal_cross_splitting hp hp3 hℓ hℓodd hpℓ hf hK T
    (Or.inr hL) (by omega : 3 ≤ n - 1) ρ hρ hρC hρp
  exact ⟨s, DFunLike.congr_fun hs⟩

end Split

theorem exists_quadOdd_ne_zero {K : Type} [Field K] (n : ℕ) : ∃ v, quadOdd n K v ≠ 0 := by
  refine ⟨Pi.single (Sum.inr (Sum.inr ())) 1, ?_⟩
  rw [quadOdd_apply]
  simp

theorem exists_quadMinus_ne_zero {K : Type} [Field K] (n : ℕ) (b c : K) :
    ∃ v, quadMinus n K b c v ≠ 0 := by
  refine ⟨Pi.single (Sum.inr (Sum.inr 0)) 1, ?_⟩
  rw [quadMinus_apply]
  simp

section Cover

variable {p ℓ f : ℕ} {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]

theorem unitary_exact_scalar_cover (hp : p.Prime) (hp3 : 3 < p) (hℓ : ℓ.Prime) (hℓodd : Odd ℓ)
    (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) {n : ℕ}
    (hn : 3 ≤ n) (hcase : p ≠ ℓ ∨ Even n ∨ n = 3)
    (η : L →* StatedProj (StatedSU n (ℓ ^ f) K)) (hη : Function.Surjective η)
    (hC : η.ker ≤ Subgroup.center L) (hCp : IsPGroup p η.ker) :
    (∃ φ : StatedSU n (ℓ ^ f) K →* L, Function.Surjective φ ∧
      η.comp φ = QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (ℓ ^ f) K)) ∧
      φ.ker ≤ (StatedScalars (Fin n) K).subgroupOf (StatedSU n (ℓ ^ f) K) ∧
      ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (ℓ ^ f) K)).map φ = η.ker ∧
      (∃ e : StatedSU n (ℓ ^ f) K ⧸ φ.ker ≃* L, ∀ h : StatedSU n (ℓ ^ f) K,
        e (h : StatedSU n (ℓ ^ f) K ⧸ φ.ker) = φ h ∧
        η (e (h : StatedSU n (ℓ ^ f) K ⧸ φ.ker)) =
          QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (ℓ ^ f) K)) h) ∧
      Nonempty (η.ker ≃* (StatedScalars (Fin n) K).subgroupOf (StatedSU n (ℓ ^ f) K) ⧸
        φ.ker.subgroupOf ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (ℓ ^ f) K)))) ∧
    Nat.card ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (ℓ ^ f) K)) ∣
      Nat.gcd n (ℓ ^ f + 1) :=
  ⟨exact_scalar_cover_of_forall_section hη hC hCp fun _ _ _ π hπ hπC hπp =>
      statedSU_forall_section hp hp3 hℓ hℓodd hf hK hn hcase π hπ hπC hπp,
    dvd_of_eq (CFSG.LinearGroups.unitary_scalar_kernel hℓ hK (by omega)).2.2⟩

theorem omegaOdd_exact_scalar_cover (hp : p.Prime) (hp3 : 3 < p) (hℓ : ℓ.Prime)
    (hℓodd : Odd ℓ) (hpℓ : p ≠ ℓ) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) {n : ℕ} (hn : 3 ≤ n)
    (η : L →* StatedProj (StatedOmega (StatedQuadOdd n K))) (hη : Function.Surjective η)
    (hC : η.ker ≤ Subgroup.center L) (hCp : IsPGroup p η.ker) :
    (∃ φ : StatedOmega (StatedQuadOdd n K) →* L, Function.Surjective φ ∧
      η.comp φ = QuotientGroup.mk'
        ((StatedScalars (Fin n ⊕ Fin n ⊕ Unit) K).subgroupOf (StatedOmega (StatedQuadOdd n K))) ∧
      φ.ker ≤
        (StatedScalars (Fin n ⊕ Fin n ⊕ Unit) K).subgroupOf (StatedOmega (StatedQuadOdd n K)) ∧
      ((StatedScalars (Fin n ⊕ Fin n ⊕ Unit) K).subgroupOf
        (StatedOmega (StatedQuadOdd n K))).map φ = η.ker ∧
      (∃ e : StatedOmega (StatedQuadOdd n K) ⧸ φ.ker ≃* L, ∀ h : StatedOmega (StatedQuadOdd n K),
        e (h : StatedOmega (StatedQuadOdd n K) ⧸ φ.ker) = φ h ∧
        η (e (h : StatedOmega (StatedQuadOdd n K) ⧸ φ.ker)) = QuotientGroup.mk'
          ((StatedScalars (Fin n ⊕ Fin n ⊕ Unit) K).subgroupOf
            (StatedOmega (StatedQuadOdd n K))) h) ∧
      Nonempty (η.ker ≃* (StatedScalars (Fin n ⊕ Fin n ⊕ Unit) K).subgroupOf
          (StatedOmega (StatedQuadOdd n K)) ⧸
        φ.ker.subgroupOf ((StatedScalars (Fin n ⊕ Fin n ⊕ Unit) K).subgroupOf
          (StatedOmega (StatedQuadOdd n K))))) ∧
    Nat.card ((StatedScalars (Fin n ⊕ Fin n ⊕ Unit) K).subgroupOf
      (StatedOmega (StatedQuadOdd n K))) ≤ 2 :=
  ⟨exact_scalar_cover_of_forall_section hη hC hCp fun _ _ _ π hπ hπC hπp =>
      statedOmegaOdd_forall_section hp hp3 hℓ hℓodd hpℓ hf hK hn π hπ hπC hπp,
    card_statedScalars_subgroupOf_statedOmega_le_two (coe_quadOdd n K)
      (exists_quadOdd_ne_zero n)⟩

theorem omegaMinus_exact_scalar_cover (hp : p.Prime) (hp3 : 3 < p) (hℓ : ℓ.Prime)
    (hℓodd : Odd ℓ) (hpℓ : p ≠ ℓ) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) {n : ℕ} (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (η : L →* StatedProj (StatedOmega (StatedQuadMinus n K b c))) (hη : Function.Surjective η)
    (hC : η.ker ≤ Subgroup.center L) (hCp : IsPGroup p η.ker) :
    (∃ φ : StatedOmega (StatedQuadMinus n K b c) →* L, Function.Surjective φ ∧
      η.comp φ = QuotientGroup.mk' ((StatedScalars (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K).subgroupOf
        (StatedOmega (StatedQuadMinus n K b c))) ∧
      φ.ker ≤ (StatedScalars (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K).subgroupOf
        (StatedOmega (StatedQuadMinus n K b c)) ∧
      ((StatedScalars (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K).subgroupOf
        (StatedOmega (StatedQuadMinus n K b c))).map φ = η.ker ∧
      (∃ e : StatedOmega (StatedQuadMinus n K b c) ⧸ φ.ker ≃* L,
        ∀ h : StatedOmega (StatedQuadMinus n K b c),
          e (h : StatedOmega (StatedQuadMinus n K b c) ⧸ φ.ker) = φ h ∧
          η (e (h : StatedOmega (StatedQuadMinus n K b c) ⧸ φ.ker)) = QuotientGroup.mk'
            ((StatedScalars (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K).subgroupOf
              (StatedOmega (StatedQuadMinus n K b c))) h) ∧
      Nonempty (η.ker ≃* (StatedScalars (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K).subgroupOf
          (StatedOmega (StatedQuadMinus n K b c)) ⧸
        φ.ker.subgroupOf ((StatedScalars (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K).subgroupOf
          (StatedOmega (StatedQuadMinus n K b c))))) ∧
    Nat.card ((StatedScalars (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K).subgroupOf
      (StatedOmega (StatedQuadMinus n K b c))) ≤ 2 :=
  ⟨exact_scalar_cover_of_forall_section hη hC hCp fun _ _ _ π hπ hπC hπp =>
      statedOmegaMinus_forall_section hp hp3 hℓ hℓodd hpℓ hf hK hn hirr π hπ hπC hπp,
    card_statedScalars_subgroupOf_statedOmega_le_two (coe_quadMinus n K b c)
      (exists_quadMinus_ne_zero n b c)⟩

end Cover

end CFSG.RankThree.CentralLift
