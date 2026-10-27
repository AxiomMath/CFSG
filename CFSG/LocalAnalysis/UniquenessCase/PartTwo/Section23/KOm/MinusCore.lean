module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.MinusPlane
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.RootGroupFix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KOm

open CFSG.Open Matrix
open CFSG.LieType.Universal.Spin
open CFSG.ClassicalGroups.Orthogonal (rootGroupGL)

local notation "ιM" => Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2

variable {K : Type} [Field K]

theorem card_mul_card_fix_le_two_mul [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {E : Subgroup (GL ιM K)}
    (hE : E ≤ isoFix (StatedQuadMinus 2 K b c) (KTabC.e1M K)) (hE2 : IsPGroup 2 ↥E)
    (hE1 : E ≠ ⊥) :
    Nat.card ↥E * Nat.card {v : ιM → K // ∀ g ∈ E, (g : Matrix ιM ιM K) *ᵥ v = v} ≤
      2 * Nat.card K ^ 3 := by
  classical
  have hcardι : Fintype.card ιM = 4 := by simp
  have hQ : (QuadraticMap.polarBilin (quadMinus 2 K b c)).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite 2 K hirr
  have hu : quadMinus 2 K b c (KTabC.e1M K) = 0 := by
    rw [quadMinus_apply]
    simp [KTabC.e1M]
  have hu0 : KTabC.e1M K ≠ 0 := by
    simp [KTabC.e1M]
  set F : Subgroup (GL ιM K) := E ⊓ rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K) with hFdef
  have hFE : F ≤ E := by rw [hFdef]; exact inf_le_left
  have hcardE : Nat.card ↥E ≤ 2 * Nat.card ↥F := by
    rw [hFdef]
    exact card_le_two_mul_card_inf_rootGroupGL hirr hE hE2
  have hmono : Nat.card {v : ιM → K // ∀ g ∈ E, (g : Matrix ιM ιM K) *ᵥ v = v} ≤
      Nat.card {v : ιM → K // ∀ g ∈ F, (g : Matrix ιM ιM K) *ᵥ v = v} := by
    refine Nat.card_le_card_of_injective
      (fun v => (⟨v.1, fun g hg => v.2 g (hFE hg)⟩ :
        {v : ιM → K // ∀ g ∈ F, (g : Matrix ιM ιM K) *ᵥ v = v})) ?_
    intro x y hxy
    exact Subtype.ext (congrArg (fun z : {v : ιM → K // ∀ g ∈ F, (g : Matrix ιM ιM K) *ᵥ v = v}
      => (z : ιM → K)) hxy)
  by_cases hF : F = ⊥
  ·
    have hcardE2 : Nat.card ↥E ≤ 2 := by
      have h := hcardE
      rw [hF, Subgroup.card_bot] at h
      simpa using h
    have hex : ∃ g : GL ιM K, g ∈ E ∧ g ≠ 1 := by
      by_contra h
      apply hE1
      apply le_antisymm _ bot_le
      intro x hx
      rw [Subgroup.mem_bot]
      by_contra hx1
      exact h ⟨x, hx, hx1⟩
    obtain ⟨g, hgE, hg1⟩ := hex
    have hCE : Nat.card {v : ιM → K // ∀ g ∈ E, (g : Matrix ιM ιM K) *ᵥ v = v} ≤
        Nat.card K ^ 3 := by
      let f : (ιM → K) →ₗ[K] (ιM → K) := Matrix.mulVecLin ((g : Matrix ιM ιM K) - 1)
      have hne : LinearMap.ker f ≠ ⊤ := by
        intro htop
        apply hg1
        apply Units.ext
        have h0 : ∀ v : ιM → K, ((g : Matrix ιM ιM K) - 1).mulVec v = 0 := fun v => by
          have hv : v ∈ LinearMap.ker f := htop ▸ Submodule.mem_top
          exact LinearMap.mem_ker.mp hv
        have h1 : (g : Matrix ιM ιM K) - 1 = 0 :=
          Matrix.ext_of_mulVec_single (fun i => by rw [h0, Matrix.zero_mulVec])
        exact sub_eq_zero.mp h1
      have hlt : Module.finrank K (LinearMap.ker f) < 4 := by
        have h := Submodule.finrank_lt hne
        rwa [Module.finrank_fintype_fun_eq_card, hcardι] at h
      have hker : Nat.card (LinearMap.ker f) ≤ Nat.card K ^ 3 := by
        rw [Module.natCard_eq_pow_finrank (K := K)]
        exact Nat.pow_le_pow_right Nat.card_pos (by omega)
      have hmem : ∀ v : {v : ιM → K // ∀ g ∈ E, (g : Matrix ιM ιM K) *ᵥ v = v},
          v.1 ∈ LinearMap.ker f := by
        intro v
        rw [LinearMap.mem_ker]
        show ((g : Matrix ιM ιM K) - 1).mulVec v.1 = 0
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
        exact v.2 g hgE
      refine le_trans (Nat.card_le_card_of_injective
        (fun v => (⟨v.1, hmem v⟩ : LinearMap.ker f)) ?_) hker
      intro x y hxy
      exact Subtype.ext (congrArg (fun z : ↥(LinearMap.ker f) => (z : ιM → K)) hxy)
    exact Nat.mul_le_mul hcardE2 hCE
  ·
    have hFixF := card_mul_card_fix_le_of_le_rootGroupGL (ι := ιM) hQ hu hu0 (F := F)
      (by rw [hFdef]; exact inf_le_right) hF
    have hFixF' : Nat.card ↥F *
        Nat.card {v : ιM → K // ∀ g ∈ F, (g : Matrix ιM ιM K) *ᵥ v = v} ≤
          Nat.card K ^ 3 := by
      have h := hFixF
      rw [hcardι] at h
      simpa using h
    calc Nat.card ↥E * Nat.card {v : ιM → K // ∀ g ∈ E, (g : Matrix ιM ιM K) *ᵥ v = v}
        ≤ (2 * Nat.card ↥F) *
            Nat.card {v : ιM → K // ∀ g ∈ F, (g : Matrix ιM ιM K) *ᵥ v = v} :=
          Nat.mul_le_mul hcardE hmono
      _ = 2 * (Nat.card ↥F *
            Nat.card {v : ιM → K // ∀ g ∈ F, (g : Matrix ιM ιM K) *ᵥ v = v}) :=
          Nat.mul_assoc 2 _ _
      _ ≤ 2 * Nat.card K ^ 3 := Nat.mul_le_mul_left 2 hFixF'

end CFSG.LocalAnalysis.UniquenessCase.UC22.KOm

end
