module

public import CFSG.RankThree.PartTwo.KFacts.AutKinds
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherGeneration
import CFSG.LocalAnalysis.ComponentInitial.ScalarSemilinearNormalizer

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

variable (r : ℕ) (K : Type) [Field K]

theorem conj_proj_eq_spConjAut (g : StatedSp r K) :
    MulAut.conj (proj r K g) = conjAut r K ⟨g, statedSp_le_gsp g.2⟩ := by
  ext x
  obtain ⟨h, rfl⟩ := proj_surjective x
  rw [MulAut.conj_apply, conjAut_proj, ← map_inv, ← map_mul, ← map_mul]
  exact congrArg (proj r K) (Subtype.ext rfl)

theorem innAut_le_range_spConjAut :
    (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).range ≤
      (conjAut r K).range := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨g, rfl⟩ := proj_surjective x
  exact ⟨_, (conj_proj_eq_spConjAut r K g).symm⟩

@[expose] noncomputable def stdPinnedPSp : PinnedAut (StatedProj (StatedSp r K)) where
  inndiag := (conjAut r K).range
  inn_le := innAut_le_range_spConjAut r K
  field := (fieldAut r K).range
  graph := ∅

variable {r K}

theorem stdPinnedPSp_stable [Finite K] (hr : 3 ≤ r) : (stdPinnedPSp r K).Stable := by
  obtain ⟨-, hform⟩ := automorphism_generation (K := K) hr
  have hcomm : ∀ σ τ : K ≃+* K, fieldAut r K σ * fieldAut r K τ = fieldAut r K τ * fieldAut r K σ :=
    fun σ τ => by
      rw [← map_mul, ← map_mul, CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm K σ τ]
  have hconj : ∀ α : MulAut (StatedProj (StatedSp r K)), ∃ A : gsp r K, ∀ τ : K ≃+* K,
      α * fieldAut r K τ * α⁻¹ = conjAut r K A * fieldAut r K τ * (conjAut r K A)⁻¹ := by
    intro α
    obtain ⟨A, σ, rfl⟩ := hform α
    refine ⟨A, fun τ => ?_⟩
    have h1 := hcomm σ τ
    calc conjAut r K A * fieldAut r K σ * fieldAut r K τ * (conjAut r K A * fieldAut r K σ)⁻¹ =
        conjAut r K A * (fieldAut r K σ * fieldAut r K τ) * (fieldAut r K σ)⁻¹ *
          (conjAut r K A)⁻¹ := by group
      _ = conjAut r K A * fieldAut r K τ * (conjAut r K A)⁻¹ := by rw [h1]; group
  refine ⟨⟨fun d hd α => ?_⟩, ?_, ?_, ?_⟩
  · obtain ⟨B, rfl⟩ := hd
    obtain ⟨A, σ, rfl⟩ := hform α
    refine ⟨A * gspFieldMap σ B * A⁻¹, ?_⟩
    rw [map_mul, map_mul, map_inv, ← fieldAut_mul_conjAut_mul_inv]
    group
  · rintro α _ ⟨τ, rfl⟩ h1
    obtain ⟨A, hA⟩ := hconj α
    exact ⟨fieldAut r K τ, ⟨τ, rfl⟩, h1, conjAut r K A, ⟨A, rfl⟩, hA τ⟩
  · rintro α γ hγ
    exact absurd hγ (Set.notMem_empty γ)
  · rintro α γ φ hγ
    exact absurd hγ (Set.notMem_empty γ)

section Induced

variable {G : Type*} [Group G] [Finite G] (L : Subgroup G)

variable (r K) in
@[expose] def InducesKindPSp (x : G) (k : AutKind) : Prop :=
  ∃ e : L ⧸ aschbacherSolvableCore 3 L ≃* StatedProj (StatedSp r K),
    InducesKind L (stdPinnedPSp r K) e x k

theorem inducesKindPSp_iff_of_stable (hP : (stdPinnedPSp r K).Stable)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* StatedProj (StatedSp r K)) (x : G) (k : AutKind) :
    InducesKindPSp r K L x k ↔ InducesKind L (stdPinnedPSp r K) e x k := by
  constructor
  · rintro ⟨e', h⟩
    exact (inducesKind_iff_of_stable L hP e' e x k).1 h
  · intro h
    exact ⟨e, h⟩

theorem inducesKindPSp_iff [Finite K] (hr : 3 ≤ r)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* StatedProj (StatedSp r K)) (x : G) (k : AutKind) :
    InducesKindPSp r K L x k ↔ InducesKind L (stdPinnedPSp r K) e x k :=
  inducesKindPSp_iff_of_stable L (stdPinnedPSp_stable hr) e x k

end Induced

end CFSG.RankThree.PartTwo.KFacts
