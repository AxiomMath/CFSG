module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutGraph
public import CFSG.LocalAnalysis.StandardType.GGRootDetectSp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

namespace OrdPGraph

variable {r : ℕ} {K : Type} [Field K]

theorem fieldSp_mem_rootGroup (σ : K ≃+* K) {γ : Fin r → ℤ}
    (hγ : γ ∈ (Symplectic.rootDatum r K).roots) {z : StatedSp r K}
    (hz : z ∈ (Symplectic.rootDatum r K).rootGroup γ) :
    fieldSp r K σ z ∈ (Symplectic.rootDatum r K).rootGroup γ := by
  obtain ⟨ρ, hρ⟩ := Symplectic.SpExtras.exists_stdVec_of_mem_roots hγ
  obtain ⟨c, rfl⟩ := (Symplectic.SpExtras.mem_rootGroup_iff hρ).mp hz
  rw [RootDetectSp.fieldSp_elt]
  exact Symplectic.SpExtras.elt_mem_rootGroup hρ (σ c)

theorem modelDiagField_sp [Finite K] [CharP K 2] {p : ℕ}
    (hform : ∀ α : MulAut (StatedProj (StatedSp r K)), α ^ p = 1 →
      ∃ (A : gsp r K) (σ : K ≃+* K), α = conjAut r K A * fieldAut r K σ)
    (β : MulAut (StatedProj (StatedSp r K))) (hβ : β ^ p = 1) :
    ModelDiagField (Symplectic.rootDatum r K) (proj r K) β := by
  obtain ⟨A, σ, rfl⟩ := hform β hβ
  obtain ⟨a, ha⟩ := RootDetectSp.exists_sp_conj_eq A
  refine ⟨proj r K a, fun γ hγ z hz => ⟨fieldSp r K σ z, fieldSp_mem_rootGroup σ hγ hz, ?_⟩⟩
  rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj, ha, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  group

end OrdPGraph

section Family

theorem ggOrdPGraphModelAt_PSp : GGOrdPGraphModelAt .PSp := by
  intro n f hadm _
  obtain ⟨-, -, hn, -⟩ := hadm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  show ∃ (C : Type) (_ : Group C) (π : StatedSp n (GaloisField 2 f) →* C),
    Function.Surjective π ∧ π.ker = Subgroup.center (StatedSp n (GaloisField 2 f)) ∧
      ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ (StatedLieTag.PSp = .POmegaPlus ∧ n = 4 ∧ p = 3) →
        ∀ β : MulAut C, β ^ p = 1 →
          OrdPGraph.ModelDiagField (Symplectic.rootDatum n (GaloisField 2 f)) π β
  refine ⟨StatedProj (StatedSp n (GaloisField 2 f)), inferInstance, proj n (GaloisField 2 f),
    proj_surjective, ?_, fun p hp hp2 _ β hβ => ?_⟩
  · rw [ker_proj]
    exact (Symplectic.center_eq n _).symm
  · rcases (show 3 ≤ n ∨ n = 2 by omega) with h3 | rfl
    · exact OrdPGraph.modelDiagField_sp
        (fun α _ => (automorphism_generation (K := GaloisField 2 f) h3).2 α) β hβ
    · exact OrdPGraph.modelDiagField_sp
        (fun α hα => RootDetectSp.sp_two_form_of_pow_eq_one (hp.odd_of_ne_two hp2) α hα) β hβ

theorem ggOrdPGraphAt_PSp : GGOrdPGraphAt .PSp :=
  ggOrdPGraphAt_of_model ggOrdPGraphModelAt_PSp

end Family

end CFSG.StandardType
