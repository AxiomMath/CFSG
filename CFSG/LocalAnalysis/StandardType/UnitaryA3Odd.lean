module

public import CFSG.LocalAnalysis.StandardType.UnitaryMatrixBridge
public import CFSG.LocalAnalysis.StandardType.UnitaryRepOdd
public import CFSG.LocalAnalysis.StandardType.UnitaryCubeRoots
public import CFSG.LocalAnalysis.StandardType.UnitaryPairs
public import CFSG.LocalAnalysis.StandardType.A8LiftBlocks

public section

namespace CFSG.StandardType

namespace UnitaryA3

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ}

theorem eq_one_of_odd (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) (hfo : Odd f) (hn : n = 6)
    {G : Type} [Group G] [Finite G] {ψ : SU (unitaryInvolution F 2 f) n →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) n))
    {Γ : Subgroup (SU (unitaryInvolution F 2 f) n)} (hperf : commutator ↥Γ = ⊤)
    (h5 : HasOrderFiveData ↥Γ) (h7 : HasOrderSevenData ↥Γ) {b : G} {A : GL (Fin n) F}
    (hbA : (b, A) ∈ UFusion.suInducedPairs ψ) (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1)
    (hcen : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (ψ.range : Set G)))
    (hbΓ : ∀ γ ∈ Γ, b * ψ γ = ψ γ * b) (γ : ↥Γ) : γ = 1 := by
  subst hn
  have hnq : ((6 : ℕ), 2 ^ f) ≠ (3, 2) := by simp
  obtain ⟨ζ, hζ1, hζ3, hσζ⟩ := UnitaryCubeRoots.exists_cubeRoot_inv_of_odd hF hf hfo
  obtain ⟨c, hc⟩ :=
    UnitaryPairs.exists_scalar_pow_of_mem_suInducedPairs hF hf (by norm_num) hnq hker hbA hb3
  have hnc := UnitaryMatrix.not_scalar_of_mem_suInducedPairs hbA hb3 hb1 hcen
  have hcomm := UnitaryPairs.commute_of_mem_suInducedPairs_of_perfect hker hperf hbA hbΓ
  obtain ⟨hAJ, -⟩ := hbA
  refine UnitaryMatrix.eq_one_of_repHom_eq_one _ Γ ?_
  refine UnitaryRep.eq_one_of_commute_odd (unitaryInvolution F 2 f) hζ1 hζ3 hσζ h5 h7 (by simp)
    UnitaryAlg.isUnit_antidiag (UnitaryMatrix.repHom _ 6 Γ) (UnitaryMatrix.repHom_form _ Γ)
    (A := (A : Matrix (Fin 6) (Fin 6) F)) (c := (c : F)) c.ne_zero
    (UnitaryMatrix.coe_pow_eq_smul_one hc) (UnitaryMatrix.transpose_form_of_isJUnitary hAJ) ?_
    (UnitaryMatrix.coe_ne_smul_one hnc) γ
  intro g
  have h := hcomm g g.2
  have h' := congrArg Units.val h
  simp only [Units.val_mul] at h'
  exact h'.symm

end UnitaryA3

end CFSG.StandardType
