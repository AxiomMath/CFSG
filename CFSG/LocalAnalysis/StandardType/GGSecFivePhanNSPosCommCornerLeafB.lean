module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosCommAux
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosLiftE
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosRank
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosCommCornerLeaf
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosCommCornerLeafBHeis
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosCommCornerLeafBEig
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosCommCornerLeafBNorm
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosCommCornerLeafBTrans
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosCommCornerLeafBGlue

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

theorem ggNSPosPF3C_centre_killed_contradiction {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} {ψ : Su K 2 f 6 →* G}
    (h : GGNSLocalHyp 3 B Bs K f 6 ψ) {b₁ b₂ : G} (hb₁ : b₁ ∈ Bs) (hb₂ : b₂ ∈ Bs)
    {g₁ g₂ : GL (Fin 6) K}
    (h₁ : GGInducesUnitary (p := 2) (f := f) ψ b₁ g₁)
    (h₂ : GGInducesUnitary (p := 2) (f := f) ψ b₂ g₂) {z : K}
    (hz : ((ggNSPosPF_commutator g₁ g₂ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = z • 1)
    (hz1 : z ≠ 1) (hz0 : z ≠ 0) {x : Su K 2 f 6}
    (hx : (x : GL (Fin 6) K) = ggNSPosPF3C_scalarGL (n := 6) z hz0) (hxeq : ψ x = 1) : False := by
  have hz3 : z ^ 3 = 1 := ggNSPosPF_commutator_pow_prime_aux h hb₁ hb₂ h₁ h₂ hz
  have hne : g₁ * g₂ ≠ g₂ * g₁ := by
    intro hcomm
    have hc1 : ggNSPosPF_commutator g₁ g₂ = 1 :=
      (ggNSPosPF_commutator_eq_one_iff g₁ g₂).mpr hcomm
    have hmat : (1 : Matrix (Fin 6) (Fin 6) K) = z • 1 := by
      have h' := hz
      rw [hc1] at h'
      simpa using h'
    have h00 : (1 : Matrix (Fin 6) (Fin 6) K) ⟨0, by norm_num⟩ ⟨0, by norm_num⟩ =
        (z • 1 : Matrix (Fin 6) (Fin 6) K) ⟨0, by norm_num⟩ ⟨0, by norm_num⟩ :=
      congrArg (fun M => M ⟨0, by norm_num⟩ ⟨0, by norm_num⟩) hmat
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h00
    exact hz1 h00.symm
  obtain ⟨ω, X, Y, N, hω, hX3, hYX, hNX, hNY, hN3, hNns, hXlift, hYlift, hNlift, hdim⟩ :=
    ggNSPosPF3C_heisenberg_data h hb₁ hb₂ h₁ h₂ hne
  obtain ⟨τ, hτ, hNq⟩ :=
    ggNSPosPF3C_quadratic_of_commutant hω hX3 hYX hNX hNY hN3 hNns hdim
  obtain ⟨c, hD, hXu, hcu⟩ :=
    ggNSPosPF3C_exists_shearData h hω hX3 hYX hNX hNY hNns hXlift hNlift hτ hNq
  have hμ := ggNSPosPF3C_psi_scalar_eq_one hz3 hz1 hz0 hx hxeq
  exact ggNSPosPF3C_false_of_shearData h hD hXu hYlift hcu hμ

end CFSG.StandardType

end
