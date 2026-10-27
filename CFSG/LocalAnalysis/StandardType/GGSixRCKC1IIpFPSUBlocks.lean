module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualPSU
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelDualPairPSU
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpAltEightSU
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpSLOrder

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.LieType.Universal CFSG.StandardType CFSG.StandardType.ClassicalPosition

theorem rckIIp_PSU_selfDual_one
    {X : Type} [Group X] {n g : ℕ}
    (φ : (ggU .PSU n (g + 1)).K →* X)
    (hφk : φ.ker ≤ Subgroup.center (ggU .PSU n (g + 1)).K)
    (S : Set (GL (Fin n) (GaloisField 2 (2 * (g + 1)))))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e)
    (hadj : formAdj
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
      (Unitary.antidiag n) e = e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e < 2)
    {J' : Subgroup (ggU .PSU n (g + 1)).K}
    (hJe : IsComponentOf J'
      ⁅(glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
          (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype S e :
          Subgroup (ggU .PSU n (g + 1)).K),
        (glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
          (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype S e :
          Subgroup (ggU .PSU n (g + 1)).K)⁆)
    (hoddJ : Odd (Nat.card (Subgroup.center ↥(J'.map φ))))
    (hA8 : Nonempty ((↥(J'.map φ) ⧸ Subgroup.center ↥(J'.map φ)) ≃* alternatingGroup (Fin 8))) :
    False := by
  obtain ⟨r, ι, β₀, hdim, hlong, hcent, hrange, rest⟩ :=
    exists_blockModel_selfDual_PSU_explicit n g S hS he hadj hdeg hJe
  let ιA : (ggU .PSU r (g + 1)).K →* (ggU .PSU n (g + 1)).K := ι
  let π : (ggU .PSU r (g + 1)).K →* X := φ.comp ιA
  have hπr : π.range = J'.map φ := by
    dsimp only [π]
    rw [MonoidHom.range_comp]
    rw [show ιA.range = J' from hrange]
  have hπk : π.ker ≤ Subgroup.center (ggU .PSU r (g + 1)).K := by
    intro y hy
    exact hcent y (hφk hy)
  have hoddπ : Odd (Nat.card (Subgroup.center ↥π.range)) := by
    rw [hπr]
    exact hoddJ
  have hA8π : Nonempty ((↥π.range ⧸ Subgroup.center ↥π.range) ≃* alternatingGroup (Fin 8)) := by
    rw [hπr]
    exact hA8
  exact rckIIp_false_of_alt_eight_PSU (r := r) (h := g + 1) (by omega) π hπk hoddπ hA8π

theorem rckIIp_PSU_dualPair_one
    {X : Type} [Group X] {n g : ℕ}
    (φ : (ggU .PSU n (g + 1)).K →* X)
    (hφk : φ.ker ≤ Subgroup.center (ggU .PSU n (g + 1)).K)
    (S : Set (GL (Fin n) (GaloisField 2 (2 * (g + 1)))))
    (hSU : ∀ s ∈ S, Unitary.conjTr
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
      (s : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) * Unitary.antidiag n *
      (s : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) = Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e)
    (hpair : formAdj
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
      (Unitary.antidiag n) e ≠ e)
    (hεeq : ε = e + formAdj
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
      (Unitary.antidiag n) e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e < 2)
    {J' : Subgroup (ggU .PSU n (g + 1)).K}
    (hJe : IsComponentOf J'
      ⁅(glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
          (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype S ε :
          Subgroup (ggU .PSU n (g + 1)).K),
        (glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
          (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype S ε :
          Subgroup (ggU .PSU n (g + 1)).K)⁆)
    (hoddJ : Odd (Nat.card (Subgroup.center ↥(J'.map φ))))
    (hA8 : Nonempty ((↥(J'.map φ) ⧸ Subgroup.center ↥(J'.map φ)) ≃* alternatingGroup (Fin 8))) :
    False := by
  subst hεeq
  obtain ⟨k, ι, β₀, hdim, hconj, hlong, hcent, hrange, rest⟩ :=
    exists_blockModel_dualPair_PSU_explicitModel n g S hSU hS he hpair hdeg hJe
  let ιA : (ggU .PSL (k + 1) (2 * (g + 1))).K →* (ggU .PSU n (g + 1)).K := ι
  let π : (ggU .PSL (k + 1) (2 * (g + 1))).K →* X := φ.comp ιA
  have hπr : π.range = J'.map φ := by
    dsimp only [π]
    rw [MonoidHom.range_comp]
    rw [show ιA.range = J' from hrange]
  have hπk : π.ker ≤ Subgroup.center (ggU .PSL (k + 1) (2 * (g + 1))).K := by
    intro y hy
    exact hcent y (hφk hy)
  have hoddπ : Odd (Nat.card (Subgroup.center ↥π.range)) := by
    rw [hπr]
    exact hoddJ
  have hA8π : Nonempty ((↥π.range ⧸ Subgroup.center ↥π.range) ≃* alternatingGroup (Fin 8)) := by
    rw [hπr]
    exact hA8
  have h1 : 2 * (g + 1) = 1 :=
    (rckIIp_eq_three_one_of_alt_eight (h := 2 * (g + 1)) (by omega) π hπk hoddπ hA8π).2
  omega

end CFSG.StandardType.RCKC1
