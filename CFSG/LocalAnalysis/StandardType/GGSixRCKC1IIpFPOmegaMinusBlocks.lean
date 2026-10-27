module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LieType.Universal.Spin.Action
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualTwoPOmegaMinus
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelDualPairPOmegaMinus
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpAltEightSU
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpSLOrder
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDegreeOneGFTwo
import CFSG.LocalAnalysis.StandardType.TableC.OrthGram

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.LieType.Universal CFSG.StandardType CFSG.StandardType.ClassicalPosition

theorem rckIIp_POmegaMinus_selfDual_two
    {X : Type} [Group X] {n f : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f)
    (φ : (ggU .POmegaMinus n f).K →* X)
    (hφk : φ.ker ≤ Subgroup.center (ggU .POmegaMinus n f).K)
    (S : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix
      (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
      (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin
          (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup (ggU .POmegaMinus n f).K}
    (hJe : IsComponentOf J'
      ⁅(glBlockCentralizer (Spin.spinMatrix
          (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) S e :
          Subgroup (ggU .POmegaMinus n f).K),
        (glBlockCentralizer (Spin.spinMatrix
          (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) S e :
          Subgroup (ggU .POmegaMinus n f).K)⁆)
    (hoddJ : Odd (Nat.card (Subgroup.center ↥(J'.map φ))))
    (hA8 : Nonempty ((↥(J'.map φ) ⧸ Subgroup.center ↥(J'.map φ)) ≃* alternatingGroup (Fin 8))) :
    False := by
  obtain ⟨r, ι, β₀, hdim, hlong, hcent, hrange, rest⟩ :=
    exists_blockModel_selfDualTwo_POmegaMinus_explicit n f S hSU hS hodd he hn hadj hdeg₁
      hdeg₂ hJe
  let ιA : (ggU .PSU r (max f 1)).K →* (ggU .POmegaMinus n f).K := ι
  let π : (ggU .PSU r (max f 1)).K →* X := φ.comp ιA
  have hπr : π.range = J'.map φ := by
    dsimp only [π]
    rw [MonoidHom.range_comp]
    rw [show ιA.range = J' from hrange]
  have hπk : π.ker ≤ Subgroup.center (ggU .PSU r (max f 1)).K := by
    intro y hy
    exact hcent y (hφk hy)
  have hoddπ : Odd (Nat.card (Subgroup.center ↥π.range)) := by
    rw [hπr]
    exact hoddJ
  have hA8π : Nonempty ((↥π.range ⧸ Subgroup.center ↥π.range) ≃* alternatingGroup (Fin 8)) := by
    rw [hπr]
    exact hA8
  have hmax : 1 ≤ max f 1 := le_trans hf (le_max_left f 1)
  exact rckIIp_false_of_alt_eight_PSU (r := r) (h := max f 1) hmax π hπk hoddπ hA8π

theorem rckIIp_POmegaMinus_dualPair_one
    {X : Type} [Group X] {n f : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f)
    (φ : (ggU .POmegaMinus n f).K →* X)
    (hφk : φ.ker ≤ Subgroup.center (ggU .POmegaMinus n f).K)
    (s : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f))
    (hsU : s ∈ (Spin.spinMatrix
      (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)).range)
    (hsodd : Odd (orderOf s))
    {ε e : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
      (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' {s})) e)
    (hpair : formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin
          (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))) e ≠ e)
    (hεeq : ε = e + formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin
          (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))) e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' {s})) e < 2)
    {J' : Subgroup (ggU .POmegaMinus n f).K}
    (hJe : IsComponentOf J'
      ⁅(glBlockCentralizer (Spin.spinMatrix
          (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) {s} ε :
          Subgroup (ggU .POmegaMinus n f).K),
        (glBlockCentralizer (Spin.spinMatrix
          (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) {s} ε :
          Subgroup (ggU .POmegaMinus n f).K)⁆)
    (hoddJ : Odd (Nat.card (Subgroup.center ↥(J'.map φ))))
    (hA8 : Nonempty ((↥(J'.map φ) ⧸ Subgroup.center ↥(J'.map φ)) ≃* alternatingGroup (Fin 8))) :
    False := by
  subst hεeq
  have hSU : ∀ t ∈ ({s} : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f))),
      t ∈ (Spin.spinMatrix
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)).range := by
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst ht
    exact hsU
  have hS : ∀ t ∈ ({s} : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f))),
      ∀ t' ∈ ({s} : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f))),
        Commute t t' := by
    intro t ht t' ht'
    rw [Set.mem_singleton_iff] at ht ht'
    subst ht
    subst ht'
    exact Commute.refl _
  have hodd : ∀ t ∈ ({s} : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f))),
      Odd (orderOf t) := by
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst ht
    exact hsodd
  obtain ⟨r, ι, β₀, hdim, hlong, hcent, hrange, rest⟩ :=
    exists_blockModel_dualPair_POmegaMinus_explicit n f hf {s} hSU hS hodd he hn hpair hdeg
      hJe
  let ιA : (ggU .PSL (r + 1) f).K →* (ggU .POmegaMinus n f).K := ι
  let π : (ggU .PSL (r + 1) f).K →* X := φ.comp ιA
  have hπr : π.range = J'.map φ := by
    dsimp only [π]
    rw [MonoidHom.range_comp]
    rw [show ιA.range = J' from hrange]
  have hπk : π.ker ≤ Subgroup.center (ggU .PSL (r + 1) f).K := by
    intro y hy
    exact hcent y (hφk hy)
  have hoddπ : Odd (Nat.card (Subgroup.center ↥π.range)) := by
    rw [hπr]
    exact hoddJ
  have hA8π : Nonempty ((↥π.range ⧸ Subgroup.center ↥π.range) ≃* alternatingGroup (Fin 8)) := by
    rw [hπr]
    exact hA8
  have hf1 : f = 1 :=
    (rckIIp_eq_three_one_of_alt_eight (h := f) hf π hπk hoddπ hA8π).2
  subst f
  have hG := CFSG.StandardType.TableC.polarGram_isUnit_det _
    (Spin.nondegenerate_polarBilin_quadMinus_of_finite n (GaloisField 2 1) (minusCoeffs_irr 2 1))
  obtain ⟨u, rfl⟩ := hsU
  exact hpair (formAdj_eq_self_of_blockDegree_lt_two_gf2 hG
    (CFSG.StandardType.TableC.spinMatrix_isometry _ u) he hdeg)

end CFSG.StandardType.RCKC1
