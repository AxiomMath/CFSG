module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LieType.Universal.Spin.Action
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualTwoPOmegaPlus
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelDualPairPOmegaPlus
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpAltEightSU
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpSLOrder
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDegreeOneGFTwo
import CFSG.LocalAnalysis.StandardType.TableC.OrthGram

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.LieType.Universal CFSG.StandardType CFSG.StandardType.ClassicalPosition

theorem rckIIp_POmegaPlus_selfDual_two
    {X : Type} [Group X] {k f : ℕ} (hf : 1 ≤ f)
    (φ : (ggU .POmegaPlus (k + 3) f).K →* X)
    (hφk : φ.ker ≤ Subgroup.center (ggU .POmegaPlus (k + 3) f).K)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup (ggU .POmegaPlus (k + 3) f).K}
    (hJe : IsComponentOf J'
      ⁅(glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S e :
          Subgroup (ggU .POmegaPlus (k + 3) f).K),
        (glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S e :
          Subgroup (ggU .POmegaPlus (k + 3) f).K)⁆)
    (hoddJ : Odd (Nat.card (Subgroup.center ↥(J'.map φ))))
    (hA8 : Nonempty ((↥(J'.map φ) ⧸ Subgroup.center ↥(J'.map φ)) ≃* alternatingGroup (Fin 8))) :
    False := by
  obtain ⟨r, ι, β₀, hdim, hlong, hcent, hrange, rest⟩ :=
    exists_blockModel_selfDualTwo_POmegaPlus_explicit k f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
  let ιA : (ggU .PSU r (max f 1)).K →* (ggU .POmegaPlus (k + 3) f).K := ι
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

theorem rckIIp_POmegaPlus_dualPair_one
    {X : Type} [Group X] {k f : ℕ} (hf : 1 ≤ f)
    (φ : (ggU .POmegaPlus (k + 3) f).K →* X)
    (hφk : φ.ker ≤ Subgroup.center (ggU .POmegaPlus (k + 3) f).K)
    (s : GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))
    (hsU : s ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range)
    (hsodd : Odd (orderOf s))
    {ε e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' {s})) e)
    (hpair : formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) e ≠ e)
    (hεeq : ε = e + formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' {s})) e < 2)
    {J' : Subgroup (ggU .POmegaPlus (k + 3) f).K}
    (hJe : IsComponentOf J'
      ⁅(glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) {s} ε :
          Subgroup (ggU .POmegaPlus (k + 3) f).K),
        (glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) {s} ε :
          Subgroup (ggU .POmegaPlus (k + 3) f).K)⁆)
    (hoddJ : Odd (Nat.card (Subgroup.center ↥(J'.map φ))))
    (hA8 : Nonempty ((↥(J'.map φ) ⧸ Subgroup.center ↥(J'.map φ)) ≃* alternatingGroup (Fin 8))) :
    False := by
  subst hεeq
  have hSU : ∀ t ∈ ({s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))),
      t ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range := by
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst ht
    exact hsU
  have hS : ∀ t ∈ ({s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))),
      ∀ t' ∈ ({s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))), Commute t t' := by
    intro t ht t' ht'
    rw [Set.mem_singleton_iff] at ht ht'
    subst ht
    subst ht'
    exact Commute.refl _
  have hodd : ∀ t ∈ ({s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))),
      Odd (orderOf t) := by
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst ht
    exact hsodd
  obtain ⟨r, ι, β₀, hdim, hlong, hcent, hrange, rest⟩ :=
    exists_blockModel_dualPair_POmegaPlus_explicit k f hf {s} hSU hS hodd he hpair hdeg hJe
  let ιA : (ggU .PSL (r + 1) f).K →* (ggU .POmegaPlus (k + 3) f).K := ι
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
  have hG : IsUnit (LinearMap.toMatrix₂' (GaloisField 2 1)
      (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 1)))).det :=
    CFSG.StandardType.TableC.polarGram_isUnit_det _
      (Spin.nondegenerate_polarBilin_quadPlus (k + 3) (GaloisField 2 1))
  obtain ⟨u, rfl⟩ := hsU
  have hs : Matrix.transpose (((Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 1)) u :
        GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 1)) :
        Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 1))) *
      LinearMap.toMatrix₂' (GaloisField 2 1)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 1))) *
      (((Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 1)) u :
        GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 1)) :
        Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 1))) =
      LinearMap.toMatrix₂' (GaloisField 2 1)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 1))) :=
    CFSG.StandardType.TableC.spinMatrix_isometry _ u
  exact hpair (formAdj_eq_self_of_blockDegree_lt_two_gf2 hG hs he hdeg)

end CFSG.StandardType.RCKC1
