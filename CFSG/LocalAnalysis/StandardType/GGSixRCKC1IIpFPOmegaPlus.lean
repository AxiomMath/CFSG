module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpRecDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeF1POmegaPlus
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeOmegaFourMinus
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepA2
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDegreeOneGFTwo
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpBlockFixed
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpFPOmegaPlusFixed
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpFPOmegaPlusBlocks
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpFPOmegaPlusFE
import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIpIso

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType
  CFSG.StandardType.RCKRP CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

theorem rckLemmaFIIpAt_POmegaPlus :
    RCKLemmaFIIpAt .POmegaPlus := by
  intro X _ _ p K J B d hp hp2 hBab hdB hBK _hBJ hrank hmodel _hodd hcomp hoddJ hrow
  rcases hmodel with ⟨m, g, φ, hg, hφr, hφk, hdiag⟩
  have hA8 := CFSG.StandardType.RCKK1IIp.rckIIp_iso hrow
  by_cases hm : 3 ≤ m
  swap
  · exfalso
    have hU : ggU .POmegaPlus m g = trivialUniversal := by
      simp only [ggU, lieUniversal, dif_neg hm]
    have hsubK : Subsingleton (ggU .POmegaPlus m g).K := by
      rw [hU]
      show Subsingleton (Matrix.SpecialLinearGroup (Fin 1) (ZMod 2))
      infer_instance
    have hsubRange : Subsingleton ↥(φ.range) :=
      @Function.Surjective.subsingleton (ggU .POmegaPlus m g).K ↥(φ.range)
        (MonoidHom.rangeRestrict φ) hsubK (MonoidHom.rangeRestrict_surjective φ)
    have hrange_bot : φ.range = ⊥ :=
      @Subgroup.eq_bot_of_subsingleton X _ (φ.range) hsubRange
    have hKbot : K = ⊥ := by rw [← hφr, hrange_bot]
    have hle : J ≤ (⊥ : Subgroup X) := by
      calc J ≤ K ⊓ Subgroup.centralizer ({d} : Set X) := hcomp.1
        _ = ⊥ := by rw [hKbot, bot_inf_eq]
    exact (Subgroup.nontrivial_iff_ne_bot J).mp
      (CFSG.ComponentClassification.Quasisimple.nontrivial hcomp.2.2) (le_bot_iff.mp hle)
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  obtain ⟨s, hs, hsodd, ε, hε, J', hJ'comp, hJ'map⟩ :=
    rckF1_POmegaPlus hp hp2 (hBab.2 d hdB) hg φ hφr hφk (hdiag d hdB) hcomp
  let j := Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 g))
  have hSU : ∀ a ∈ ({j s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 g))),
      a ∈ j.range := by
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    exact ⟨s, ha.symm⟩
  have hS : ∀ a ∈ ({j s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 g))),
      ∀ b ∈ ({j s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 g))), Commute a b := by
    intro a ha b hb
    rw [Set.mem_singleton_iff] at ha hb
    subst a
    subst b
    exact Commute.refl _
  have hoddS : ∀ a ∈ ({j s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 g))),
      Odd (orderOf a) := by
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst a
    exact hsodd
  have hoddJ' : Odd (Nat.card (Subgroup.center ↥(J'.map φ))) := by
    rw [hJ'map]
    exact hoddJ
  have hA8' : Nonempty ((↥(J'.map φ) ⧸ Subgroup.center ↥(J'.map φ)) ≃*
      alternatingGroup (Fin 8)) := by
    rw [hJ'map]
    exact hA8
  obtain ⟨e, he, heε, hcase⟩ :=
    exists_isPrimIdemIn_of_isPrimAdjIdemIn_POmegaPlus k g _ hSU hS hε
  rcases hcase with rfl | ⟨hne, hpair, hεeq⟩
  ·
    have hadj := hε.2.2.2.1
    by_cases hdeg2 : blockDegree (Algebra.adjoin (GaloisField 2 g)
        (Units.val '' ({j s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 g))))) e < 2
    · by_cases hm4 : e.rank = 4 ∧ ∀ x y : Fin (k + 3) ⊕ Fin (k + 3) → GaloisField 2 g,
          e.mulVec x = x → e.mulVec y = y → Spin.quadPlus (k + 3) (GaloisField 2 g) x = 0 →
          Spin.quadPlus (k + 3) (GaloisField 2 g) y = 0 →
          QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 g)) x y = 0 →
          ¬ LinearIndependent (GaloisField 2 g) ![x, y]
      · exact (rckF_POmegaPlus_not_omegaFourMinus hp hp2 hBab hdB hrank φ hφk hdiag s hs he
          hadj hm4 (hJ'comp.1.trans (Subgroup.commutator_le_self _)) hJ'map).elim
      · obtain ⟨rfl, hJ'eq, hdim⟩ :=
          rckIIp_POmegaPlus_selfDual_fixed hg φ hφk _ hSU hS hoddS he hadj hdeg2 hm4 hJ'comp
            hoddJ' hA8'
        have hse : (j s : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3))
            (GaloisField 2 1)) * e = e :=
          mul_eq_self_of_blockDegree_lt_two_gf2 he hdeg2
        have hblock := blockOn_glBlockCentralizer_of_mul_eq_self j he hse
        have hact : (fun (u : ↥(spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 1)))) v =>
            (j u : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3))
              (GaloisField 2 1)).mulVec v) =
            fun u v => Spin.spinAction (Spin.quadPlus (k + 3) (GaloisField 2 1)) u v := by
          funext u v
          exact Spin.spinMatrix_mulVec _ u v
        have hJ'eq' : J' = glBlockCentralizer j {j s} e := hJ'eq
        rw [hact, ← hJ'eq'] at hblock
        have hQ : IsUnit (LinearMap.toMatrix₂' (GaloisField 2 1)
            (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 1)))).det :=
          (Matrix.nondegenerate_iff_det_ne_zero.mp
            (LinearMap.BilinForm.Nondegenerate.toMatrix'
              (Spin.nondegenerate_polarBilin_quadPlus (k + 3) (GaloisField 2 1)))).isUnit
        exact Or.inr (Or.inr (Or.inl ⟨k + 3, φ, LinearMap.range (Matrix.toLin' e),
          LinearMap.ker (Matrix.toLin' e), J', hφr, hφk, hblock, hJ'map,
          polar_eq_zero_of_formAdj_eq_self _ hQ he.2.1 hadj, hdim⟩))
    · by_cases hdeg4 : blockDegree (Algebra.adjoin (GaloisField 2 g)
          (Units.val '' ({j s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 g))))) e < 4
      · exact (rckIIp_POmegaPlus_selfDual_two hg φ hφk _ hSU hS hoddS he hadj (by omega) hdeg4
          hJ'comp hoddJ' hA8').elim
      · exact (rckIIp_POmegaPlus_fieldExt hg φ hφk _ hSU hS hoddS hε hJ'comp he heε
          (Or.inl ⟨rfl, by omega⟩) hA8').elim
  ·
    by_cases hdeg2 : blockDegree (Algebra.adjoin (GaloisField 2 g)
        (Units.val '' ({j s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 g))))) e < 2
    · exact (rckIIp_POmegaPlus_dualPair_one hg φ hφk (j s) ⟨s, rfl⟩ hsodd he hpair hεeq hdeg2
        hJ'comp hoddJ' hA8').elim
    · exact (rckIIp_POmegaPlus_fieldExt hg φ hφk _ hSU hS hoddS hε hJ'comp he heε
        (Or.inr ⟨hne, by omega⟩) hA8').elim

end CFSG.StandardType.RCKC1
