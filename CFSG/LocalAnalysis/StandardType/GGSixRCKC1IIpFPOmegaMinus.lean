module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpRecDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeF1POmegaMinus
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeOmegaFourMinusPOmegaMinus
import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerMinus
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepA2
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDegreeOneGFTwo
import CFSG.LocalAnalysis.StandardType.TableC.OrthGram
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpBlockFixed
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpFPOmegaMinusSmall
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpFPOmegaMinusThree
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpFPOmegaMinusFixed
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpFPOmegaMinusBlocks
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpFPOmegaMinusFE
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpFPSU
import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIpIso

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType
  CFSG.StandardType.RCKRP CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

theorem rckLemmaFIIp_POmegaMinus_of_four_le
    {X : Type} [Group X] [Finite X] {p : ℕ} {K J B : Subgroup X} {d : X} (hp : p.Prime)
    (hp2 : p ≠ 2) (hBab : IsElemAbelian p B) (hdB : d ∈ B)
    (hrank : p ^ 2 * Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set X)) ≤ Nat.card B)
    {m g : ℕ} (hn : 4 ≤ m) (hg : 1 ≤ g) (φ : (ggU .POmegaMinus m g).K →* X) (hφr : φ.range = K)
    (hφk : φ.ker ≤ Subgroup.center (ggU .POmegaMinus m g).K)
    (hdiag : ∀ b ∈ B, GGPsiInnerDiag (ggU .POmegaMinus m g).D φ b)
    (hcomp : IsComponentOf J (K ⊓ Subgroup.centralizer {d}))
    (hoddJ : Odd (Nat.card (Subgroup.center ↥J))) (hrow : GGSixRCKJRow .IIp J) :
    K = J ∨ SLFourEmbed K J ∨ OmegaSixEmbed K J := by
  have hA8 := CFSG.StandardType.RCKK1IIp.rckIIp_iso hrow
  obtain ⟨s, hs, hsodd, ε, hε, J', hJ'comp, hJ'map⟩ :=
    rckF1_POmegaMinus hp hp2 (hBab.2 d hdB) (minusCoeffs_irr 2 g) hn φ hφr hφk (hdiag d hdB)
      hcomp
  let j := Spin.spinMatrix
    (Spin.quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1 (minusCoeffs 2 g).2)
  have hSU : ∀ a ∈ ({j s} : Set (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (GaloisField 2 g))),
      a ∈ j.range := by
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    exact ⟨s, ha.symm⟩
  have hS : ∀ a ∈ ({j s} : Set (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (GaloisField 2 g))),
      ∀ b ∈ ({j s} : Set (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (GaloisField 2 g))),
        Commute a b := by
    intro a ha b hb
    rw [Set.mem_singleton_iff] at ha hb
    subst a
    subst b
    exact Commute.refl _
  have hoddS : ∀ a ∈ ({j s} : Set (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (GaloisField 2 g))),
      Odd (orderOf a) := by
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst a
    exact hsodd
  have hJ'mapU : J'.map φ = J := hJ'map
  have hoddJ' : Odd (Nat.card (Subgroup.center ↥(J'.map φ))) := by
    rw [hJ'mapU]
    exact hoddJ
  have hA8' : Nonempty ((↥(J'.map φ) ⧸ Subgroup.center ↥(J'.map φ)) ≃*
      alternatingGroup (Fin 8)) := by
    rw [hJ'mapU]
    exact hA8
  obtain ⟨e, he, heε, hcase⟩ :=
    exists_isPrimIdemIn_of_isPrimAdjIdemIn_POmegaMinus m g _ hSU hS hε
  rcases hcase with rfl | ⟨hne, hpair, hεeq⟩
  ·
    have hadj := hε.2.2.2.1
    by_cases hdeg2 : blockDegree (Algebra.adjoin (GaloisField 2 g)
        (Units.val '' ({j s} : Set (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
          (GaloisField 2 g))))) e < 2
    · by_cases hm4 : e.rank = 4 ∧ ∀ x y : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → GaloisField 2 g,
          e.mulVec x = x → e.mulVec y = y →
          Spin.quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1 (minusCoeffs 2 g).2 x = 0 →
          Spin.quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1 (minusCoeffs 2 g).2 y = 0 →
          QuadraticMap.polar
            (Spin.quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1 (minusCoeffs 2 g).2) x y = 0 →
          ¬ LinearIndependent (GaloisField 2 g) ![x, y]
      · exact (rckF_POmegaMinus_not_omegaFourMinus hp hp2 hBab hdB hrank (minusCoeffs_irr 2 g) hn
          φ hφk hdiag s hs he hadj hm4 (hJ'comp.1.trans (Subgroup.commutator_le_self _))
          hJ'map).elim
      · obtain ⟨rfl, hJ'eq, hdim⟩ :=
          rckIIp_POmegaMinus_selfDual_fixed hn hg φ hφk _ hSU hS hoddS he hadj hdeg2 hm4 hJ'comp
            hoddJ' hA8'
        have hse : (j s : Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
            (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (GaloisField 2 1)) * e = e :=
          mul_eq_self_of_blockDegree_lt_two_gf2 he hdeg2
        have hblock := blockOn_glBlockCentralizer_of_mul_eq_self j he hse
        have hact : (fun (u : ↥(spinGroup
            (Spin.quadMinus m (GaloisField 2 1) (minusCoeffs 2 1).1 (minusCoeffs 2 1).2))) v =>
            (j u : Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
              (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (GaloisField 2 1)).mulVec v) =
            fun u v => Spin.spinAction _ u v := by
          funext u v
          exact Spin.spinMatrix_mulVec _ u v
        have hJ'eq' : J' = glBlockCentralizer j {j s} e := hJ'eq
        rw [hact, ← hJ'eq'] at hblock
        have hQ := CFSG.StandardType.TableC.polarGram_isUnit_det _
          (Spin.nondegenerate_polarBilin_quadMinus_of_finite m (GaloisField 2 1)
            (minusCoeffs_irr 2 1))
        exact Or.inr (Or.inr (Or.inr ⟨m, φ, LinearMap.range (Matrix.toLin' e),
          LinearMap.ker (Matrix.toLin' e), J', hφr, hφk, hblock, hJ'map,
          polar_eq_zero_of_formAdj_eq_self _ hQ he.2.1 hadj, hdim⟩))
    · by_cases hdeg4 : blockDegree (Algebra.adjoin (GaloisField 2 g)
          (Units.val '' ({j s} : Set (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
            (GaloisField 2 g))))) e < 4
      · exact (rckIIp_POmegaMinus_selfDual_two hn hg φ hφk _ hSU hS hoddS he hadj (by omega)
          hdeg4 hJ'comp hoddJ' hA8').elim
      · exact (rckIIp_POmegaMinus_fieldExt hn hg φ hφk _ hSU hS hoddS hε hJ'comp he heε
          (Or.inl ⟨rfl, by omega⟩) hA8').elim
  ·
    by_cases hdeg2 : blockDegree (Algebra.adjoin (GaloisField 2 g)
        (Units.val '' ({j s} : Set (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
          (GaloisField 2 g))))) e < 2
    · exact (rckIIp_POmegaMinus_dualPair_one hn hg φ hφk (j s) ⟨s, rfl⟩ hsodd he hpair hεeq
        hdeg2 hJ'comp hoddJ' hA8').elim
    · exact (rckIIp_POmegaMinus_fieldExt hn hg φ hφk _ hSU hS hoddS hε hJ'comp he heε
        (Or.inr ⟨hne, by omega⟩) hA8').elim

theorem rckLemmaFIIpAt_POmegaMinus :
    RCKLemmaFIIpAt .POmegaMinus := by
  intro X _ _ p K J B d hp hp2 hBab hdB hBK hBJ hrank hmodel hodd hcomp hoddJ hrow
  rcases hmodel with ⟨m, g, φ, hg, hφr, hφk, hdiag⟩
  by_cases hm2 : m ≤ 2
  · have hJK : J ≤ φ.range := by
      rw [hφr]
      exact hcomp.1.trans inf_le_left
    exact (rckIIp_false_of_POmegaMinus_le_two hm2 hg φ hJK
      (CFSG.StandardType.RCKK1IIp.rckIIp_iso hrow)).elim
  by_cases hm3 : m = 3
  · subst hm3
    let φ₃ : ↥(spinGroup
        (Spin.quadMinus 3 (GaloisField 2 g) (minusCoeffs 2 g).1 (minusCoeffs 2 g).2)) →* X := φ
    have hmodel : RCKClassicalModelIDAt .PSU K B :=
      rckClassicalModelIDAt_PSU_of_POmegaMinus_three hg φ hφr hφk fun b hb =>
        PsiDiag.SpinM.exists_mem_centralizer_three (minusCoeffs_irr 2 g) φ₃ hφk (hdiag b hb)
    exact rckLemmaFIIpAt_PSU X p K J B d hp hp2 hBab hdB hBK hBJ hrank hmodel hodd hcomp hoddJ
      hrow
  exact rckLemmaFIIp_POmegaMinus_of_four_le hp hp2 hBab hdB hrank (by omega) hg φ hφr hφk hdiag
    hcomp hoddJ hrow

end CFSG.StandardType.RCKC1
