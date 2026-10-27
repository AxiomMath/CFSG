module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpRecDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeF1PSU
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpFPSUSmall
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpFPSUBlocks
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpFPSUFE
import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIpIso

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType
  CFSG.StandardType.RCKRP CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

theorem rckLemmaFIIpAt_PSU
    : RCKLemmaFIIpAt .PSU := by
  intro X _ _ p K J B d hp hp2 hBab hdB hBK _hBJ _hrank hmodel _hodd hcomp hoddJ hrow
  rcases hmodel with ⟨n, g, φ, hg, hφr, hφk, hdiag⟩
  have hA8 := CFSG.StandardType.RCKK1IIp.rckIIp_iso hrow
  exfalso
  by_cases hn : n ≤ 2
  · have hJK : J ≤ φ.range := by
      rw [hφr]
      exact hcomp.1.trans inf_le_left
    exact rckIIp_false_of_PSU_le_two hn hg φ hJK hA8
  obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
  obtain ⟨s, hsU, -, hsodd, ε, hε, ⟨e, he, heε, hcase⟩, J', hJ'comp, hJ'map⟩ :=
    rckF1_PSU hp hp2 (hBab.2 d hdB) (by omega) φ hφr hφk (hBK hdB) (hdiag d hdB) hcomp
  have hJ'mapU : J'.map φ = J := hJ'map
  have hoddJ' : Odd (Nat.card (Subgroup.center ↥(J'.map φ))) := by
    rw [hJ'mapU]
    exact hoddJ
  have hA8' : Nonempty ((↥(J'.map φ) ⧸ Subgroup.center ↥(J'.map φ)) ≃*
      alternatingGroup (Fin 8)) := by
    rw [hJ'mapU]
    exact hA8
  have hSU : ∀ a ∈ ({s} : Set (GL (Fin n) (GaloisField 2 (2 * (g + 1))))), Unitary.conjTr
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
      (a : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) * Unitary.antidiag n *
      (a : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) = Unitary.antidiag n := by
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst a
    exact hsU
  have hS : ∀ a ∈ ({s} : Set (GL (Fin n) (GaloisField 2 (2 * (g + 1))))),
      ∀ b ∈ ({s} : Set (GL (Fin n) (GaloisField 2 (2 * (g + 1))))), Commute a b := by
    intro a ha b hb
    rw [Set.mem_singleton_iff] at ha hb
    subst a
    subst b
    exact Commute.refl _
  have hoddS : ∀ a ∈ ({s} : Set (GL (Fin n) (GaloisField 2 (2 * (g + 1))))), Odd (orderOf a) := by
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst a
    exact hsodd
  rcases hcase with rfl | ⟨_hne, hpair, hεeq⟩
  ·
    have hadj := hε.2.2.2.1
    by_cases hdeg2 : blockDegree (Algebra.adjoin (GaloisField 2 (2 * (g + 1)))
        (Units.val '' ({s} : Set (GL (Fin n) (GaloisField 2 (2 * (g + 1))))))) e < 2
    · exact rckIIp_PSU_selfDual_one φ hφk _ hS he hadj hdeg2 hJ'comp hoddJ' hA8'
    · exact rckIIp_PSU_fieldExt φ hφk _ hSU hS hoddS hε hJ'comp he heε (by omega) hA8'
  ·
    by_cases hdeg2 : blockDegree (Algebra.adjoin (GaloisField 2 (2 * (g + 1)))
        (Units.val '' ({s} : Set (GL (Fin n) (GaloisField 2 (2 * (g + 1))))))) e < 2
    · exact rckIIp_PSU_dualPair_one φ hφk _ hSU hS he hpair hεeq hdeg2 hJ'comp hoddJ' hA8'
    · exact rckIIp_PSU_fieldExt φ hφk _ hSU hS hoddS hε hJ'comp he heε (by omega) hA8'

end CFSG.StandardType.RCKC1
