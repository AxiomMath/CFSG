module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpRecDefs
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeF1PSp
import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIpIso
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpFPSpCases

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType
  CFSG.StandardType.RCKRP CFSG.StandardType.ClassicalPosition

theorem rckLemmaFIIpAt_PSp :
    RCKLemmaFIIpAt .PSp := by
  intro X _ _ p K J B d hp hp2 hBab hdB hBK _hBJ _hrank hmodel _hodd hcomp hoddJ hrow
  rcases hmodel with ⟨m, g, φ, hg, hφr, hφk, hdiag⟩
  have hA8 := CFSG.StandardType.RCKK1IIp.rckIIp_iso hrow
  exfalso
  obtain ⟨s, hs, -, hsodd, ε, hε, ⟨e, he, heε, hcase⟩, J', hJ'comp, hJ'map⟩ :=
    rckF1_PSp hp hp2 (hBab.2 d hdB) hg φ hφr hφk (hBK hdB) (hdiag d hdB) hcomp
  have hSU : ∀ a ∈ ({s} : Set (GL (Fin m ⊕ Fin m) (GaloisField 2 g))),
      a ∈ CFSG.Open.StatedSp m (GaloisField 2 g) := by
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst a
    exact hs
  have hS : ∀ a ∈ ({s} : Set (GL (Fin m ⊕ Fin m) (GaloisField 2 g))),
      ∀ b ∈ ({s} : Set (GL (Fin m ⊕ Fin m) (GaloisField 2 g))), Commute a b := by
    intro a ha b hb
    rw [Set.mem_singleton_iff] at ha hb
    subst a
    subst b
    exact Commute.refl _
  have hoddS : ∀ a ∈ ({s} : Set (GL (Fin m ⊕ Fin m) (GaloisField 2 g))), Odd (orderOf a) := by
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
  rcases hcase with rfl | ⟨hne, hpair, hεeq⟩
  ·
    have hadj := hε.2.2.2.1
    by_cases hdeg2 : blockDegree (Algebra.adjoin (GaloisField 2 g)
        (Units.val '' ({s} : Set (GL (Fin m ⊕ Fin m) (GaloisField 2 g))))) e < 2
    · exact rckIIp_PSp_selfDual_one hg φ hφk _ hS he hadj hdeg2 hJ'comp hoddJ' hA8'
    · by_cases hdeg4 : blockDegree (Algebra.adjoin (GaloisField 2 g)
          (Units.val '' ({s} : Set (GL (Fin m ⊕ Fin m) (GaloisField 2 g))))) e < 4
      · exact rckIIp_PSp_selfDual_two hg φ hφk _ hSU hS hoddS he hadj (by omega) hdeg4 hJ'comp
          hoddJ' hA8'
      · exact rckIIp_PSp_fieldExt hg φ hφk _ hSU hS hoddS hε hJ'comp he heε
          (Or.inl ⟨rfl, by omega⟩) hA8'
  ·
    by_cases hdeg2 : blockDegree (Algebra.adjoin (GaloisField 2 g)
        (Units.val '' ({s} : Set (GL (Fin m ⊕ Fin m) (GaloisField 2 g))))) e < 2
    · exact rckIIp_PSp_dualPair_one hg φ hφk s hs he hpair hεeq hdeg2 hJ'comp hoddJ' hA8'
    · exact rckIIp_PSp_fieldExt hg φ hφk _ hSU hS hoddS hε hJ'comp he heε
        (Or.inr ⟨hne, by omega⟩) hA8'

end CFSG.StandardType.RCKC1
