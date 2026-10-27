module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFAt
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeF1PSU
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeBlockPSUSelfDual
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeBlockPSUDualPair
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeBlockPSUFEPair
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeBlockPSUFESelf
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePSULowRank
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1Helpers
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFIIPSULow

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

private theorem rckRPfsu_singleton {n g : ℕ} {s : GL (Fin n) (GaloisField 2 (2 * (g + 1)))}
    (hsU : Unitary.conjTr
          (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
          (s : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) * Unitary.antidiag n *
        (s : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) = Unitary.antidiag n)
    (hsodd : Odd (orderOf s)) :
    (∀ a ∈ ({s} : Set (GL (Fin n) (GaloisField 2 (2 * (g + 1))))),
      Unitary.conjTr
          (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
          (a : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) * Unitary.antidiag n *
        (a : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) = Unitary.antidiag n) ∧
    (∀ a ∈ ({s} : Set (GL (Fin n) (GaloisField 2 (2 * (g + 1))))),
      ∀ b ∈ ({s} : Set (GL (Fin n) (GaloisField 2 (2 * (g + 1))))), Commute a b) ∧
    ∀ a ∈ ({s} : Set (GL (Fin n) (GaloisField 2 (2 * (g + 1))))), Odd (orderOf a) := by
  refine ⟨fun a ha => ?_, fun a ha b hb => ?_, fun a ha => ?_⟩
  · rw [Set.mem_singleton_iff.mp ha]
    exact hsU
  · rw [Set.mem_singleton_iff.mp ha, Set.mem_singleton_iff.mp hb]
  · rw [Set.mem_singleton_iff.mp ha]
    exact hsodd

private theorem rckRPfsu_flaggedModel
    {n g : ℕ} {s : GL (Fin n) (GaloisField 2 (2 * (g + 1)))}
    (hsU : Unitary.conjTr
          (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
          (s : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) * Unitary.antidiag n *
        (s : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) = Unitary.antidiag n)
    (hsodd : Odd (orderOf s))
    {ε e : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom (Unitary.antidiag n)
      (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' {s})) ε)
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' {s})) e)
    (hsplit : e = ε ∨ (e ≠ ε ∧ formAdj (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom (Unitary.antidiag n) e ≠ e ∧
      ε = e + formAdj (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom (Unitary.antidiag n) e))
    {J' : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
      (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n)}
    (hJ' : IsComponentOf J'
      ⁅glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype {s} ε,
      glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype {s} ε⁆) :
    RCKRPFlaggedModel
      (Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype
      none J' := by
  obtain ⟨hSU, hS, hoddS⟩ := rckRPfsu_singleton hsU hsodd
  rcases hsplit with rfl | ⟨-, hpair, rfl⟩
  · have hadj := hε.2.2.2.1
    rcases lt_or_ge
        (blockDegree (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' {s})) e) 2
      with h1 | h2
    · exact rckRP_flaggedModel_PSU_selfDual n g {s} hS he hadj h1 hJ'
    · exact rckRP_flaggedModel_PSU_fieldExtSelf n g {s} hSU hS hoddS he hadj h2 hJ'
  · rcases lt_or_ge
        (blockDegree (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' {s})) e) 2
      with h1 | h2
    · exact rckRP_flaggedModel_PSU_dualPair n g {s} hSU hS he hpair h1 hJ'
    · exact rckRP_flaggedModel_PSU_fieldExtPair n g {s} hSU hS hoddS hε he hpair h2 hJ'

theorem rckLemmaFAt_PSU
    (hIRG : RCKIntrinsicRoot) : RCKLemmaFAt .PSU := by
  intro X _ _ p K J R Rm B d hp hp2 hBab hdB hBK _hBJ _hrank hmodel _hodd hcomp _hA6 hRJ _hRmJ
    hroot
  rcases hmodel with ⟨n, g, φ, hg, hφr, hφk, hdiag⟩
  obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
  rcases lt_or_ge n 3 with hn | hn
  · exact rckRP_ggRootPosFlag_PSU_le_two (by omega) hg φ hφr hφk
      (hRJ.trans (hcomp.1.trans inf_le_left)) (rck_rootPosJ_isPGroup hroot)
  obtain ⟨s, hsU, -, hsodd, ε, hε, ⟨e, he, -, hsplit⟩, J', hJ'comp, hJ'map⟩ :=
    rckF1_PSU hp hp2 (hBab.2 d hdB) hn φ hφr hφk (hBK hdB) (hdiag d hdB) hcomp
  have hM := rckRPfsu_flaggedModel hsU hsodd hε he hsplit hJ'comp
  obtain ⟨R', hR'map, hR'flag⟩ :=
    rckRP_glGeoFlag_of_flaggedModel hIRG _ φ hφk hJ'map hcomp.2.2 hroot hM
  exact ggRootPosFlag_of_glGeoFlag_PSU hg φ hφr hφk hR'map hR'flag

private theorem rckRPfsu_modelII
    {n g : ℕ} {s : GL (Fin n) (GaloisField 2 (2 * (g + 1)))}
    (hsU : Unitary.conjTr
          (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
          (s : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) * Unitary.antidiag n *
        (s : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) = Unitary.antidiag n)
    (hsodd : Odd (orderOf s))
    {ε e : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom (Unitary.antidiag n)
      (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' {s})) ε)
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' {s})) e)
    (hsplit : e = ε ∨ (e ≠ ε ∧ formAdj (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom (Unitary.antidiag n) e ≠ e ∧
      ε = e + formAdj (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom (Unitary.antidiag n) e))
    {J' : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
      (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n)}
    (hJ' : IsComponentOf J'
      ⁅glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype {s} ε,
      glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype {s} ε⁆) :
    RCKRPModelII (RCKRPRootSubOf (ggU .PSU n (g + 1))) J' := by
  obtain ⟨hSU, hS, hoddS⟩ := rckRPfsu_singleton hsU hsodd
  rcases hsplit with rfl | ⟨-, hpair, rfl⟩
  · have hadj := hε.2.2.2.1
    rcases lt_or_ge
        (blockDegree (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' {s})) e) 2
      with h1 | h2
    · exact rckRP_modelII_PSU_selfDual n g {s} hS he hadj h1 hJ'
    · exact rckRP_modelII_of_big _
        (rckRP_modelBig_PSU_fieldExtSelf n g {s} hSU hS hoddS he hadj h2 hJ')
  · rcases lt_or_ge
        (blockDegree (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' {s})) e) 2
      with h1 | h2
    · exact rckRP_modelII_of_big _ (rckRP_modelBig_PSU_dualPair n g {s} hSU hS he hpair h1 hJ')
    · exact rckRP_modelII_of_big _
        (rckRP_modelBig_PSU_fieldExtPair n g {s} hSU hS hoddS hε he hpair h2 hJ')

theorem rckLemmaFIIAt_PSU
    (hIRG : RCKIntrinsicRoot) : RCKLemmaFIIAt .PSU := by
  intro X _ _ p K J R Rm B d hp hp2 hBab hdB hBK _hBJ _hrank hmodel _hodd hcomp _hrow _hA6 _hRJ
    _hRmJ hroot hR2
  rcases hmodel with ⟨n, g, φ, hg, hφr, hφk, hdiag⟩
  obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
  rcases lt_or_ge n 3 with hn | hn
  · have hJK := rckRP_eq_of_PSU_le_two (by omega) φ hφr hφk (hBK hdB) (hdiag d hdB) hcomp
    rw [hJK] at hroot
    exact ggRootPosNbr_of_rootPosJ hroot
  obtain ⟨s, hsU, -, hsodd, ε, hε, ⟨e, he, -, hsplit⟩, J', hJ'comp, hJ'map⟩ :=
    rckF1_PSU hp hp2 (hBab.2 d hdB) hn φ hφr hφk (hBK hdB) (hdiag d hdB) hcomp
  have hM := rckRPfsu_modelII hsU hsodd hε he hsplit hJ'comp
  obtain ⟨R', hR'map, hR'⟩ := rckRP_exists_of_modelII hIRG φ hφk hJ'map hcomp.2.2 hroot hR2 hM
  exact ggRootPosNbr_of_rootSubOf (t := .PSU) (by simp [GGPosTag]) (Or.inr (Or.inr (Or.inl rfl)))
    hg φ hφr hφk hR'map hR'

end CFSG.StandardType.RCKRP
