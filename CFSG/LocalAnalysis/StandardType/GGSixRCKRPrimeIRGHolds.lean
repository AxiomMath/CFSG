module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGTransfer
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGAutSp
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGAutE78
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGAutF4
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGAutA1
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGAutPSL
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGAutPSU
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGAutOmP
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGAutOmF
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGAutOmM
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGAutE6
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGAutTE6
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGTyNorm
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGTyEq
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGTriSame

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag StatedLieAdmissible)

theorem irgRootPairAut_all
    {t : StatedLieTag} {n g : ℕ} (ht : GGPosTag t) (hadm : StatedLieAdmissible t n 2 g) :
    IRGRootPairAut t n g := by
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hn : 2 ≤ n := hadm.2.2.1
    rcases Nat.lt_or_ge n 3 with h | h
    · obtain rfl : n = 2 := by omega
      exact irgRootPairAut_PSL_two hadm
    · exact irgRootPairAut_PSL h hadm
  · exact irgRootPairAut_PSU hadm
  · have hn : 2 ≤ n := hadm.2.2.1
    rcases Nat.lt_or_ge n 3 with h | h
    · obtain rfl : n = 2 := by omega
      exact irgRootPairAut_PSp_two hadm
    · exact irgRootPairAut_PSp h hadm
  · have hn : 4 ≤ n := hadm.2.2
    rcases Nat.lt_or_ge n 5 with h | h
    · obtain rfl : n = 4 := by omega
      exact irgRootPairAut_POmegaPlus_four hadm
    · exact irgRootPairAut_POmegaPlus h hadm
  · exact irgRootPairAut_POmegaMinus hadm
  · obtain rfl : n = 0 := hadm.2.2
    exact irgRootPairAut_F4 hadm
  · obtain rfl : n = 0 := hadm.2.2
    exact irgRootPairAut_E6 hadm
  · obtain rfl : n = 0 := hadm.2.2
    exact irgRootPairAut_E7 hadm
  · obtain rfl : n = 0 := hadm.2.2
    exact irgRootPairAut_E8 hadm
  · obtain rfl : n = 0 := hadm.2.2
    exact irgRootPairAut_twistedE6 hadm

theorem irg_classical_conjunct
    {X : Type} [Group X] (J R Rm : Subgroup X) (hqs : CFSG.Assembly.IsQuasisimple ↥J)
    (hpos : GGRootPosJ J R Rm) :
    ∀ (t : StatedLieTag) (n g : ℕ) (φ : (ggU t n g).K →* X), RCKNormalizedModel t n g →
      φ.range = J → φ.ker ≤ Subgroup.center (ggU t n g).K →
      ∃ (β : Fin (ggU t n g).D.rank → ℤ) (u : (ggU t n g).K), β ∈ (ggU t n g).D.roots ∧
        (GGLongRoot (ggU t n g).D β ∨
          (((t = .PSp ∧ n = 2) ∨ t = .F4) ∧ 2 • β ∉ (ggU t n g).D.roots)) ∧
        R = ggRootSub (ggU t n g).D φ β u ∧ Rm = ggRootSub (ggU t n g).D φ (-β) u := by
  intro t n g φ hn hr hk
  rcases hpos with hleft | ⟨F', _, _, σ', g', β', hT', hl', hpair⟩
  · obtain ⟨t'', m'', g'', φ'', γ, u'', hn'', hr'', hk'', hγ, hlγ, hR, hRm⟩ :=
      irg_normalize_hyp hqs hleft
    obtain ⟨rfl, rfl, rfl⟩ := irg_type_eq hqs hn hn'' φ φ'' hr hr'' hk hk''
    have hM := irgRootPairAut_all hn.1 hn.2
    obtain ⟨β, hβ, u, hR', hRm'⟩ :=
      irg_transfer hn.1 hn.2 hM φ φ'' (hr''.trans hr.symm) hk hk'' hγ hlγ u''
    exact ⟨β, u, hβ.1, hβ.2, hR.trans hR', hRm.trans hRm'⟩
  · obtain ⟨φ', hr', hk', u', -, -⟩ := hpair
    exact (irg_tri_not_classical hqs hn φ hr hk hT' φ' hr' hk').elim

theorem irg_tri_not_left
    {X : Type} [Group X] {J R Rm : Subgroup X} (hqs : CFSG.Assembly.IsQuasisimple ↥J)
    (hleft : ∃ (t' : StatedLieTag) (m g : ℕ) (β : Fin (ggU t' m g).D.rank → ℤ), GGPosTag t' ∧
      1 ≤ g ∧ GGLongRoot (ggU t' m g).D β ∧ GGRootPairVia (ggU t' m g) J R Rm β)
    {F : Type} [Field F] [Finite F] {σ : F →+* F} {g : ℕ} (hT : TriField F σ g)
    (φ : (triD4Universal F σ).K →* X) (hr : φ.range = J)
    (hk : φ.ker ≤ Subgroup.center (triD4Universal F σ).K) : False := by
  obtain ⟨t'', m'', g'', φ'', γ, u'', hn'', hr'', hk'', -⟩ := irg_normalize_hyp hqs hleft
  exact irg_tri_not_classical hqs hn'' φ'' hr'' hk'' hT φ hr hk

theorem rckIntrinsicRoot_holds
    : RCKIntrinsicRoot := by
  intro X _ _ J R Rm hqs _ hpos
  refine ⟨irg_classical_conjunct J R Rm hqs hpos, ?_⟩
  intro F _ _ σ g φ hT hr hk
  rcases hpos with hleft | hright
  · exact (irg_tri_not_left hqs hleft hT φ hr hk).elim
  · exact irg_tri_same hqs hright hT φ hr hk

end CFSG.StandardType.RCKRP
