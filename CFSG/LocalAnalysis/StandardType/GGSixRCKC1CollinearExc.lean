module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1CollinearLong
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LemmaHNbr
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1ShortCore
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongF4
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongE6
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongE7
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongE8
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongTwE6

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
  CFSG.StandardType.LieKnownR2.Short CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
open CFSG.ClassicalInvolution.ModelFacts (isIrreducible_F4 isIrreducible_E6 isIrreducible_E7
  isIrreducible_E8)

theorem rckCollinearVia_F4_long
    {m g : ℕ} (hg : 1 ≤ g) {β : Fin (ggU .F4 m g).D.rank → ℤ}
    (hβ : β ∈ (ggU .F4 m g).D.roots) (hl : GGLongRoot (ggU .F4 m g).D β) :
    RCKCollinearVia (ggU .F4 m g) β := by
  have ht : GGPosTag .F4 := by simp [GGPosTag]
  have hfin : Finite (ggU .F4 m g).K := rckXF_finite_ggU ht hg
  exact @rckCollinearVia_of_long (ggU .F4 m g) hfin _ _
    (f4_isCTGroupDatum_exact (GaloisField 2 g))
    (f4_steinbergExtras_exact (GaloisField 2 g))
    isIrreducible_F4 rfl
    (rckGL1_centerPPrime_ggU ht hg (by simp))
    β hl (isPGroup_two_rootGroup_F4 (GaloisField 2 g) hβ)
    (fun u => (coreFour_F4_long hl u rfl rfl).1)

theorem rckCollinearVia_E6
    {m g : ℕ} (hg : 1 ≤ g) {β : Fin (ggU .E6 m g).D.rank → ℤ}
    (hβ : β ∈ (ggU .E6 m g).D.roots) (hl : GGLongRoot (ggU .E6 m g).D β) :
    RCKCollinearVia (ggU .E6 m g) β := by
  have ht : GGPosTag .E6 := by simp [GGPosTag]
  have hfin : Finite (ggU .E6 m g).K := rckXF_finite_ggU ht hg
  exact @rckCollinearVia_of_long (ggU .E6 m g) hfin _ _
    (e6Datum_isCTGroupDatum (GaloisField 2 g))
    (e6Datum_steinbergExtras (GaloisField 2 g))
    isIrreducible_E6 rfl
    (rckGL1_centerPPrime_ggU ht hg (by simp))
    β hl (isPGroup_two_range_of_charTwo (e6Data_valid.xHom (GaloisField 2 g) β))
    (fun u => (CFSG.StandardType.LieKnownR2.E6.coreFour_E6 hβ u rfl rfl).1)

theorem rckCollinearVia_E7
    {m g : ℕ} (hg : 1 ≤ g) {β : Fin (ggU .E7 m g).D.rank → ℤ}
    (hβ : β ∈ (ggU .E7 m g).D.roots) (hl : GGLongRoot (ggU .E7 m g).D β) :
    RCKCollinearVia (ggU .E7 m g) β := by
  have ht : GGPosTag .E7 := by simp [GGPosTag]
  have hfin : Finite (ggU .E7 m g).K := rckXF_finite_ggU ht hg
  exact @rckCollinearVia_of_long (ggU .E7 m g) hfin _ _
    (e7Datum_isCTGroupDatum (GaloisField 2 g))
    (e7Datum_steinbergExtras (GaloisField 2 g))
    isIrreducible_E7 rfl
    (rckGL1_centerPPrime_ggU ht hg (by simp))
    β hl (isPGroup_two_range_of_charTwo (e7Data_valid.xHom (GaloisField 2 g) β))
    (fun u => (CFSG.StandardType.LieKnownR2.E7.coreFour_E7 hβ u rfl rfl).1)

theorem rckCollinearVia_E8
    {m g : ℕ} (hg : 1 ≤ g) {β : Fin (ggU .E8 m g).D.rank → ℤ}
    (hβ : β ∈ (ggU .E8 m g).D.roots) (hl : GGLongRoot (ggU .E8 m g).D β) :
    RCKCollinearVia (ggU .E8 m g) β := by
  have ht : GGPosTag .E8 := by simp [GGPosTag]
  have hfin : Finite (ggU .E8 m g).K := rckXF_finite_ggU ht hg
  exact @rckCollinearVia_of_long (ggU .E8 m g) hfin _ _
    (CFSG.LieType.Steinberg.Adjoint.adjDatum_isCTGroupDatum
      (CFSG.LieType.Chevalley.rootOperatorFamily .E8) (GaloisField 2 g))
    (CFSG.LieType.Steinberg.Adjoint.e8_steinbergExtras (GaloisField 2 g))
    isIrreducible_E8 rfl
    (rckGL1_centerPPrime_ggU ht hg (by simp))
    β hl (CFSG.StandardType.LieKnownR2.Exc.isPGroup_two_rootGroup_adj .E8
      (GaloisField 2 g) hβ)
    (fun u => (CFSG.StandardType.LieKnownR2.E8.coreFour_E8 hβ u rfl rfl).1)

theorem rckCollinearVia_twistedE6_long
    {m g : ℕ} (hg : 1 ≤ g) {β : Fin (ggU .twistedE6 m g).D.rank → ℤ}
    (hβ : β ∈ (ggU .twistedE6 m g).D.roots) (hl : GGLongRoot (ggU .twistedE6 m g).D β) :
    RCKCollinearVia (ggU .twistedE6 m g) β := by
  have ht : GGPosTag .twistedE6 := by simp [GGPosTag]
  have hfin : Finite (ggU .twistedE6 m g).K := rckXF_finite_ggU ht hg
  exact @rckCollinearVia_of_long (ggU .twistedE6 m g) hfin _ _
    (twistedDatum_isCTGroupDatum (frobQ 2 g) (frobQ_frobQ 2 g hg)
      (iSup_twistedDatum_rootGroup (frobQ 2 g) (frobQ_frobQ 2 g hg)))
    (twistedDatum_steinbergExtras (frobQ 2 g) (frobQ_frobQ 2 g hg))
    isIrreducible_F4 rfl
    (rckGL1_centerPPrime_ggU ht hg (by simp))
    β hl (isPGroup_two_twistedRootGroup (frobQ 2 g) hβ)
    (fun u => (coreFour_twistedE6_long hg hl u rfl rfl).1)

end CFSG.StandardType.RCKC1
