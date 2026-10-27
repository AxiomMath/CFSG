module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFAt
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRG
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeF1PSL
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFIIDeg
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFIITransv

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

theorem rckLemmaFIIAt_PSL
    (hIRG : RCKIntrinsicRoot) : RCKLemmaFIIAt .PSL := by
  intro X _ _ p K J R Rm B d hp hp2 hBab hdB hBK hBJ hrank hmodel hodd hcomp hrow _hA6 hRJ hRmJ
    hroot hR2
  rcases hmodel with ⟨m, g, φ, hg, hφr, hφk, hdiag⟩
  have hm0 : m ≠ 0 := by
    rintro rfl
    haveI : Subsingleton (ggU .PSL 0 g).K := by
      show Subsingleton (Matrix.SpecialLinearGroup (Fin 1) (ZMod 2))
      infer_instance
    haveI : Subsingleton ↥(φ.range) :=
      (MonoidHom.rangeRestrict_surjective φ).subsingleton
    have hrange_bot : φ.range = ⊥ := Subgroup.eq_bot_of_subsingleton (φ.range)
    have hKbot : K = ⊥ := by rw [← hφr, hrange_bot]
    have hle : J ≤ (⊥ : Subgroup X) := by
      calc J ≤ K ⊓ Subgroup.centralizer ({d} : Set X) := hcomp.1
        _ = ⊥ := by rw [hKbot, bot_inf_eq]
    exact (Subgroup.nontrivial_iff_ne_bot J).mp
      (CFSG.ComponentClassification.Quasisimple.nontrivial hcomp.2.2) (le_bot_iff.mp hle)
  obtain ⟨m', rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hm0
  obtain ⟨s, _hs, hsodd, e, he, J', hJ'comp, hJ'map⟩ :=
    rckF1_PSL (m := m') (g := g) hp hp2 (hBab.2 d hdB) hg φ hφr hφk (hBK hdB)
      (hdiag d hdB) hcomp
  have hS : ∀ a ∈ ({s} : Set (GL (Fin (m' + 1)) (GaloisField 2 g))),
      ∀ b ∈ ({s} : Set (GL (Fin (m' + 1)) (GaloisField 2 g))), Commute a b := by
    intro a ha b hb
    rw [Set.mem_singleton_iff] at ha hb
    subst a
    subst b
    exact Commute.refl s
  have hoddS : ∀ a ∈ ({s} : Set (GL (Fin (m' + 1)) (GaloisField 2 g))), Odd (orderOf a) := by
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst a
    exact hsodd
  have hR' : R ≤ J'.map φ := by rw [hJ'map]; exact hRJ
  have hRm' : Rm ≤ J'.map φ := by rw [hJ'map]; exact hRmJ
  have hpos' : GGRootPosJ (J'.map φ) R Rm := by rw [hJ'map]; exact hroot
  obtain ⟨hg1, hdeg⟩ :=
    rckFII_PSL_degOne hIRG hg φ hφk {s} hS hoddS he hJ'comp hR' hRm' hpos' hR2
  subst g
  obtain ⟨β, hβroot, hlong, hvia⟩ :=
    rckFII_PSL_transv hIRG φ hφk {s} hS hoddS he hJ'comp hdeg hR' hRm' hpos'
  rw [hφr] at hvia
  exact Or.inl ⟨.PSL, m' + 1, 1, β, Or.inl rfl, le_refl 1, hβroot, Or.inl hlong, hvia⟩

end CFSG.StandardType.RCKRP
