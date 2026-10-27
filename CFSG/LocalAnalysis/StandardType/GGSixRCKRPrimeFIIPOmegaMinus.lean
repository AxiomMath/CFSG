module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFPOmegaMinus
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoPOmegaMinusRoot
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1ShortOmMAux

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

@[expose] def RCKLemmaFIIAtPOmegaMinusLow :
    Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) (K J R Rm B : Subgroup X) (d : X),
    p.Prime → p ≠ 2 → IsElemAbelian p B → d ∈ B →
    B ≤ Subgroup.normalizer (K : Set X) → B ≤ Subgroup.normalizer (J : Set X) →
    p ^ 2 * Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set X)) ≤ Nat.card B →
    (∃ (m g : ℕ) (φ : (ggU .POmegaMinus m g).K →* X), m < 4 ∧ 1 ≤ g ∧ φ.range = K ∧
      φ.ker ≤ Subgroup.center (ggU .POmegaMinus m g).K ∧
      ∀ b ∈ B, GGPsiInnerDiag (ggU .POmegaMinus m g).D φ b) →
    Odd (Nat.card (Subgroup.center ↥K)) →
    IsComponentOf J (K ⊓ Subgroup.centralizer {d}) → GGSixRCKJRow .II J →
    IsEmpty (↥J ≃* alternatingGroup (Fin 6)) →
    R ≤ J → Rm ≤ J → GGRootPosJ J R Rm → Nat.card R = 2 → GGRootPosNbr K R

theorem rckLemmaFIIAt_POmegaMinus_of
    (hIRG : RCKIntrinsicRoot)
    (hdp : RCKM3POmegaMinusDualPairHigh) (hsd : RCKM3POmegaMinusSelfDualHigh)
    (hlow : RCKLemmaFIIAtPOmegaMinusLow) : RCKLemmaFIIAt .POmegaMinus := by
  intro X _ _ p K J R Rm B d hp hp2 hBab hdB hBK hBJ hrank hmodel hodd hcomp hrow hA6 hRJ hRmJ hroot
    hR2
  obtain ⟨m, g, φ, hg, hφr, hφk, hdiag⟩ := hmodel
  by_cases hm : 4 ≤ m
  swap
  · exact hlow X p K J R Rm B d hp hp2 hBab hdB hBK hBJ hrank
      ⟨m, g, φ, by omega, hg, hφr, hφk, hdiag⟩ hodd hcomp hrow hA6 hRJ hRmJ hroot hR2
  have hirr : ∀ s : GaloisField 2 g,
      s ^ 2 + (minusCoeffs 2 g).1 * s + (minusCoeffs 2 g).2 ≠ 0 := minusCoeffs_irr 2 g
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hφk.trans (CFSG.StandardType.PsiDiag.SpinM.center_eq_bot hirr hm).le
  obtain ⟨s, hs, hsodd, ε, hε, J', hJ'comp, hJ'map⟩ :=
    rckF1_POmegaMinus hp hp2 (hBab.2 d hdB) hirr hm φ hφr hφk (hdiag d hdB) hcomp
  have hJq : CFSG.Assembly.IsQuasisimple ↥J := hcomp.2.2
  have hJq' := hJq
  rw [← hJ'map] at hJq'
  have hpos := hroot
  rw [← hJ'map] at hpos
  rcases rckM3_POmegaMinus_dispatch hdp hsd hp hp2 hBab hdB hrank hg hm φ hφk hdiag hs hsodd
      hε hJ'comp hJ'map with hsieg | hfl
  ·
    obtain ⟨t', m', g', ι, β₀, hnorm, ht, hβ₀, hlong, hrange, hcent, a₁, a₂, b₁, b₂, hQ, hb1,
      hb2, hb12, hsig⟩ := hsieg
    obtain ⟨c, hc⟩ := rckRP_exists_rootSub_eq_of_long hIRG φ hφk hJ'map hJq hroot ι hnorm
      (rckRP_not_PSp_two_or_F4_of_tag ht) hrange hcent hlong
    obtain ⟨β, hβroot, hβlong, u, hu, -⟩ :=
      exists_conj_rootGroup_eq_siegelGroup_POmegaMinus m hirr hm a₁ a₂ b₁ b₂ hQ hb1 hb2 hb12
    have hspin : Function.Injective (Spin.spinAction (Spin.quadMinus m (GaloisField 2 g)
        (minusCoeffs 2 g).1 (minusCoeffs 2 g).2)) :=
      rckSOmM_spinAction_injective hirr
    have hroots : ((ggU t' m' g').D.rootGroup β₀).map ι =
        ((Spin.Twisted.minusDatum m hirr).rootGroup β).map (MulAut.conj u).toMonoidHom :=
      Subgroup.map_injective hspin (hsig.trans hu.symm)
    have hconj : ((((ggU t' m' g').D.rootGroup β₀).map (MulAut.conj c).toMonoidHom).map ι) =
        (((ggU t' m' g').D.rootGroup β₀).map ι).map (MulAut.conj (ι c)).toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply]
    refine Or.inl ⟨.POmegaMinus, m, g, β, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), hg,
      hβroot, Or.inl hβlong, φ, hφr, hφk, ι c * u, ?_⟩
    rw [← hc]
    change _ = (((Spin.Twisted.minusDatum m hirr).rootGroup β).map
      (MulAut.conj (ι c * u)).toMonoidHom).map φ
    rw [← CFSG.GroupTheory.map_conj_map_conj, ← hroots, ← hconj]
    rfl
  ·
    have h4 := rckFII_card_le_of_spinFlagModel hIRG φ hφinj hfl hJq' hpos
    omega

end CFSG.StandardType.RCKRP
