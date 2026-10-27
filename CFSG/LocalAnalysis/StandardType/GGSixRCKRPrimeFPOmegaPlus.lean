module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFAt
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeF1POmegaPlus
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeM3POmegaPlus
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeOmegaFourMinus
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeSpinFlag
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoPOmegaPlusRoot

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

theorem rckFII_nbr_of_spinSiegelModel_POmegaPlus
    (hIRG : RCKIntrinsicRoot)
    {X : Type} [Group X] [Finite X] {k f : ℕ} (φ : (ggU .POmegaPlus (k + 3) f).K →* X)
    (hφ : Function.Injective φ) {J' : Subgroup (ggU .POmegaPlus (k + 3) f).K}
    (hmod : RCKSpinSiegelModel (Spin.quadPlus (k + 3) (GaloisField 2 f)) J')
    (hJq : CFSG.Assembly.IsQuasisimple ↥(J'.map φ)) {R Rm : Subgroup X}
    (hpos : GGRootPosJ (J'.map φ) R Rm) :
    ∃ β : Fin (ggU .POmegaPlus (k + 3) f).D.rank → ℤ,
      β ∈ (ggU .POmegaPlus (k + 3) f).D.roots ∧
      GGLongRoot (ggU .POmegaPlus (k + 3) f).D β ∧
      GGRootVia (ggU .POmegaPlus (k + 3) f) φ.range R β := by
  obtain ⟨t, m, g, ι, β₀, hnorm, ht, hβ₀, hlong₀, hrange, hcent, a₁, a₂, b₁, b₂, hQ, h₁,
    h₂, h₀, hS⟩ := hmod
  let ι' : (ggU t m g).K →* (ggU .POmegaPlus (k + 3) f).K := ι
  have hrange' : ι'.range = J' := hrange
  have hφk : φ.ker ≤ Subgroup.center (ggU .POmegaPlus (k + 3) f).K := by
    rw [(MonoidHom.ker_eq_bot_iff φ).mpr hφ]
    exact bot_le
  obtain ⟨x, hx'⟩ := rckRP_exists_rootSub_eq_of_long hIRG φ hφk rfl hJq hpos ι' hnorm
    (rckRP_not_PSp_two_or_F4_of_tag ht) hrange' hcent hlong₀
  have hx : R = ((((ggU t m g).D.rootGroup β₀).map (MulAut.conj x).toMonoidHom).map ι').map φ :=
    hx'.symm
  obtain ⟨β, hβ, hlongβ, u, hu, -⟩ :=
    exists_conj_rootGroup_eq_siegelGroup_POmegaPlus (k + 3) (GaloisField 2 f) (by omega)
      a₁ a₂ b₁ b₂ hQ h₁ h₂ h₀
  let u' : (ggU .POmegaPlus (k + 3) f).K := u
  have hβ' : β ∈ (ggU .POmegaPlus (k + 3) f).D.roots := hβ
  have hlongβ' : GGLongRoot (ggU .POmegaPlus (k + 3) f).D β := hlongβ
  have hu' : (((ggU .POmegaPlus (k + 3) f).D.rootGroup β).map
        (MulAut.conj u').toMonoidHom).map
        (Spin.spinAction (Spin.quadPlus (k + 3) (GaloisField 2 f))) =
      siegelGroup (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ a₂ := hu
  have hinjA :
      Function.Injective (Spin.spinAction (Spin.quadPlus (k + 3) (GaloisField 2 f))) := by
    have := Spin.isCentral_cliffordAlgebra_quadPlus (GaloisField 2 f) (k + 3)
    exact (MonoidHom.ker_eq_bot_iff _).mp
      (Spin.ker_spinAction_eq_bot_of_isCentral _ (CharP.cast_eq_zero (GaloisField 2 f) 2))
  have hEq : ((ggU t m g).D.rootGroup β₀).map ι' =
      ((ggU .POmegaPlus (k + 3) f).D.rootGroup β).map (MulAut.conj u').toMonoidHom :=
    Subgroup.map_injective hinjA (hS.trans hu'.symm)
  have hconjι : (((ggU t m g).D.rootGroup β₀).map (MulAut.conj x).toMonoidHom).map ι' =
      (((ggU t m g).D.rootGroup β₀).map ι').map (MulAut.conj (ι' x)).toMonoidHom := by
    simp only [Subgroup.map_map]
    congr 1
    ext z
    simp [MulAut.conj_apply]
  have hmerge :
      ((((ggU .POmegaPlus (k + 3) f).D.rootGroup β).map (MulAut.conj u').toMonoidHom).map
          (MulAut.conj (ι' x)).toMonoidHom) =
        ((ggU .POmegaPlus (k + 3) f).D.rootGroup β).map
          (MulAut.conj (ι' x * u')).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext z
    simp [MulAut.conj_apply, mul_assoc]
  have hR : R = ggRootSub (ggU .POmegaPlus (k + 3) f).D φ β (ι' x * u') := by
    rw [hx, hconjι, hEq, hmerge]
    rfl
  exact ⟨β, hβ', hlongβ', φ, rfl, hφk, ι' x * u', hR⟩

theorem rckPOmegaPlus_rank_of_component
    {X : Type} [Group X] {m f : ℕ} {K J : Subgroup X} {d : X}
    (φ : (ggU .POmegaPlus m f).K →* X) (hφr : φ.range = K)
    (hJ : IsComponentOf J (K ⊓ Subgroup.centralizer {d})) : ∃ k, m = k + 3 := by
  by_cases hm : 3 ≤ m
  · exact ⟨m - 3, by omega⟩
  · exfalso
    have hU : ggU .POmegaPlus m f = trivialUniversal := dite_eq_right hm
    have hsub : Subsingleton (ggU .POmegaPlus m f).K := by
      rw [hU]
      change Subsingleton (Matrix.SpecialLinearGroup (Fin 1) (ZMod 2))
      infer_instance
    have hbot : φ.range = ⊥ := by
      refine le_bot_iff.mp ?_
      rintro _ ⟨y, rfl⟩
      exact Subgroup.mem_bot.mpr (by rw [← map_one φ, Subsingleton.elim y 1])
    have hKbot : K = ⊥ := hφr ▸ hbot
    have hJbot : J = ⊥ := by
      refine le_bot_iff.mp ?_
      calc J ≤ K ⊓ Subgroup.centralizer {d} := hJ.1
        _ ≤ K := inf_le_left
        _ = ⊥ := hKbot
    have hnt : Nontrivial ↥J := CFSG.ComponentClassification.Quasisimple.nontrivial hJ.2.2
    exact (Subgroup.nontrivial_iff_ne_bot J).mp hnt hJbot

theorem rckLemmaFAt_POmegaPlus
    (hIRG : RCKIntrinsicRoot) : RCKLemmaFAt .POmegaPlus := by
  intro X _ _ p K J R Rm B d hp hp2 hBab hdB hBK hBJ hrank hmodel hodd hcomp hA6 hRJ hRmJ hroot
  rcases hmodel with ⟨m, f, φ, hf, hφr, hφk, hdiag⟩
  obtain ⟨k, rfl⟩ := rckPOmegaPlus_rank_of_component φ hφr hcomp
  have hφinj : Function.Injective φ := by
    have hbot : Subgroup.center (ggU .POmegaPlus (k + 3) f).K = ⊥ :=
      CFSG.StandardType.RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo (by omega)
    exact (MonoidHom.ker_eq_bot_iff φ).mp (le_bot_iff.mp (hφk.trans hbot.le))
  obtain ⟨s, hs, hso, ε, hε, J', hJ'comp, hJ'map⟩ :=
    rckF1_POmegaPlus hp hp2 (hBab.2 d hdB) hf φ hφr hφk (hdiag d hdB) hcomp
  have hpos' : GGRootPosJ (J'.map φ) R Rm := by rw [hJ'map]; exact hroot
  have hJq : CFSG.Assembly.IsQuasisimple ↥(J'.map φ) := by rw [hJ'map]; exact hcomp.2.2
  have hj : Function.Injective (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact Spin.ker_spinMatrix_quadPlus_eq_bot (n := k + 3) (K := GaloisField 2 f)
      (CharP.cast_eq_zero (GaloisField 2 f) 2)
  rcases rckM3_POmegaPlus k f hf _ (by rintro x rfl; exact ⟨s, rfl⟩)
      (by rintro x rfl y rfl; exact Commute.refl _) (by rintro x rfl; exact hso) hε hJ'comp with
    ⟨hprim, hadj, -, hm4⟩ | hsieg | hflag
  · exact (rckF_POmegaPlus_not_omegaFourMinus hp hp2 hBab hdB hrank φ hφk hdiag s hs hprim
      hadj hm4 (hJ'comp.1.trans (Subgroup.commutator_le_self _)) hJ'map).elim
  · have hnd := Spin.nondegenerate_polarBilin_quadPlus (k + 3) (GaloisField 2 f)
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨k + 3, f, hf,
      rckFlagAt_of_spinFlagModel hIRG hj φ hφinj (rckSpinFlagModel_of_siegel hnd hsieg) hJq
        hφr hpos'⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨k + 3, f, hf,
      rckFlagAt_of_spinFlagModel hIRG hj φ hφinj hflag hJq hφr hpos'⟩)))

theorem rckLemmaFIIAt_POmegaPlus
    (hIRG : RCKIntrinsicRoot) : RCKLemmaFIIAt .POmegaPlus := by
  intro X _ _ p K J R Rm B d hp hp2 hBab hdB hBK hBJ hrank hmodel hodd hcomp hrow _hA6 hRJ hRmJ
    hroot hR2
  rcases hmodel with ⟨m, f, φ, hf, hφr, hφk, hdiag⟩
  obtain ⟨k, rfl⟩ := rckPOmegaPlus_rank_of_component φ hφr hcomp
  have hφinj : Function.Injective φ := by
    have hbot : Subgroup.center (ggU .POmegaPlus (k + 3) f).K = ⊥ :=
      CFSG.StandardType.RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo (by omega)
    exact (MonoidHom.ker_eq_bot_iff φ).mp (le_bot_iff.mp (hφk.trans hbot.le))
  obtain ⟨s, hs, hso, ε, hε, J', hJ'comp, hJ'map⟩ :=
    rckF1_POmegaPlus hp hp2 (hBab.2 d hdB) hf φ hφr hφk (hdiag d hdB) hcomp
  have hpos' : GGRootPosJ (J'.map φ) R Rm := by rw [hJ'map]; exact hroot
  have hJq : CFSG.Assembly.IsQuasisimple ↥(J'.map φ) := by rw [hJ'map]; exact hcomp.2.2
  rcases rckM3_POmegaPlus k f hf _ (by rintro x rfl; exact ⟨s, rfl⟩)
      (by rintro x rfl y rfl; exact Commute.refl _) (by rintro x rfl; exact hso) hε hJ'comp with
    ⟨hprim, hadj, -, hm4⟩ | hsieg | hflag
  · exact (rckF_POmegaPlus_not_omegaFourMinus hp hp2 hBab hdB hrank φ hφk hdiag s hs hprim
      hadj hm4 (hJ'comp.1.trans (Subgroup.commutator_le_self _)) hJ'map).elim
  · obtain ⟨β, hβ, hlong, hvia⟩ :=
      rckFII_nbr_of_spinSiegelModel_POmegaPlus hIRG φ hφinj hsieg hJq hpos'
    rw [hφr] at hvia
    exact Or.inl ⟨.POmegaPlus, k + 3, f, β, Or.inr (Or.inr (Or.inr (Or.inl rfl))), hf, hβ,
      Or.inl hlong, hvia⟩
  · have h4 := rckFII_card_le_of_spinFlagModel hIRG φ hφinj hflag hJq hpos'
    omega

end CFSG.StandardType.RCKRP
