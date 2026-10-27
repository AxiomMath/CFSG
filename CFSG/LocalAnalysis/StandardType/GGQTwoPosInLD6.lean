module

public import CFSG.LocalAnalysis.StandardType.GGQTwoD6NormForm
public import CFSG.LocalAnalysis.StandardType.GGQTwoD6FrameLoc
public import CFSG.LocalAnalysis.StandardType.GGQTwoD6Group2
public import Certificates.Certificate712502
public import CFSG.LocalAnalysis.StandardType.GGQTwoK1OfI1
public import CFSG.LocalAnalysis.StandardType.GGQTwoAjSetting
public import CFSG.LocalAnalysis.StandardType.GGQTwoPosInLCells
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType.QTwoD6

open CFSG.StandardType CFSG.Assembly CFSG.StandardType.QTwoLin

theorem ggQ2_posInL_lineD6_of_linear (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) (hxm : GGQTwoXInLNbrModelInput) (hlin : GGQ2D6LinearCell) :
    GGQ2GammaNbrPosInLOn GGQ2SelD6 := by
  intro G _ _ p B Bs x L D J hS hp hI hxL _ y K hnb _hnr _hM hsel u hu
  subst hp
  obtain ⟨N, b, hb, hJ, _hpos, hnorm⟩ := hsel
  have hK1 : GGQTwoK1 3 B Bs x D J := ggQ2_K1_of_I1 hLB hP hS.1 hI
  have hConfig := hS.1.1
  have hStd : LargeEvenStdSub 3 B x L D J := hConfig.2.2
  have hStdPre : LargeEvenStdSubPre 3 B x L D J := hStd.1
  have hDleB : D ≤ B := hStdPre.1
  have hBBs : B ≤ Bs := hConfig.2.1.1
  have hDBs : D ≤ Bs := hDleB.trans hBBs
  have hxmem : x ∈ D := by
    rw [hnb.2.1]
    exact Subgroup.subset_closure (Set.mem_insert x {y})
  have hymem : y ∈ D := by
    rw [hnb.2.1]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem x rfl)
  have hxBs : x ∈ Bs := hDBs hxmem
  have hyBs : y ∈ Bs := hDBs hymem
  obtain ⟨Fr⟩ := ggQ2_d6_frame hnb N b hb hK1 hyBs
  obtain ⟨y', K', _hnb', ⟨M'⟩⟩ := hxm G 3 B Bs x L D J hS hI hxL
  let A : Subgroup (V7 ≃ₗ[ZMod 3] V7) := linA N Fr.F
  let Aℓ : Subgroup (V7 ≃ₗ[ZMod 3] V7) := linAL L N Fr.F
  let ell : V7 := ggEll N Fr.F hxBs
  have hTF : TransvectionFree A := ggQ2d6_transvectionFree hS Fr
  have hW : W6 ≤ A := ggQ2d6_W6_le Fr
  have hNF : ∀ φ ∈ A, φ e0 ∈ Submodule.span (ZMod 3) {e0} →
      ∃ w ∈ W6, ∃ c : ZMod 3, c ≠ 0 ∧ ∃ π : Fin 6 ≃ Fin 6,
        (π = Equiv.refl _ ∨ π = swapD6) ∧ ∀ i, φ (hvec i) = c • w (hvec (π i)) :=
    ggQ2d6_normForm hS hnb (hb := hb) hK1 Fr hnorm
  have hell : ell ∈ Dplane := ggQ2_d6_ell_mem_Dplane hS hJ Fr hxBs
  have hell0 : ell ∉ Submodule.span (ZMod 3) {e0} := ggQ2_d6_ell_not_mem hS hnb Fr hxBs
  have hALL : Aℓ ≤ A := ggQ2d6_linAL_le_linA Fr
  have hJ6 : J6 ≤ Aℓ := ggQ2d6_J6_le_linAL hS hJ Fr
  have hfix : ∀ φ ∈ Aℓ, φ ell = ell := ggQ2d6_AL_fix hS M' Fr hxBs
  have hmove : ∃ φ ∈ Aℓ, φ e0 ≠ e0 := ggQ2d6_AL_moves hS hnb M' Fr
  have hgen : Aℓ = Subgroup.closure {g | g ∈ Aℓ ∧ IsReflLin g} := ggQ2d6_AL_reflGen hS M' Fr
  have hcard : 1440 < Nat.card Aℓ := ggQ2d6_card_AL hS hnb M' (hb := hb) hJ Fr
  intro φ hφ hφu
  have hfixy : φ ⟨y, hyBs⟩ ∈ Subgroup.zpowers (⟨y, hyBs⟩ : ↥Bs) :=
    ggQ2d6_g1_stable hyBs hu hφu
  have hφlin : ggCoord N Fr.F φ e0 ∈ Submodule.span (ZMod 3) {e0} :=
    ggQ2d6_phi_e0 Fr φ hfixy
  have hφin : ggCoord N Fr.F φ ∈ A := Subgroup.mem_map.mpr ⟨φ, hφ, rfl⟩
  obtain ⟨ψ, hψmem, hψconcl⟩ :=
    hlin A ell Aℓ hTF hW hNF hell hell0 hALL hJ6 hfix hmove hgen hcard
      (ggCoord N Fr.F φ) hφin hφlin
  have hle : W6 ⊔ Aℓ ≤ (ggAutomizer (L ⊔ K) Bs).map (ggCoord N Fr.F) :=
    ggQ2d6_W6_sup_linAL_le_map hS Fr
  have hψmem' : ψ ∈ (ggAutomizer (L ⊔ K) Bs).map (ggCoord N Fr.F) := hle hψmem
  obtain ⟨ψg, hψgmem, hψgeq⟩ := Subgroup.mem_map.mp hψmem'
  have hAJ : ggAutomizer J Bs ≠ ⊥ := ggQ2_ajOfSetting hP h5 hS
  have hHle : L ⊔ K ≤ ggG0 3 B x L D J :=
    sup_le (le_ggG0_left 3 B x L D J) (le_ggG0_of_ggNbr hnb)
  refine ggQ2_finish_of_le hLB hP hS hAJ hK1 hnb hHle hφ hψgmem ?_
  intro d hdD
  have hdDp : Fr.F (N.model (Additive.ofMul d)) ∈ Dplane :=
    (ggQ2d6_mem_D_iff Fr hnb.2.1 hxBs hell hell0 d).mp hdD
  have hψd : ψ (ggCoord N Fr.F φ (Fr.F (N.model (Additive.ofMul d)))) ∈ Dplane :=
    hψconcl _ hdDp
  refine (ggQ2d6_mem_D_iff Fr hnb.2.1 hxBs hell hell0 ((ψg * φ) d)).mpr ?_
  have hcoord : ggCoord N Fr.F (ψg * φ) (Fr.F (N.model (Additive.ofMul d))) =
      Fr.F (ggLin (p := 3) N.model (ψg * φ) (N.model (Additive.ofMul d))) := by
    rw [ggQ2_d6_coord_apply, Fr.F.symm_apply_apply]
  rw [← ggLin_apply_ofMul (p := 3) N.model (ψg * φ) d, ← hcoord, map_mul, hψgeq,
    LinearEquiv.mul_apply]
  exact hψd

theorem ggQ2_posInL_lineD6 (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) (h5 : GGQTwoCentralizerInput) (hxm : GGQTwoXInLNbrModelInput) :
    GGQ2GammaNbrPosInLOn GGQ2SelD6 :=
  ggQ2_posInL_lineD6_of_linear hLB hP h5 hxm Certificates.certificate712502

end CFSG.StandardType.QTwoD6

end
