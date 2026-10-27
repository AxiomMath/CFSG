module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongE8
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2PosGlue
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortTransport
public import CFSG.LieType.Chevalley.AdjointCenter

public section

namespace CFSG.StandardType.LieKnownR2.E8

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.StandardType.LieKnownR2.OddCenter
open scoped commutatorElement

theorem ggSixLieKnown_of_pos_E8
    (h : GGSixLieKnownPos .E8) : GGSixLieKnown .E8 := by
  intro X _ _ n f ψ p G₀ B₁ D J L x hψ hker hmodel hoddG0 hp hp2 hB₁G₀ hinner hab hcardB hDB
    hcardD hB₁J hB₁centJ hJcomp hoddJ hxD hxne hLG₀ hLcomp hJL hDnotCL hLEM1 hB₁L hLEM2 hA3
    hE6c hA6 hField hN hE
  have hadm : StatedLieAdmissible .E8 n 2 f := hmodel.admissible
  have hoddker : Odd (Nat.card ψ.ker) :=
    Odd.of_dvd_nat
      (odd_card_center_ggU (by decide) hadm)
      (Subgroup.card_dvd_of_le hker)
  obtain ⟨R, Rm, hRJ, hRmJ, hpos, h2, h3⟩ :=
    h X n f ψ p G₀ B₁ D J L x hψ hker hmodel hoddG0 hp hp2 hB₁G₀ hinner hab hcardB hDB hcardD
      hB₁J hB₁centJ hJcomp hoddJ hxD hxne hLG₀ hLcomp hJL hDnotCL hLEM1 hB₁L hLEM2 hA3 hE6c
      hA6 hField hN hE
  obtain ⟨β, hβ, -, u, hR, hRm⟩ := hpos
  have hRleG₀ : R ≤ G₀ := hRJ.trans (hJL.trans hLG₀)
  have hRmap : R = (ggRootSub (ggU .E8 n f).D (MonoidHom.id (ggU .E8 n f).K) β u).map ψ :=
    hR.trans (Short.ggRootSub_eq_map _ _ _ _)
  have hRmmap : Rm =
      (ggRootSub (ggU .E8 n f).D (MonoidHom.id (ggU .E8 n f).K) (-β) u).map ψ :=
    hRm.trans (Short.ggRootSub_eq_map _ _ _ _)
  have hRp : IsPGroup 2 R := by
    rw [hRmap]
    exact (rootGroup_isPGroup_E8 hβ u rfl).map ψ
  have hSne : ggRootSub (ggU .E8 n f).D (MonoidHom.id (ggU .E8 n f).K) β u ≠ ⊥ := by
    intro hbot
    have hroot : (ggU .E8 n f).D.rootGroup β ≠ ⊥ :=
      (CFSG.LieType.Steinberg.Adjoint.e8_steinbergExtras (GaloisField 2 f)).ne_bot β hβ
    apply hroot
    rw [ggRootSub] at hbot
    simp only [Subgroup.map_id] at hbot
    exact (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj u).injective).mp hbot
  have hZ : Subgroup.center (ggU .E8 n f).K = ⊥ := by
    change Subgroup.center (CFSG.Blueprint.Chevalley.adjointGroup .E8 (GaloisField 2 f)) = ⊥
    exact CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  have hinj : Function.Injective ψ :=
    (MonoidHom.ker_eq_bot_iff ψ).mp (le_bot_iff.mp (hker.trans (le_of_eq hZ)))
  have hRne : R ≠ ⊥ := by
    rw [hRmap]
    intro hb
    exact hSne ((Subgroup.map_eq_bot_iff_of_injective _ hinj).mp hb)
  have hbase : pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X)) ⊔ (R ⊔ Rm) = G₀ := by
    have h1 := Short.itemOne_of_core hker hoddker (rootGroup_isPGroup_E8 hβ u rfl)
      (coreOne_E8 hβ u rfl rfl rfl)
    rw [hψ, ← hRmap, ← hRmmap] at h1
    exact h1
  have hRle_pcore : R ≤ pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X)) :=
    GGRootNorm.le_pCoreOf_of_normalized
      (fun r hr => ⟨hRleG₀ hr, Subgroup.le_normalizer hr⟩)
      hRp
      (Subgroup.le_normalizer_iff.mp inf_le_right)
  have hitem1 : pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X)) ⊔ Rm = G₀ := by
    rw [← sup_assoc, sup_eq_left.mpr hRle_pcore] at hbase
    exact hbase
  have hcore := coreFour_E8 hβ u rfl rfl
  have h4 := Short.itemFour_of_core hker hoddker (rootGroup_isPGroup_E8 hβ u rfl) hcore.1 hcore.2
  rw [hψ, ← hRmap] at h4
  exact ⟨R, Rm, hRJ, hRne, hRp, hRmJ, hitem1, h2, h3, Or.inl h4⟩

end CFSG.StandardType.LieKnownR2.E8
