module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1OmegaCScal
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Background.B4L3Coord
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.RankThree.GF2n.Stroth80

theorem s16k_centralizer_of_addCommutant {Q : Type} [CommGroup Q] {L' : Subgroup (MulAut Q)}
    {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {Γ : Subgroup (GL ι K)} (hΓ : AddCommutantScalar Γ)
    (h : (FFModel.nat Γ).Realizes L' ⊤ ⊥) :
    Subgroup.centralizer (L' : Set (MulAut Q)) = ⊥ := by
  classical
  by_cases hι : Nonempty ι
  · obtain ⟨π, hπ⟩ := h
    obtain ⟨f, hf⟩ := s16e_omc_centralizer_hom_units (H := L') hΓ hπ
    haveI : Fintype K := Fintype.ofFinite K
    have hcardK : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
    haveI : Subsingleton Kˣ :=
      Fintype.card_le_one_iff_subsingleton.1 (by rw [Fintype.card_units, hcardK])
    rw [Subgroup.eq_bot_iff_forall]
    intro c hc
    have h1 : (⟨c, hc⟩ : ↥(Subgroup.centralizer (L' : Set (MulAut Q)))) = 1 :=
      hf (Subsingleton.elim (f ⟨c, hc⟩) (f 1))
    exact Subtype.ext_iff.mp h1
  · rw [not_nonempty_iff] at hι
    obtain ⟨π, hπ⟩ := h
    obtain ⟨β, -, hβk, -⟩ :=
      FFModel.RealizesVia.coord (D := FFModel.nat Γ) rfl rfl hπ
    have hβ_inj : Function.Injective β := by
      rw [injective_iff_map_eq_one]
      intro u hu
      exact Subtype.ext (Subgroup.mem_bot.mp ((hβk u).1 hu))
    haveI hsubA : Subsingleton (ι → K) :=
      ⟨fun f g => funext fun i => (hι.false i).elim⟩
    haveI hsubM : Subsingleton ((FFModel.nat Γ).Amb) := hsubA
    haveI hsubU : Subsingleton ↥(⊤ : Subgroup Q) :=
      ⟨fun u v => hβ_inj (Subsingleton.elim (β u) (β v))⟩
    haveI hsubQ : Subsingleton Q :=
      ⟨fun x y => (Subgroup.topEquiv (G := Q)).symm.injective (Subsingleton.elim _ _)⟩
    rw [Subgroup.eq_bot_iff_forall]
    intro c hc
    apply MulEquiv.ext
    intro q
    exact Subsingleton.elim (c q) ((1 : MulAut Q) q)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
