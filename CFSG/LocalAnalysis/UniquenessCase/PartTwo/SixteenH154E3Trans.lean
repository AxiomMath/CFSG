module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Fix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Nat
public import CFSG.Quasithin.Background.B4L3Coord
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Shapes
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

private theorem s16h_e3_natural_ne_bot {H : Subgroup (MulAut W)} {U Z : Subgroup W}
    (h : BinaryNaturalSL H U Z 3 1) : U ≠ ⊥ := by
  obtain ⟨K, hK, _, _, π, hπ⟩ := h
  letI : Field K := hK
  obtain ⟨β, hβs, -, -⟩ := FFModel.RealizesVia.coord
    (D := FFModel.nat (StatedSL 3 K)) rfl rfl hπ
  have hm : Multiplicative.ofAdd (fun _ : Fin 3 => (1 : K)) ≠ 1 := by
    intro h1
    have h2 : (fun _ : Fin 3 => (1 : K)) = (fun _ : Fin 3 => 0) :=
      Multiplicative.ofAdd.injective h1
    exact one_ne_zero (congrFun h2 0)
  obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd (fun _ : Fin 3 => (1 : K)))
  intro hU
  haveI : Subsingleton ↥U := by rw [hU]; infer_instance
  have hu1 : u = 1 := Subsingleton.elim u 1
  have hbu : β u = 1 := by rw [hu1, map_one]
  exact hm (hu.symm.trans hbu)

theorem s16h_e3_trans_of_l3_three [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) (hrow : s16h_H5L3Sum L (commSub ⊤ L) ⊥ 3)
    (hZ : commSub ⊤ L ⊓ fixV L = ⊥) :
    ∀ I₁ ∈ irrSet L, ∀ I₂ ∈ irrSet L,
      ∃ g ∈ A ⊓ normalizer (L : Set (MulAut W)), I₂ = I₁.map g.toMonoidHom := by
  rcases hc.conc.2.2 with h1 | h2 | h3 | h4
  · exact (s16h_H5_not_pgroup hc h1).elim
  · exact (s16h_H5_not_tensor hc h2).elim
  · obtain ⟨-, -, htrans⟩ := h3
    exact htrans
  · obtain ⟨hirr, -, -, -⟩ := h4
    obtain ⟨I, -, hind, hsup, hnat⟩ := hrow.2
    have hIU : ∀ i, I i ≤ commSub ⊤ L :=
      fun i => (le_iSup I i).trans (le_sup_right.trans_eq hsup)
    have hstable : ∀ i, StableUnder L (I i) := fun i => c23_binaryNatural_stable (hnat i)
    have hne : ∀ i, I i ≠ ⊥ := fun i => s16h_e3_natural_ne_bot (hnat i)
    have hirrOn : IsIrrOn L (commSub ⊤ L) ⊥ := by
      rw [irrSet, Set.mem_setOf_eq] at hirr
      have h := hirr.2
      rwa [hZ] at h
    have hI0or : I 0 = ⊥ ∨ I 0 = commSub ⊤ L :=
      hirrOn.2.2.2 (I 0) (hstable 0) bot_le (hIU 0)
    rcases hI0or with hI0 | hI0
    · exact absurd hI0 (hne 0)
    · have hI1le0 : I 1 ≤ I 0 := by rw [hI0]; exact hIU 1
      have hI0sup : I 0 ≤ ⨆ (j : Fin 3) (_ : j ≠ 1), I j :=
        le_iSup₂ (f := fun (j : Fin 3) (_ : j ≠ 1) => I j) (0 : Fin 3) (by decide)
      have hI1in : I 1 ≤ ⊥ ⊔ ⨆ (j : Fin 3) (_ : j ≠ 1), I j :=
        le_sup_of_le_right (hI1le0.trans hI0sup)
      have hI1bot : I 1 = ⊥ :=
        le_antisymm ((le_inf le_rfl hI1in).trans (hind 1)) bot_le
      exact absurd hI1bot (hne 1)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
