module

public import CFSG.Quasithin.Vol2.Ch3Sec3Obs3324
public import CFSG.LieType.Multipliers.ThreeThreeCenter
public import CFSG.Quasithin.Background.RonanG72Classical
public import CFSG.Adapters.LieModelSimple
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

omit [Finite G] in
theorem s168e3_g2_isPSU
    {H : Subgroup (MulAut (Vtil V₀ V hV))} {U Z : Subgroup (Vtil V₀ V hV)}
    (hN : G2NaturalDerived H U Z 1) : IsPSU 3 3 1 ↥H := by
  obtain ⟨K, hKfield, hKfin, hKcard, π, hπ⟩ := hN
  let _ : Field K := hKfield
  let _ : Finite K := hKfin
  have hchar : CharP K 2 := FFC.charP_two_of_card_pow hKcard
  have hΓ : ⁅quasithinG2 K, quasithinG2 K⁆ ≤ quasithinG2 K := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact (quasithinG2 K).mul_mem
      ((quasithinG2 K).mul_mem ((quasithinG2 K).mul_mem ha hb)
        ((quasithinG2 K).inv_mem ha)) ((quasithinG2 K).inv_mem hb)
  have hfaith : (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).Faithful :=
    FFC.zornQ_faithful _ hΓ
  have e : ↥⁅quasithinG2 K, quasithinG2 K⁆ ≃* ↥H :=
    FFC.equivOfRealizes hfaith hπ
  exact CFSG.Quasithin.H13.Obs3324.isPSU_of_g2Two (K := K) (by rw [hKcard]; norm_num) e.symm

omit [Finite G] in
theorem s168e3_g2_center_eq_bot {H : Subgroup (MulAut (Vtil V₀ V hV))}
    (hPSU : IsPSU 3 3 1 ↥H) (hperf : Group.IsPerfect ↥H) :
    Subgroup.center ↥H = ⊥ := by
  have hsimple : IsSimpleGroup ↥H :=
    CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hPSU
  have hnt : Nontrivial ↥H := hsimple.toNontrivial
  have hnc : ¬ IsMulCommutative ↥H :=
    @Group.IsPerfect.not_isMulCommutative ↥H _ hnt hperf
  exact @TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative ↥H _ hsimple hnc

omit [Finite G] in
theorem s168e3_g2_b42Type {H : Subgroup (MulAut (Vtil V₀ V hV))}
    (hPSU : IsPSU 3 3 1 ↥H) (hperf : Group.IsPerfect ↥H) :
    CFSG.Quasithin.B42TypeU33 ↥H := by
  have hZ : Subgroup.center ↥H = ⊥ := s168e3_g2_center_eq_bot hPSU hperf
  refine ⟨hZ, ?_⟩
  have e : ↥H ⧸ Subgroup.center ↥H ≃* ↥H :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot (G := ↥H))
  exact CFSG.Quasithin.RonanG72.statedClassicalModel_of_mulEquiv e hPSU

omit [Finite G] in
theorem s168e3_center_eq_bot_of_cover
    {H : Subgroup (MulAut (Vtil V₀ V hV))} (hPSU : IsPSU 3 3 1 ↥H)
    {Q : Type} [Group Q] [Finite Q] (hq : CFSG.Open.IsQuasisimple Q)
    (e : (Q ⧸ Subgroup.center Q) ≃* ↥H) :
    Subgroup.center Q = ⊥ := by
  have hPSUq : IsPSU 3 3 1 (Q ⧸ Subgroup.center Q) :=
    CFSG.Quasithin.RonanG72.statedClassicalModel_of_mulEquiv e hPSU
  have hLie : CFSG.Blueprint.LieModel (Q ⧸ Subgroup.center Q) .PSU 3 3 1 :=
    Or.inl ⟨by decide, hPSUq⟩
  exact CFSG.LieType.Multipliers.center_eq_bot_of_lieModel_psu_three_three hq hLie

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
