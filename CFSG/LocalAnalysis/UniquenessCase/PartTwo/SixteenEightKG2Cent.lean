module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKG2CentA
import CFSG.Quasithin.Background.SmithB42U33
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Background.FFC8A
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.TitsIso

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13
open scoped commutatorElement

theorem s16k_centralizer_g2_trivial {Q : Type} [CommGroup Q] {L' : Subgroup (MulAut Q)}
    (h : G2NaturalDerived L' ⊤ ⊥ 1) : Subgroup.centralizer (L' : Set (MulAut Q)) = ⊥ := by
  obtain ⟨e, hLe⟩ := B42U33.exists_equiv_of_g2NaturalDerived h
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  have hcomm : ∀ h ∈ (g2Derived (ZMod 2)).map (g2QAct (ZMod 2)),
      (MulAut.congr e).toMonoidHom y * h = h * (MulAut.congr e).toMonoidHom y := by
    intro h hh
    rw [← hLe] at hh
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hh
    rw [← map_mul, ← map_mul]
    exact congrArg (MulAut.congr e).toMonoidHom
      (Subgroup.mem_centralizer_iff.mp hy l hl).symm
  have h1 : (MulAut.congr e).toMonoidHom y = 1 :=
    schur_Q ((MulAut.congr e).toMonoidHom y) hcomm
  exact (MulAut.congr e).injective (h1.trans (map_one (MulAut.congr e)).symm)

theorem s16k_b42TypeU33_of_g2 (hU : S16kG2IsU33) {Q : Type} [CommGroup Q]
    {L' : Subgroup (MulAut Q)} (h : G2NaturalDerived L' ⊤ ⊥ 1) : B42TypeU33 ↥L' := by
  obtain ⟨K, hKfield, hKfin, hc, π, hπ⟩ := h
  letI := hKfield
  letI := hKfin
  haveI hchar : CharP K 2 := FFC.charP_two_of_card_pow hc
  have hc2 : Nat.card K = 2 := by rw [hc, pow_one]
  have hΓ : ⁅quasithinG2 K, quasithinG2 K⁆ ≤ quasithinG2 K := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact (quasithinG2 K).mul_mem
      ((quasithinG2 K).mul_mem ((quasithinG2 K).mul_mem ha hb)
        ((quasithinG2 K).inv_mem ha)) ((quasithinG2 K).inv_mem hb)
  exact hU K hc2 _ (FFC.equivOfRealizes (FFC.zornQ_faithful _ hΓ) hπ).symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
