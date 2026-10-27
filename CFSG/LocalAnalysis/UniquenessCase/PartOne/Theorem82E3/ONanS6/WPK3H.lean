module

public import CFSG.HardMathSupport.Solomon.Coordinator.ONCSylow
public import CFSG.LocalAnalysis.AGLEmbedding.CoverAbelianSylowAux
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicAlpha
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG
open scoped commutatorElement
open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)
variable {G : Type} [Group G] [Finite G] {D : Data G}

theorem K3_holds' :
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K3 := by
  intro Y _ _ hY S
  obtain ⟨hq, hZcard, hON⟩ := hY
  obtain ⟨e⟩ := hON
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Group.IsPerfect Y := ⟨hq.1⟩
  have hZp : IsPGroup 3 (Subgroup.center Y) :=
    IsPGroup.of_card (n := 1) (by rw [hZcard, pow_one])
  have hcardON : Nat.card (Y ⧸ Subgroup.center Y) = 460815505920 := by
    rw [Nat.card_congr e.toEquiv]
    change Nat.card CFSG.Blueprint.NativeSporadic.ON = 460815505920
    exact CFSG.Sporadic.ON.card_ON
  have hD : CFSG.AGLEmbedding.AbelianSylowDatum (Y ⧸ Subgroup.center Y) 3 :=
    CFSG.AGLEmbedding.AbelianSylowDatum.of_mulEquiv e.symm
      CFSG.AGLEmbedding.abelianSylowDatum_ON_three
  let π : Y →* Y ⧸ Subgroup.center Y := QuotientGroup.mk' _
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = Subgroup.center Y := QuotientGroup.ker_mk' _
  obtain ⟨hcardS, hexpS, hcommS, hcenS⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.sylow_hat_on hD hcardON hq.1 hZcard π hπ hker S
  have hZY : Subgroup.center Y ≤ (S : Subgroup Y) := IsPGroup.le_sylow_of_normal hZp S
  have hZleC : Subgroup.center Y ≤ Subgroup.centralizer (S : Set Y) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro m _
    exact Subgroup.mem_center_iff.mp hz m
  have hZle : Subgroup.center Y ≤ (S : Subgroup Y) ⊓ Subgroup.centralizer (S : Set Y) :=
    le_inf hZY hZleC
  have hleZ : (S : Subgroup Y) ⊓ Subgroup.centralizer (S : Set Y) ≤ Subgroup.center Y := by
    rintro x ⟨hxS, hxC⟩
    exact hcenS x hxS fun g hg => Subgroup.mem_centralizer_iff.mp hxC g hg
  have hcenEq : (S : Subgroup Y) ⊓ Subgroup.centralizer (S : Set Y) = Subgroup.center Y :=
    le_antisymm hleZ hZle
  have hcommZ : ⁅(S : Subgroup Y), (S : Subgroup Y)⁆ ≤ Subgroup.center Y :=
    Subgroup.commutator_le.mpr hcommS
  have hZcomm : Subgroup.center Y ≤ ⁅(S : Subgroup Y), (S : Subgroup Y)⁆ := fun z hz => by
    obtain ⟨k, hk⟩ := hZp ⟨z, hz⟩
    exact CFSG.AGLEmbedding.center_le_commutator_of_isPerfect S hz ⟨k, congrArg Subtype.val hk⟩
  have hcommEq : ⁅(S : Subgroup Y), (S : Subgroup Y)⁆ = Subgroup.center Y :=
    le_antisymm hcommZ hZcomm
  exact ⟨hcardS, hexpS, by rw [hcenEq, hZcard], by rw [hcommEq, hcenEq]⟩

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
