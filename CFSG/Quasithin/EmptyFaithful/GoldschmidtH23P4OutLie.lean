module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4OutBase
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.EmptyFaithful.SBc11List
public import CFSG.Quasithin.Recognition.CertU33AutBound
public import CFSG.Timmesfeld.Final.PSU33
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
public import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.Sporadic.Schreier.TitsAutD
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryTrace
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.Quasithin.H23Out

open CFSG.ComponentClassification.OuterAutomorphisms

theorem nonempty_mulEquiv_PSU3_of_isPSU33 {X : Type} [Group X] (h : IsPSU 3 3 1 X) :
    Nonempty (X ≃* CFSG.Open.PSU3 3 1) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have := Fintype.ofFinite K
  have := Fintype.ofFinite (GaloisField 3 (2 * 1))
  have hc : Fintype.card K = Fintype.card (GaloisField 3 (2 * 1)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      CFSG.Timmesfeld.Final.GF9.card]
  obtain ⟨e'⟩ := CFSG.Timmesfeld.Final.nonempty_statedProj_statedSU_equiv_PSU3
  exact ⟨e.trans ((CFSG.Fischer.Classification.Recognition.statedProjSUEquiv
    (FiniteField.ringEquivOfCardEq hc) 3 (3 ^ 1)).trans e')⟩

section U33


theorem noFiveOut_of_isPSU33 {X : Type} [Group X] (h : IsPSU 3 3 1 X) : NoFiveOut X := by
  obtain ⟨e⟩ := nonempty_mulEquiv_PSU3_of_isPSU33 h
  have hcard := CFSG.Quasithin.SBc11.card_of_isPSU_three_three h
  have hfin : Finite X := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  refine NoFiveOut.of_card_mulAut_le
    (CFSG.Quasithin.SBc11.center_eq_bot_of_list (Or.inr (Or.inr h))) ?_
  rw [Nat.card_congr (MulAut.congr e).toEquiv, hcard]
  have := CFSG.Quasithin.card_mulAut_psu3_le
  omega

theorem out5Pow_of_isPSU33 {X : Type} [Group X] [Finite X] (h : IsPSU 3 3 1 X) : Out5Pow X :=
  Out5Pow.of_noFiveOut (noFiveOut_of_isPSU33 h)

end U33

section D4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem card_outer_is3D4 {X : Type} [Group X] (hm : Is3D4 2 1 X) : Nat.card (Outer X) = 3 := by
  have hm0 : ChevalleyExceptionalModel X .trialityD4 2 1 := hm
  obtain ⟨hp, hf, -⟩ := hm0.1
  have hm' : TwistedChevalleyModel X .D4 (2 ^ 1) := hm0.2
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hp hf hm'
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC
  obtain ⟨-, -, ⟨Θ, -, hsurj, hker, -⟩, -, hcard, -⟩ :=
    even_triality_exact_automorphism_normal_form (f := 1) hf K hK σ hσ
  have hker' : Θ.ker = inner C := hker
  have hle : inner C ≤ Θ.ker := hker'.ge
  set Φ := QuotientGroup.lift (inner C) Θ hle
  have hΦsurj : Function.Surjective Φ := fun y => by
    obtain ⟨α, rfl⟩ := hsurj y
    exact ⟨α, QuotientGroup.lift_mk _ hle α⟩
  have hΦker : Φ.ker = ⊥ := by
    rw [QuotientGroup.ker_lift, hker', QuotientGroup.map_mk'_self]
  have : Finite (Outer C) := by
    have : Finite (MulAut C) := MulEquiv.finite_left
    infer_instance
  have hcardO : Nat.card (Outer C) = 3 * 1 := by
    rw [← Subgroup.card_mul_index Φ.ker, Subgroup.index_ker, MonoidHom.range_eq_top.2 hΦsurj,
      Subgroup.card_top, hcard, hΦker, Subgroup.card_bot, one_mul]
  rw [Nat.card_congr (equivalence e).toEquiv, hcardO]

theorem noFiveOut_of_is3D4 {X : Type} [Group X] (h : Is3D4 2 1 X) : NoFiveOut X := by
  unfold NoFiveOut
  rw [card_outer_is3D4 h]
  norm_num

theorem out5Pow_of_is3D4 {X : Type} [Group X] [Finite X] (h : Is3D4 2 1 X) : Out5Pow X :=
  Out5Pow.of_noFiveOut (noFiveOut_of_is3D4 h)

end D4

section Tits


theorem noFiveOut_of_isTits {X : Type} [Group X] (h : IsTits X) : NoFiveOut X := by
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv X 2 1 h
  refine NoFiveOut.of_mulEquiv e ?_
  unfold NoFiveOut
  rw [CFSG.Sporadic.Schreier.Tits.card_outer_titsD]
  norm_num

theorem out5Pow_of_isTits {X : Type} [Group X] [Finite X] (h : IsTits X) : Out5Pow X :=
  Out5Pow.of_noFiveOut (noFiveOut_of_isTits h)

end Tits

end CFSG.Quasithin.H23Out
