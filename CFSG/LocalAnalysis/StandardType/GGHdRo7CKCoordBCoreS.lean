module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CCoordDefs
public import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpFrame
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoKey
public import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpTorus
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSpNsComp
import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpPull
import CFSG.LocalAnalysis.StandardType.GGK1CBlSu
import CFSG.LocalAnalysis.StandardType.GGK1CCoLabel
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CDefs

public section

namespace CFSG.StandardType.HdRo7C

open CFSG.StandardType
open CFSG.Open
open CFSG.Assembly
open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)
open Polynomial

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem hdRo7CKCoordAux_bc_ne {tag : LargeEvenLieTag} (htag : tag = .B ∨ tag = .C) :
    tag ≠ .A ∧ tag ≠ .twA ∧ tag ≠ .D ∧ tag ≠ .twD := by
  rcases htag with rfl | rfl <;> decide

private theorem hdRo7CKCoordAux_not_ggLabelIso_bc_twA
    {tag : LargeEvenLieTag} (htag : tag = .B ∨ tag = .C) {r s n n' : ℕ} :
    ¬ GGLabelIso ⟨tag, r, n⟩ ⟨.twA, s, n'⟩ := by
  intro h
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h
  · have ht : tag = .twA := by simpa using congrArg LargeEvenLabel.tag h
    exact (hdRo7CKCoordAux_bc_ne htag).2.1 ht
  · exact absurd h.2.1 (by rintro (h | h) <;> exact absurd h (by simp))
  · have ht : tag = .D := by simpa using congrArg LargeEvenLabel.tag h.1
    exact (hdRo7CKCoordAux_bc_ne htag).2.2.1 ht
  · have ht : tag = .A := by simpa using congrArg LargeEvenLabel.tag h.1
    exact (hdRo7CKCoordAux_bc_ne htag).1 ht
  · have ht : tag = .twD := by simpa using congrArg LargeEvenLabel.tag h.1
    exact (hdRo7CKCoordAux_bc_ne htag).2.2.2 ht
  · have ht : tag = .twA := by simpa using congrArg LargeEvenLabel.tag h.1
    exact (hdRo7CKCoordAux_bc_ne htag).2.1 ht
  · have ht : tag = .twD := by simpa using congrArg LargeEvenLabel.tag h.1
    exact (hdRo7CKCoordAux_bc_ne htag).2.2.2 ht
  · have ht : (.twA : LargeEvenLieTag) = .twD := by simpa using congrArg LargeEvenLabel.tag h.1
    exact absurd ht (by decide)

private theorem hdRo7CKCoordAux_supported_eq_spPull
    {L : Type} [Field L] [Algebra (GaloisField 2 1) L] [Module.Finite (GaloisField 2 1) L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ 3) (hdim : Module.finrank (GaloisField 2 1) L = 2)
    {m : ℕ} (hm : 5 ≤ m) {E : Subgroup (StatedSp m (GaloisField 2 1))}
    (F : ChoiceTwo.SpFrame (GaloisField 2 1) m ζ E) (c : Fin F.s → ZMod 3)
    (J' : Subgroup (StatedSp m (GaloisField 2 1)))
    (hJ' : CFSG.Assembly.IsComponentOf J'
      (Subgroup.centralizer ({F.tor c} : Set (StatedSp m (GaloisField 2 1)))))
    (hsup : J' ≤ CFSG.RankThree.Classical.spSupported (F.tor c)
      {ChoiceTwo.phi3 (GaloisField 2 1)})
    (hbig : 4 ≤ (F.suppSet c).card) :
    J' = CFSG.RankThree.PartOne.spPull (F.tor c) (ChoiceTwo.phi3 (GaloisField 2 1)) := by
  haveI : NeZero m := ⟨by omega⟩
  have hK : Nat.card (GaloisField 2 1) = 2 := by
    simpa using CFSG.LieType.Catalog.card_galoisField 2 1 (by norm_num)
  have hq : CFSG.IsQuasisimple
      ↥(CFSG.RankThree.PartOne.spPull (F.tor c) (ChoiceTwo.phi3 (GaloisField 2 1))) :=
    CFSG.StandardType.A6InsideSp.isQuasisimple_spPull_phi3 (F := F) hK hζ hdim hbig
  refine SevSpNs.eq_spPull_of_le hJ' ?_ hq
  rw [ChoiceTwo.reciprocal_phi3, Set.pair_eq_singleton]
  exact hsup

private theorem hdRo7CKCoordAux_spPull_commutator_eq
    {L : Type} [Field L] [Algebra (GaloisField 2 1) L] [Module.Finite (GaloisField 2 1) L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ 3) (hdim : Module.finrank (GaloisField 2 1) L = 2)
    {m : ℕ} (hm : 5 ≤ m) {E : Subgroup (StatedSp m (GaloisField 2 1))}
    (F : ChoiceTwo.SpFrame (GaloisField 2 1) m ζ E) (c : Fin F.s → ZMod 3)
    (hbig : 4 ≤ (F.suppSet c).card) :
    ⁅CFSG.RankThree.Classical.spSupported (F.tor c) {ChoiceTwo.phi3 (GaloisField 2 1)},
      CFSG.RankThree.Classical.spSupported (F.tor c)
        {ChoiceTwo.phi3 (GaloisField 2 1)}⁆ =
      CFSG.RankThree.PartOne.spPull (F.tor c) (ChoiceTwo.phi3 (GaloisField 2 1)) := by
  classical
  haveI : NeZero m := ⟨by omega⟩
  have hK : Nat.card (GaloisField 2 1) = 2 := by
    simpa using CFSG.LieType.Catalog.card_galoisField 2 1 (by norm_num)
  have hq : CFSG.IsQuasisimple
      ↥(CFSG.RankThree.PartOne.spPull (F.tor c) (ChoiceTwo.phi3 (GaloisField 2 1))) :=
    A6InsideSp.isQuasisimple_spPull_phi3 (F := F) hK hζ hdim hbig
  have hperf : ⁅CFSG.RankThree.PartOne.spPull (F.tor c) (ChoiceTwo.phi3 (GaloisField 2 1)),
      CFSG.RankThree.PartOne.spPull (F.tor c)
        (ChoiceTwo.phi3 (GaloisField 2 1))⁆ =
      CFSG.RankThree.PartOne.spPull (F.tor c) (ChoiceTwo.phi3 (GaloisField 2 1)) :=
    LayerFacts.ggCommutator_eq_of_isQuasisimple hq
  refine le_antisymm ?_ ?_
  · have h := SevSpNs.commutator_le_spPull (x := F.tor c)
      (h := ChoiceTwo.phi3 (GaloisField 2 1))
    rwa [ChoiceTwo.reciprocal_phi3, Set.pair_eq_singleton] at h
  · have hle : CFSG.RankThree.PartOne.spPull (F.tor c)
          (ChoiceTwo.phi3 (GaloisField 2 1)) ≤
        CFSG.RankThree.Classical.spSupported (F.tor c)
          {ChoiceTwo.phi3 (GaloisField 2 1)} :=
      A6InsideSp.spPull_phi3_le_spSupported (F := F) c
    calc CFSG.RankThree.PartOne.spPull (F.tor c) (ChoiceTwo.phi3 (GaloisField 2 1))
        = ⁅CFSG.RankThree.PartOne.spPull (F.tor c) (ChoiceTwo.phi3 (GaloisField 2 1)),
            CFSG.RankThree.PartOne.spPull (F.tor c)
              (ChoiceTwo.phi3 (GaloisField 2 1))⁆ := hperf.symm
      _ ≤ ⁅CFSG.RankThree.Classical.spSupported (F.tor c)
              {ChoiceTwo.phi3 (GaloisField 2 1)},
            CFSG.RankThree.Classical.spSupported (F.tor c)
              {ChoiceTwo.phi3 (GaloisField 2 1)}⁆ :=
          Subgroup.commutator_mono hle hle

private theorem hdRo7CKCoordAux_spPull_model
    {L : Type} [Field L] [Algebra (GaloisField 2 1) L] [Module.Finite (GaloisField 2 1) L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ 3) (hdim : Module.finrank (GaloisField 2 1) L = 2)
    {m : ℕ} (hm : 5 ≤ m) {E : Subgroup (StatedSp m (GaloisField 2 1))}
    (F : ChoiceTwo.SpFrame (GaloisField 2 1) m ζ E) (c : Fin F.s → ZMod 3)
    (hbig : 4 ≤ (F.suppSet c).card) :
    ggK1CCo_Kind.Model 1 (ggK1CCo_Kind.su (F.suppSet c).card)
      (CFSG.RankThree.PartOne.spPull (F.tor c) (ChoiceTwo.phi3 (GaloisField 2 1))) := by
  classical
  haveI : NeZero m := ⟨by omega⟩
  have hK : Nat.card (GaloisField 2 1) = 2 := by
    simpa using CFSG.LieType.Catalog.card_galoisField 2 1 (by norm_num)
  have hK' : Nat.card (GaloisField 2 1) = 2 ^ 1 := by simpa using hK
  have hc0 : c ≠ 0 := by
    intro h
    rw [h] at hbig
    simp [ChoiceTwo.SpFrame.suppSet] at hbig
  have blocks := F.blocks_tor hK hζ hc0
  have hmem : ChoiceTwo.phi3 (GaloisField 2 1) ∈ primaryFactors (spEnd (F.tor c)) := by
    by_contra hnm
    have hbot := primaryComponent_eq_bot_of_not_mem (ChoiceTwo.phi3_irreducible hK)
      ChoiceTwo.monic_phi3 hnm
    have hm' := F.finrank_phi3_tor hζ hdim c
    rw [hbot, finrank_bot] at hm'
    omega
  have hself : reciprocalPolynomial
      ((⟨ChoiceTwo.phi3 (GaloisField 2 1), hmem⟩ : primaryFactors (spEnd (F.tor c))) :
        (GaloisField 2 1)[X]) =
      (⟨ChoiceTwo.phi3 (GaloisField 2 1), hmem⟩ : primaryFactors (spEnd (F.tor c))) :=
    ChoiceTwo.reciprocal_phi3
  obtain ⟨d, hd2, -, -, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, ⟨e, he⟩, φ, hφ⟩ :=
    (blocks.selfDual ⟨ChoiceTwo.phi3 (GaloisField 2 1), hmem⟩
      ChoiceTwo.phi3_ne_X_sub_one hself).exists_half
  have hd1 : d = 1 := by
    have h := hd2
    rw [ChoiceTwo.natDegree_phi3] at h
    omega
  subst hd1
  haveI : Fact (Irreducible ((⟨ChoiceTwo.phi3 (GaloisField 2 1), hmem⟩ :
      primaryFactors (spEnd (F.tor c))) : (GaloisField 2 1)[X])) :=
    ⟨ChoiceTwo.phi3_irreducible hK⟩
  haveI : Finite (AdjoinRoot ((⟨ChoiceTwo.phi3 (GaloisField 2 1), hmem⟩ :
      primaryFactors (spEnd (F.tor c))) : (GaloisField 2 1)[X])) := hE.finite
  haveI : Fintype (AdjoinRoot ((⟨ChoiceTwo.phi3 (GaloisField 2 1), hmem⟩ :
      primaryFactors (spEnd (F.tor c))) : (GaloisField 2 1)[X])) := Fintype.ofFinite _
  have hmul : primaryMultiplicity (spEnd (F.tor c)) (ChoiceTwo.phi3 (GaloisField 2 1)) =
      (F.suppSet c).card := F.mult_phi3_tor hK hζ hdim c
  have hm1 : 1 ≤ primaryMultiplicity (spEnd (F.tor c)) (ChoiceTwo.phi3 (GaloisField 2 1)) := by
    rw [hmul]
    omega
  have hq : CFSG.IsQuasisimple
      ↥(CFSG.RankThree.PartOne.spPull (F.tor c) (ChoiceTwo.phi3 (GaloisField 2 1))) :=
    A6InsideSp.isQuasisimple_spPull_phi3 (F := F) hK hζ hdim hbig
  have hcomm := hdRo7CKCoordAux_spPull_commutator_eq hζ hdim hm F c hbig
  have hsu := ggK1CBl_classical_su (K := GaloisField 2 1)
    (A := CFSG.RankThree.Classical.spSupported (F.tor c)
      {ChoiceTwo.phi3 (GaloisField 2 1)})
    hK' (le_refl 1) hm1 hE hHf hHfl e he φ
  have hq_comm : CFSG.IsQuasisimple
      ↥⁅CFSG.RankThree.Classical.spSupported (F.tor c)
          {ChoiceTwo.phi3 (GaloisField 2 1)},
        CFSG.RankThree.Classical.spSupported (F.tor c)
          {ChoiceTwo.phi3 (GaloisField 2 1)}⁆ := by
    rw [hcomm]
    exact hq
  have hmodel_comm := hsu.2.2 hq_comm
  rw [hcomm, hmul] at hmodel_comm
  exact ggK1CBl_model_subgroup
    (CFSG.RankThree.PartOne.spPull (F.tor c) (ChoiceTwo.phi3 (GaloisField 2 1)))
    hmodel_comm

private theorem hdRo7CKCoordAux_spPull_label_transport
    {m : ℕ} [NeZero m] {K : Type} [Field K] [Finite K] [CharP K 2]
    {H : Subgroup (StatedSp m K)} {lab : LargeEvenLabel}
    (h : GGHasLabel lab
      (↥(H.map (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m K))
        ⧸ Subgroup.center ↥(H.map (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m K)))) :
    GGHasLabel lab (↥H ⧸ Subgroup.center ↥H) := by
  have hinj : Function.Injective
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m K) :=
    (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
      (r := m) (K := K)).1
  let e : ↥H ≃* ↥(H.map (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m K)) :=
    Subgroup.equivMapOfInjective H _ hinj
  have hc : (Subgroup.center ↥H).map
        (e : ↥H →* ↥(H.map (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m K))) =
      Subgroup.center ↥(H.map (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m K)) :=
    Subgroup.map_center_eq e
  let e' : (↥H ⧸ Subgroup.center ↥H) ≃*
      (↥(H.map (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m K))
        ⧸ Subgroup.center
          ↥(H.map (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m K))) :=
    QuotientGroup.congr _ _ e hc
  exact ggHasLabel_of_mulEquiv e'.symm h

private theorem hdRo7CKCoordAux_ggMultBlockA_lab {r nf : ℕ} (h : 2 ≤ r) :
    (ggMultBlockA r nf 2).lab = ⟨.twA, r, nf⟩ := by
  simp [ggMultBlockA, h]

private theorem hdRo7CKCoordAux_spPull_hasLabel
    {L : Type} [Field L] [Algebra (GaloisField 2 1) L] [Module.Finite (GaloisField 2 1) L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ 3) (hdim : Module.finrank (GaloisField 2 1) L = 2)
    {m : ℕ} (hm : 5 ≤ m) {E : Subgroup (StatedSp m (GaloisField 2 1))}
    (F : ChoiceTwo.SpFrame (GaloisField 2 1) m ζ E) (c : Fin F.s → ZMod 3)
    (hbig : 4 ≤ (F.suppSet c).card) :
    GGHasLabel ⟨.twA, (F.suppSet c).card - 1, 1⟩
      (↥(CFSG.RankThree.PartOne.spPull (F.tor c) (ChoiceTwo.phi3 (GaloisField 2 1)))
        ⧸ Subgroup.center ↥(CFSG.RankThree.PartOne.spPull (F.tor c)
          (ChoiceTwo.phi3 (GaloisField 2 1)))) := by
  classical
  haveI : NeZero m := ⟨by omega⟩
  have hK : Nat.card (GaloisField 2 1) = 2 := by
    simpa using CFSG.LieType.Catalog.card_galoisField 2 1 (by norm_num)
  have hK' : Nat.card (GaloisField 2 1) = 2 ^ 1 := by simpa using hK
  have hq : CFSG.IsQuasisimple
      ↥(CFSG.RankThree.PartOne.spPull (F.tor c) (ChoiceTwo.phi3 (GaloisField 2 1))) :=
    A6InsideSp.isQuasisimple_spPull_phi3 (F := F) hK hζ hdim hbig
  have hmodel := hdRo7CKCoordAux_spPull_model hζ hdim hm F c hbig
  have hlab := ggK1CCo_kind_label (nf := 1) (ggK1CCo_Kind.su (F.suppSet c).card)
    (CFSG.RankThree.PartOne.spPull (F.tor c) (ChoiceTwo.phi3 (GaloisField 2 1))) hq hmodel hK'
  have horbit : (ggK1CCo_kindOrbit 1 (ggK1CCo_Kind.su (F.suppSet c).card)).lab =
      ⟨.twA, (F.suppSet c).card - 1, 1⟩ := by
    have hs : 2 ≤ (F.suppSet c).card - 1 := by omega
    rw [ggK1CCo_kindOrbit]
    all_goals first
      | exact hdRo7CKCoordAux_ggMultBlockA_lab (r := (F.suppSet c).card - 1) (nf := 1) hs
      | omega
  rw [horbit] at hlab
  exact hdRo7CKCoordAux_spPull_label_transport (m := m) (H :=
    CFSG.RankThree.PartOne.spPull (F.tor c) (ChoiceTwo.phi3 (GaloisField 2 1))) hlab

theorem hdRo7CKCoordAux_supported_false_core
    (hRig : GGLabelRigidInput)
    {L : Type} [Field L] [Algebra (GaloisField 2 1) L] [Module.Finite (GaloisField 2 1) L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ 3) (hdim : Module.finrank (GaloisField 2 1) L = 2)
    {m : ℕ} (hm : 5 ≤ m) {E : Subgroup (StatedSp m (GaloisField 2 1))}
    (F : ChoiceTwo.SpFrame (GaloisField 2 1) m ζ E) (c : Fin F.s → ZMod 3)
    (J' : Subgroup (StatedSp m (GaloisField 2 1)))
    (hJ' : CFSG.Assembly.IsComponentOf J'
      (Subgroup.centralizer ({F.tor c} : Set (StatedSp m (GaloisField 2 1)))))
    {tag : LargeEvenLieTag} (htag : tag = .B ∨ tag = .C)
    (hlabel : GGHasLabel ⟨tag, m - 2, 1⟩ (↥J' ⧸ Subgroup.center ↥J'))
    (hsup : J' ≤ CFSG.RankThree.Classical.spSupported (F.tor c)
      {ChoiceTwo.phi3 (GaloisField 2 1)}) :
    False := by
  classical
  haveI : NeZero m := ⟨by omega⟩
  by_cases hsmall : (F.suppSet c).card ≤ 3
  ·
    have hq : CFSG.IsQuasisimple ↥J' :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native J').1 hJ'.2.2
    have hperf : ⁅J', J'⁆ = J' := LayerFacts.ggCommutator_eq_of_isQuasisimple hq
    have hK : Nat.card (GaloisField 2 1) = 2 := by
      simpa using CFSG.LieType.Catalog.card_galoisField 2 1 (by norm_num)
    have hJfixed : J' ≤ CFSG.RankThree.PartOne.spFixedFactor (F.tor c) :=
      F.le_spFixedFactor hK hζ hdim hsmall hperf hJ'.1
    exact SevSpNs.false_of_le_of_commute hJ'.2.2 le_rfl fun g hg g' hg' =>
      ChoiceTwo.commute_of_mem_spFixedFactor hK (F.tor_pow_three hζ.pow_eq_one c)
        (O := {ChoiceTwo.phi3 (GaloisField 2 1)})
        (by rw [Set.mem_singleton_iff]; exact fun h => ChoiceTwo.phi3_ne_X_sub_one h.symm)
        (hJfixed hg) (hsup hg')
  ·
    push Not at hsmall
    have hbig : 4 ≤ (F.suppSet c).card := by omega
    have hJs := hdRo7CKCoordAux_supported_eq_spPull hζ hdim hm F c J' hJ' hsup hbig
    have htwA_sp := hdRo7CKCoordAux_spPull_hasLabel hζ hdim hm F c hbig
    have htwA : GGHasLabel ⟨.twA, (F.suppSet c).card - 1, 1⟩
        (↥J' ⧸ Subgroup.center ↥J') := by
      rw [hJs]
      exact htwA_sp
    have hΛ : LargeEvenInLambda2 ⟨tag, m - 2, 1⟩ := by
      rcases htag with rfl | rfl
      · show 1 ≤ 1 ∧ 2 ≤ m - 2 ∧ (m - 2 = 2 → 2 ≤ 1)
        exact ⟨by norm_num, by omega, fun h => by omega⟩
      · show 1 ≤ 1 ∧ 2 ≤ m - 2 ∧ (m - 2 = 2 → 2 ≤ 1)
        exact ⟨by norm_num, by omega, fun h => by omega⟩
    have hΛ' : LargeEvenInLambda2 ⟨.twA, (F.suppSet c).card - 1, 1⟩ := by
      show 1 ≤ 1 ∧ 2 ≤ (F.suppSet c).card - 1 ∧ ((F.suppSet c).card - 1 = 2 → 2 ≤ 1)
      exact ⟨by norm_num, by omega, fun h => by omega⟩
    have hiso := hRig ⟨tag, m - 2, 1⟩ ⟨.twA, (F.suppSet c).card - 1, 1⟩
      (↥J' ⧸ Subgroup.center ↥J') hΛ hΛ' hlabel htwA
    exact hdRo7CKCoordAux_not_ggLabelIso_bc_twA htag hiso

end CFSG.StandardType.HdRo7C

end
