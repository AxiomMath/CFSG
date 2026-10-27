module

public import CFSG.LocalAnalysis.StandardType.GGTBJUnitaryDvd
public import CFSG.LocalAnalysis.StandardType.GGTBJLE3Transport
public import CFSG.LocalAnalysis.StandardType.GGTWZKQuotient
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitarySixOriginal
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSU
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvdSmall
public import CFSG.LocalAnalysis.StandardType.GGTBJFamilyInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.Line63.H5 CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement

private theorem ggSix_comm_mul_left_central {G : Type*} [Group G] {a b z : G}
    (hzb : z * b = b * z) : ⁅a * z, b⁆ = ⁅a, b⁆ := by
  have hz : z * b * z⁻¹ = b := by rw [hzb, mul_inv_cancel_right]
  calc ⁅a * z, b⁆ = a * (z * b * z⁻¹) * a⁻¹ * b⁻¹ := by
        simp only [commutatorElement_def, mul_inv_rev]; group
    _ = ⁅a, b⁆ := by rw [hz]; simp only [commutatorElement_def]

private theorem ggSix_comm_mul_right_central {G : Type*} [Group G] {a b w : G}
    (hwa : w * a = a * w) : ⁅a, b * w⁆ = ⁅a, b⁆ := by
  have hw : w * a⁻¹ * w⁻¹ = a⁻¹ := by
    rw [(Commute.inv_right (show Commute w a from hwa)).eq, mul_inv_cancel_right]
  calc ⁅a, b * w⁆ = a * b * (w * a⁻¹ * w⁻¹) * b⁻¹ := by
        simp only [commutatorElement_def, mul_inv_rev]; group
    _ = ⁅a, b⁆ := by rw [hw]; simp only [commutatorElement_def]

theorem eq_of_map_redMk_eq_redMkL_range {G : Type} [Group G] [Finite G] {X J : Subgroup G}
    (hXp : commutator ↥X = ⊤) (hJX : J ≤ X)
    (h : (J.subgroupOf (Subgroup.normalizer (X : Set G))).map (redMk X) =
      (redMkL X).range) : J = X := by
  classical
  have hdec : ∀ a ∈ X, ∃ j ∈ J, ∃ z ∈ twoCenter X, a = j * z := by
    intro a ha
    have hmem : redMkL X ⟨a, ha⟩ ∈
        (J.subgroupOf (Subgroup.normalizer (X : Set G))).map (redMk X) := by
      rw [h]
      exact ⟨⟨a, ha⟩, rfl⟩
    obtain ⟨j', hj', hjeq⟩ := hmem
    have h1 : redMk X (j'⁻¹ * ⟨a, Subgroup.le_normalizer ha⟩) = 1 := by
      rw [map_mul, map_inv]
      have : redMk X ⟨a, Subgroup.le_normalizer ha⟩ = redMk X j' := hjeq.symm
      rw [this, inv_mul_cancel]
    have h2 := (redMk_eq_one_iff X _).mp h1
    refine ⟨(j' : G), Subgroup.mem_subgroupOf.mp hj', (j' : G)⁻¹ * a, ?_, by group⟩
    simpa using h2
  have hXX : ⁅X, X⁆ = X := Subgroup.isPerfect_iff.1 (Group.IsPerfect.mk hXp)
  refine le_antisymm hJX ?_
  calc X = ⁅X, X⁆ := hXX.symm
    _ ≤ J := by
      refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
      obtain ⟨j, hj, z, hz, rfl⟩ := hdec a ha
      obtain ⟨j', hj', w, hw, rfl⟩ := hdec b hb
      have hwX : w ∈ X := hw.1
      have hjX : j ∈ X := hJX hj
      have hj'X : j' ∈ X := hJX hj'
      rw [ggSix_comm_mul_left_central (hz.2.1 _ (X.mul_mem hj'X hwX)),
        ggSix_comm_mul_right_central (hw.2.1 j hjX), commutatorElement_def]
      exact J.mul_mem (J.mul_mem (J.mul_mem hj hj') (J.inv_mem hj)) (J.inv_mem hj')

theorem ggResSideDatumLE3_of_redMk
    {G : Type} [Group G] [Finite G] {X Bs J : Subgroup G}
    (hBs : IsElemAbelian 3 Bs) (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hJX : J ≤ X) (hBJ : Bs ≤ Subgroup.normalizer (J : Set G))
    (hD : GGResSideDatum 3 (redMkB hN).range (redMkL X).range
        ((J.subgroupOf (Subgroup.normalizer (X : Set G))).map (redMk X)) ∨
      GGResLeviSideDatumLE3 3 (redMkB hN).range (redMkL X).range
        ((J.subgroupOf (Subgroup.normalizer (X : Set G))).map (redMk X))) :
    GGResSideDatum 3 Bs X J ∨ GGResLeviSideDatumLE3 3 Bs X J := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXmap : (X.subgroupOf (Subgroup.normalizer (X : Set G))).map (redMk X) =
      (redMkL X).range := by
    ext q
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨⟨l, hl⟩, rfl⟩
    · rintro ⟨l, rfl⟩
      exact ⟨⟨l, Subgroup.le_normalizer l.2⟩, l.2, rfl⟩
  have hXaut := ggAutomizer_redMk_eq hBs hN Subgroup.le_normalizer hN
  rw [hXmap] at hXaut
  have hJaut := ggAutomizer_redMk_eq hBs hN (hJX.trans Subgroup.le_normalizer) hBJ
  rcases hD with hD | hD
  · exact Or.inl ((GGResSideDatum.transport_iff
      (MonoidHom.ofInjective (redMkB_injective hN hBs)) hXaut hJaut).mpr hD)
  · exact Or.inr ((GGResLeviSideDatumLE3.transport_iff
      (MonoidHom.ofInjective (redMkB_injective hN hBs)) hXaut hJaut).mpr hD)

theorem ggTBJUnitarySix_of_component
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K X : Subgroup G} (hH : GGResHyp 3 B Bs x L D J y K)
    (hLab : GGHasLabel ⟨.twA, 5, 1⟩ (X ⧸ Subgroup.center X))
    (hΛ : LargeEvenInLambda2 ⟨.twA, 5, 1⟩)
    (hInn : GGInnerDiagOn Bs X)
    (hcard : ∀ hN : Bs ≤ Subgroup.normalizer (X : Set G),
      3 ^ 4 ≤ Nat.card (ggGamma X hN).range)
    {C : Subgroup G} (hCB : C ≤ Bs)
    (hJ : IsComponentOf J (X ⊓ Subgroup.centralizer (C : Set G))) (hJX : J ≠ X) :
    GGResSideDatum 3 Bs X J ∨ GGResLeviSideDatumLE3 3 Bs X J := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmark := ggInnerDiagOn_relabel hRig hInn hΛ hLab
  obtain ⟨hXperf, lab, hlab, hraw⟩ := hmark
  obtain ⟨R₀, _, I₀, F₀, _, _, _, hP₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨heq, -, -⟩ := hP₀
  subst lab
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨F, hField, hFinite, hFK, hQ⟩ := hraw
  let : Field F := hField
  let : Finite F := hFinite
  have hF : Nat.card F = 4 := by simpa using hFK
  have : CharP F 2 := charP_two_of_card (by simpa using hF : Nat.card F = 2 ^ 2)
  obtain ⟨hs, hna, θ, hP⟩ := hQ
  obtain ⟨-, hN, hBsI⟩ := hP
  have hBs : IsElemAbelian 3 Bs := hH.1.tableB_facts.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hH.1.2.1.2.2.2
  have hBJ : Bs ≤ Subgroup.normalizer (J : Set G) := hH.Bs_le_normalizer_J
  have hJXle : J ≤ X := hJ.1.trans inf_le_left
  obtain ⟨hNbar, φ, hM, hdiag⟩ :=
    exists_diagonal_cover_of_unitary_six_two_red hF hXperf θ hN hBs hBsI (hcard hN)
  obtain ⟨S, hS2, hJblock, hJbarComp⟩ :=
    exists_block_unitarySix_reduced_component hF hBs hN hCB hJ hNbar φ hM hdiag
  have hS4 : 4 ≤ S.card := by
    by_contra hlt
    have hsol : Group.IsSolvable ↥((TableBUE.blockSU (K := F) (n := 1) S).map
        (((redMkL X).range).subtype.comp φ)) :=
      WitSU.isSolvable_map_blockSU_two_one hM.field _ (by omega) (by omega)
    have hsolJ : Group.IsSolvable
        ↥((J.subgroupOf (Subgroup.normalizer (X : Set G))).map (redMk X)) := by
      rw [hJblock]
      exact hsol
    exact SmallU.not_isComponentOf_of_solvable hJbarComp hsolJ
  have hS5 : S.card ≤ 5 := by
    by_contra hS6
    have hSle : S.card ≤ 6 := by
      simpa only [Fintype.card_fin] using Finset.card_le_univ S
    have hSuniv : S = Finset.univ :=
      Finset.eq_univ_of_card S (by simpa only [Fintype.card_fin] using (by omega : S.card = 6))
    apply hJX
    refine eq_of_map_redMk_eq_redMkL_range hXperf hJXle ?_
    rw [hJblock, hSuniv, SUTorus.blockSU_univ, ← MonoidHom.range_eq_map, MonoidHom.range_comp,
      MonoidHom.range_eq_top_of_surjective _ hM.surj, Subgroup.map_top, Subgroup.range_subtype]
  have hred := ggTBJUnitary_sideDatum_of_block (p := 3) (r := 5) (f := 1)
    (by simpa using hF) le_rfl (by norm_num) (by norm_num) (by norm_num)
    (isElemAbelian_redB hN hBs) (redSC hN hBs hSC) hNbar hM hdiag S hS2 hS5 (by omega) hJblock
  exact ggResSideDatumLE3_of_redMk hBs hN hJXle hBJ hred

theorem ggTBJLeft_unitarySix_of_label
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp 3 B Bs x L D J y K)
    (hLab : GGHasLabel ⟨.twA, 5, 1⟩ (L ⧸ Subgroup.center L))
    (hΛ : LargeEvenInLambda2 ⟨.twA, 5, 1⟩) :
    GGResSideDatum 3 Bs L J ∨ GGResLeviSideDatumLE3 3 Bs L J := by
  have hDB : D ≤ Bs := hH.1.2.2.1.1.trans hH.1.2.1.1
  exact ggTBJUnitarySix_of_component hRig hH hLab hΛ hH.2.2.1.1
    (fun hN => four_le_card_ggGamma_of_unitary_six_L hRig hH (by norm_num) hLab hΛ hN)
    hDB hH.1.2.2.1.2.2.2.2.2.1 (ggResHyp_J_ne_L hH)

theorem ggTBJNbr_unitarySix_of_label
    (hRig : GGLabelRigidInput) (hI3 : GGNbrSubcomponentInput)
    (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp 3 B Bs x L D J y K)
    (hLab : GGHasLabel ⟨.twA, 5, 1⟩ (K ⧸ Subgroup.center K))
    (hΛ : LargeEvenInLambda2 ⟨.twA, 5, 1⟩) :
    GGResSideDatum 3 Bs K J ∨ GGResLeviSideDatumLE3 3 Bs K J := by
  have hnb : GGNbr 3 B x D J y K := hH.2.2.2.2.1
  have hpJ : 3 ∣ Nat.card J := hSP G 3 B x L D J hH.1.1 hH.1.2.2
  have hJK : J ≤ K := hI3 G 3 B x L D J hH.1.1 hH.1.2.2 y K hnb
  have hcomp := ggIsComponentOf_inf_centralizer_nbr hH.1 hnb hJK
  have hxD : x ∈ D := hH.1.2.2.1.2.2.2.1
  have hx : x ∈ Bs := hH.1.2.1.1 (hH.1.2.2.1.1 hxD)
  have hcomp' : IsComponentOf J (K ⊓ Subgroup.centralizer
      ((Subgroup.zpowers x : Subgroup G) : Set G)) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hcomp
  exact ggTBJUnitarySix_of_component hRig hH hLab hΛ (hH.2.2.1.2 y K hnb)
    (fun hN => four_le_card_ggGamma_of_unitary_six_side hRig hLB hH (Or.inr rfl) (by norm_num)
      hLab hΛ hpJ hN)
    (Subgroup.zpowers_le.mpr hx) hcomp' (ggResHyp_J_ne_K hH)

private theorem ggUnitarySix_label_eq {lab : LargeEvenLabel}
    (htag : lab.tag = .twA) (hr : lab.rank = 5) (hn : lab.n = 1) :
    lab = ⟨.twA, 5, 1⟩ := by
  rcases lab with ⟨t, r, n⟩
  simp only at htag hr hn
  subst htag hr hn
  rfl

theorem ggTBJLeftOn_unitarySix
    (hRig : GGLabelRigidInput) :
    GGTBJLeftOn ggTBJUnitarySixLabel := by
  intro G _ _ p B Bs x L D J y K hH hp hL _hX
  obtain ⟨lab, hΛ, hhas, R, _, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hL
  obtain ⟨htag, hr, hp3, hn⟩ := hP.1
  subst hp3
  have hlab : lab = ⟨.twA, 5, 1⟩ := ggUnitarySix_label_eq htag hr hn
  have hΛ' : LargeEvenInLambda2 (⟨.twA, 5, 1⟩ : LargeEvenLabel) := by
    rw [← hlab]
    exact hΛ
  have hhas' : GGHasLabel (⟨.twA, 5, 1⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L) := by
    rw [← hlab]
    exact hhas
  rcases ggTBJLeft_unitarySix_of_label hRig hH hhas' hΛ' with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem ggTBJNbrOn_unitarySix
    (hRig : GGLabelRigidInput) (hI3 : GGNbrSubcomponentInput)
    (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput) :
    GGTBJNbrOn ggTBJUnitarySixLabel := by
  intro G _ _ p B Bs x L D J y K hH hp hK _hX
  obtain ⟨lab, hΛ, hhas, R, _, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hK
  obtain ⟨htag, hr, hp3, hn⟩ := hP.1
  subst hp3
  have hlab : lab = ⟨.twA, 5, 1⟩ := ggUnitarySix_label_eq htag hr hn
  have hΛ' : LargeEvenInLambda2 (⟨.twA, 5, 1⟩ : LargeEvenLabel) := by
    rw [← hlab]
    exact hΛ
  have hhas' : GGHasLabel (⟨.twA, 5, 1⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K) := by
    rw [← hlab]
    exact hhas
  rcases ggTBJNbr_unitarySix_of_label hRig hI3 hLB hSP hH hhas' hΛ' with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem ggTBJOrderRestSplitAUnitDvd_of_restUnitSix
    (hRig : GGLabelRigidInput) (hI3 : GGNbrSubcomponentInput)
    (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput)
    (h : GGTBJOrderRestSplitAUnitSixInput) : GGTBJOrderRestSplitAUnitDvdInput :=
  GGTBJOrdinaryOutside.of_proved (ggTBJLeftOn_unitarySix hRig)
    (ggTBJNbrOn_unitarySix hRig hI3 hLB hSP) h

end CFSG.StandardType

end
