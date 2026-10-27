module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitary
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitaryDatum
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeNbr
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnola
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy
public import CFSG.LocalAnalysis.StandardType.GGNbrU63
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Q2ProofFinal
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag

theorem four_le_card_ggGamma_of_unitary_six_L_of_cfg
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) (hInn : GGInnerDiagOn Bs L)
    {f : ℕ} (hpq : 3 ∣ 2 ^ f + 1)
    (hLab : GGHasLabel ⟨.twA, 5, f⟩ (L ⧸ Subgroup.center L))
    (hΛ : LargeEvenInLambda2 ⟨.twA, 5, f⟩)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    3 ^ 4 ≤ Nat.card (ggGamma L hN).range := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmark := ggInnerDiagOn_relabel hRig hInn hΛ hLab
  have hM : GGInnerDiagOnLab GGUnitDvd63Label 3 Bs L :=
    largeEvenMarking_mono (fun lab _ _ _ _ _ hP => by
      obtain ⟨rfl, hn, hi⟩ := hP
      exact ⟨⟨⟨rfl, by norm_num, hpq, by norm_num⟩, rfl, rfl⟩,
        Or.inr (Or.inl ⟨by simp [LargeEvenUntwisted], by simp, hpq⟩), hn, hi⟩) hmark
  have h5 := Line63.H5.ggUnitDvd63BstarRankInput_holds
    G 3 B Bs x L D J hcfg hM
  have hS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hxBs : x ∈ Bs := hcfg.2.1.1 hS.2.1
  have hc := card_range_ggGamma_mul_of Nat.prime_three hcfg.tableB_facts.2.1 hxBs
    hS.2.2.1 hS.2.2.2.1.1 hS.2.2.2.2 hN
  have hmul : 3 ^ 4 * 3 ≤ Nat.card (ggGamma L hN).range * 3 := by
    rw [hc]
    exact h5
  exact Nat.le_of_mul_le_mul_right hmul (by norm_num)

theorem four_le_card_ggGamma_of_unitary_six_L
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp 3 B Bs x L D J y K)
    {f : ℕ} (hpq : 3 ∣ 2 ^ f + 1)
    (hLab : GGHasLabel ⟨.twA, 5, f⟩ (L ⧸ Subgroup.center L))
    (hΛ : LargeEvenInLambda2 ⟨.twA, 5, f⟩)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    3 ^ 4 ≤ Nat.card (ggGamma L hN).range :=
  four_le_card_ggGamma_of_unitary_six_L_of_cfg hRig hH.1 hH.2.2.1.1 hpq hLab hΛ hN

theorem four_le_card_ggGamma_of_unitary_six_side
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K X : Subgroup G} (hH : GGResHyp 3 B Bs x L D J y K)
    (hside : X = L ∨ X = K) {f : ℕ} (hpq : 3 ∣ 2 ^ f + 1)
    (hLab : GGHasLabel ⟨.twA, 5, f⟩ (X ⧸ Subgroup.center X))
    (hΛ : LargeEvenInLambda2 ⟨.twA, 5, f⟩)
    (hpJ : 3 ∣ Nat.card J)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) :
    3 ^ 4 ≤ Nat.card (ggGamma X hN).range := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases hside with hXL | hXK
  · subst X
    exact four_le_card_ggGamma_of_unitary_six_L hRig hH hpq hLab hΛ hN
  · subst X
    have hInn : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hH.2.2.2.2.1
    have hmark := ggInnerDiagOn_relabel hRig hInn hΛ hLab
    have hM : GGInnerDiagOnLabel GGNbrInner937U63Label 3 Bs K :=
      largeEvenMarking_mono (fun lab _ _ _ _ _ hP => by
        obtain ⟨rfl, hn, hi⟩ := hP
        exact ⟨⟨⟨rfl, by norm_num, hpq, by norm_num⟩, rfl, rfl⟩, hn, hi⟩) hmark
    by_contra hlt
    push Not at hlt
    exact NbrU63.nbrU63_stepTwo hLB hH.1 hpJ hH.2.2.2.2.1 hN hM hlt
      (NbrU63.nbrU63_stepOne hH.1 hH.2.2.2.2.1 hN hM hlt)

private theorem exists_diagonal_cover_of_unitary_six_core
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K X : Subgroup G} (hH : GGResHyp 3 B Bs x L D J y K)
    {f : ℕ} (hf : f ≠ 1) (hpq : 3 ∣ 2 ^ f + 1)
    (hLab : GGHasLabel ⟨.twA, 5, f⟩ (X ⧸ Subgroup.center X))
    (hΛ : LargeEvenInLambda2 ⟨.twA, 5, f⟩)
    (hInn : GGInnerDiagOn Bs X)
    (hcard : ∀ hN : Bs ≤ Subgroup.normalizer (X : Set G),
      3 ^ 4 ≤ Nat.card (ggGamma X hN).range) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (X : Set G))
      (φ : ↥(unitarySU 2 f F 6) →* X),
      Nat.card F = (2 ^ f) ^ 2 ∧ UnitTB.Model φ ∧
        ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin 6 → F, LineU.ActsDiagU φ a t := by
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
  have hF : Nat.card F = (2 ^ f) ^ 2 := by simpa [pow_two] using hFK
  have hF2 : Nat.card F = 2 ^ (2 * f) := by
    calc Nat.card F = (2 ^ f) ^ 2 := hF
      _ = 2 ^ (f * 2) := by rw [pow_mul]
      _ = 2 ^ (2 * f) := by rw [mul_comm]
  have : CharP F 2 := charP_two_of_card hF2
  obtain ⟨hs, hna, θ, hP⟩ := hQ
  obtain ⟨-, hN, hBsI⟩ := hP
  have hAe : IsElemAbelian 3 (ggGamma X hN).range := ggTD_elemAb hN hH.1.tableB_facts.2.1
  have hAI : ∀ a ∈ (ggGamma X hN).range, ∃ φ ∈
      LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 f F 6))
        (LargeEvenGUSet (Fin 6) F (2 ^ f)),
      ∀ l : X, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta X θ hN b, ggBeta_mem X θ hN hBsI b,
      fun l => ggBeta_ggQuotHom X hN θ b l⟩
  have hcardN : 3 ^ 4 ≤ Nat.card (ggGamma X hN).range := hcard hN
  have hf1 : 1 ≤ f := hΛ.1
  have hcov := LineU.unitaryUniversalCover_holds f 6 F hF (by norm_num)
    (fun h => hf (congrArg Prod.snd h))
  have hk : (ggQuotHom θ).ker ≤ Subgroup.center X := by
    rw [ker_ggQuotHom θ]
  obtain ⟨φ, hφs, hφker, hdiag⟩ := LineU.exists_diagModel hF hf1 (by norm_num)
    Nat.prime_three hpq (by norm_num) hcov (ggQuotHom_surjective θ)
      hk hXperf hAe hAI (by simpa using hcardN)
  exact ⟨F, hField, hFinite, inferInstance, hN, φ, hF,
    ⟨TableBU.unitaryFieldData_of_card hF hf1, hφs, hφker⟩, hdiag⟩

theorem exists_diagonal_cover_of_unitary_six_L
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp 3 B Bs x L D J y K)
    {f : ℕ} (hf : f ≠ 1) (hpq : 3 ∣ 2 ^ f + 1)
    (hLab : GGHasLabel ⟨.twA, 5, f⟩ (L ⧸ Subgroup.center L))
    (hΛ : LargeEvenInLambda2 ⟨.twA, 5, f⟩) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (L : Set G))
      (φ : ↥(unitarySU 2 f F 6) →* L),
      Nat.card F = (2 ^ f) ^ 2 ∧ UnitTB.Model φ ∧
        ∀ a ∈ (ggGamma L hN).range, ∃ t : Fin 6 → F, LineU.ActsDiagU φ a t := by
  have hInn : GGInnerDiagOn Bs L := hH.2.2.1.1
  exact exists_diagonal_cover_of_unitary_six_core hRig hH hf hpq hLab hΛ hInn
    (fun hN => four_le_card_ggGamma_of_unitary_six_L hRig hH hpq hLab hΛ hN)

theorem exists_diagonal_cover_of_unitary_six_side
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K X : Subgroup G} (hH : GGResHyp 3 B Bs x L D J y K)
    (hside : X = L ∨ X = K) {f : ℕ} (hf : f ≠ 1) (hpq : 3 ∣ 2 ^ f + 1)
    (hLab : GGHasLabel ⟨.twA, 5, f⟩ (X ⧸ Subgroup.center X))
    (hΛ : LargeEvenInLambda2 ⟨.twA, 5, f⟩)
    (hpJ : 3 ∣ Nat.card J) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (X : Set G))
      (φ : ↥(unitarySU 2 f F 6) →* X),
      Nat.card F = (2 ^ f) ^ 2 ∧ UnitTB.Model φ ∧
        ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin 6 → F, LineU.ActsDiagU φ a t := by
  have hInn : GGInnerDiagOn Bs X := by
    rcases hside with hXL | hXK
    · rw [hXL]; exact hH.2.2.1.1
    · rw [hXK]; exact hH.2.2.1.2 y K hH.2.2.2.2.1
  exact exists_diagonal_cover_of_unitary_six_core hRig hH hf hpq hLab hΛ hInn
    (fun hN => four_le_card_ggGamma_of_unitary_six_side hRig hLB hH hside hpq hLab hΛ hpJ hN)

theorem exists_corank_two_block_of_unitary_six_side
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K X : Subgroup G} (hH : GGResHyp 3 B Bs x L D J y K)
    (hside : X = L ∨ X = K) {f : ℕ} (hf : f ≠ 1) (hpq : 3 ∣ 2 ^ f + 1)
    (hLab : GGHasLabel ⟨.twA, 5, f⟩ (X ⧸ Subgroup.center X))
    (hΛ : LargeEvenInLambda2 ⟨.twA, 5, f⟩)
    (hJLab : GGHasLabel ⟨.twA, 3, f⟩ (J ⧸ Subgroup.center J)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (X : Set G))
      (φ : ↥(unitarySU 2 f F 6) →* X) (S : Finset (Fin 6)),
      Nat.card F = (2 ^ f) ^ 2 ∧ UnitTB.Model φ ∧ S.card = 4 ∧
        J = (TableBUE.blockSU (K := F) (n := f) S).map (X.subtype.comp φ) ∧
        ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin 6 → F, LineU.ActsDiagU φ a t := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨F, hField, hFinite, hChar, hN, φ, hF, hM, hdiag⟩ :=
    exists_diagonal_cover_of_unitary_six_side hRig hLB hH hside hf hpq hLab hΛ
      ((prime_dvd_card_of_hasLabel_unitary Nat.prime_three (by norm_num)
        (by norm_num) hpq hJLab).trans
        (Subgroup.card_dvd_of_surjective (QuotientGroup.mk'_surjective _)))
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  have hblock : ∃ S : Finset (Fin 6),
      J = (TableBUE.blockSU (K := F) (n := f) S).map (X.subtype.comp φ) ∧ 2 ≤ S.card := by
    rcases hside with hXL | hXK
    · subst X
      exact exists_block_of_diagonal_unitary_component (r := 5) (by norm_num) hΛ.1 hpq
        hH.1.tableB_facts.2.1 hN hF hM hdiag
        (show (D : Set G) ⊆ Bs from hH.1.2.2.1.1.trans hH.1.2.1.1)
        hH.1.2.2.1.2.2.2.2.2.1
    · subst X
      have hpJ : 3 ∣ Nat.card J :=
        (prime_dvd_card_of_hasLabel_unitary Nat.prime_three (by norm_num)
          (by norm_num) hpq hJLab).trans
          (Subgroup.card_dvd_of_surjective (QuotientGroup.mk'_surjective _))
      have hJK : J ≤ K := le_of_ggNbr hLB hH.1.1 hH.1.2.2 hpJ hH.2.2.2.2.1
      have hcomp := ggIsComponentOf_inf_centralizer_nbr hH.1 hH.2.2.2.2.1 hJK
      have hx : x ∈ Bs := hH.1.2.1.1 (hH.1.2.2.1.1 hH.1.2.2.1.2.2.2.1)
      exact exists_block_of_diagonal_unitary_component (r := 5) (by norm_num) hΛ.1 hpq
        hH.1.tableB_facts.2.1 hN hF hM hdiag (Set.singleton_subset_iff.mpr hx) hcomp
  obtain ⟨S, hJblock, hS⟩ := hblock
  have hk : (X.subtype.comp φ).ker ≤ Subgroup.center ↥(unitarySU 2 f F 6) :=
    UnitTB.ker_comp_subtype_le_center hM
  have hJq : Assembly.IsQuasisimple
      ((TableBUE.blockSU (K := F) (n := f) S).map (X.subtype.comp φ)) := by
    rw [← hJblock]
    exact hH.1.2.2.1.2.2.2.2.2.1.2.2
  have hc := card_eq_of_blockSU_label hRig hF hΛ.1 hk hS hJq
    (show LargeEvenInLambda2 ⟨.twA, 3, f⟩ from ⟨hΛ.1, by norm_num, by norm_num⟩)
    (hJblock ▸ hJLab)
  exact ⟨F, hField, hFinite, hChar, hN, φ, S, hF, hM, hc, hJblock, hdiag⟩

theorem ggResTwoNodeSideDatum_unitary_six_side
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K X : Subgroup G} (hH : GGResHyp 3 B Bs x L D J y K)
    (hside : X = L ∨ X = K) {f : ℕ} (hf : f ≠ 1) (hpq : 3 ∣ 2 ^ f + 1)
    (hLab : GGHasLabel ⟨.twA, 5, f⟩ (X ⧸ Subgroup.center X))
    (hΛ : LargeEvenInLambda2 ⟨.twA, 5, f⟩)
    (hJLab : GGHasLabel ⟨.twA, 3, f⟩ (J ⧸ Subgroup.center J)) :
    GGResTwoNodeSideDatum 3 Bs X J := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨F, hField, hFinite, hChar, hN, φ, S, hF, hM, hc, hJblock, hdiag⟩ :=
    exists_corank_two_block_of_unitary_six_side hRig hLB hH hside hf hpq hLab hΛ hJLab
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  exact ggResTwoNodeSideDatum_of_diagonal_unitary_block (r := 5) hF hΛ.1 (by norm_num)
    hpq (by norm_num) hH.1.tableB_facts.2.1 hH.1.2.1.2.2.2 hN hM hdiag S hc hJblock

theorem exists_centralizer_subgroup_of_unitary_six_side
    (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K X : Subgroup G} (hH : GGResHyp 3 B Bs x L D J y K)
    (hside : X = L ∨ X = K) {f : ℕ} (hpq : 3 ∣ 2 ^ f + 1)
    (hJLab : GGHasLabel ⟨.twA, 3, f⟩ (J ⧸ Subgroup.center J)) :
    J ≤ X ∧ Bs ≤ Subgroup.normalizer (J : Set G) ∧
      ∃ C : Subgroup G, C ≤ Bs ∧ IsComponentOf J (X ⊓ Subgroup.centralizer (C : Set G)) := by
  have hNL : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hH.2.2.1.1
  have hBs : IsElemAbelian 3 Bs := hH.1.tableB_facts.2.1
  have hNJ : Bs ≤ Subgroup.normalizer (J : Set G) :=
    GGDichotomy.le_normalizer_stdSub (fun a ha b hb =>
      congrArg Subtype.val (hBs.1.is_comm.comm (⟨a, ha⟩ : Bs) ⟨b, hb⟩))
      hH.1.2.1.1 hH.1.2.2.1 hNL
  rcases hside with hXL | hXK
  · subst X
    have hcomp : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
      hH.1.2.2.1.2.2.2.2.2.1
    exact ⟨hcomp.1.trans inf_le_left, hNJ, D, hH.1.2.2.1.1.trans hH.1.2.1.1, hcomp⟩
  · subst X
    have hpJ : 3 ∣ Nat.card J :=
      (prime_dvd_card_of_hasLabel_unitary Nat.prime_three (by norm_num)
        (by norm_num) hpq hJLab).trans
        (Subgroup.card_dvd_of_surjective (QuotientGroup.mk'_surjective _))
    have hJK : J ≤ K := le_of_ggNbr hLB hH.1.1 hH.1.2.2 hpJ hH.2.2.2.2.1
    have hcomp := ggIsComponentOf_inf_centralizer_nbr hH.1 hH.2.2.2.2.1 hJK
    have hx : x ∈ Bs := hH.1.2.1.1 (hH.1.2.2.1.1 hH.1.2.2.1.2.2.2.1)
    refine ⟨hJK, hNJ, Subgroup.zpowers x, Subgroup.zpowers_le.mpr hx, ?_⟩
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hcomp

end CFSG.StandardType

end
