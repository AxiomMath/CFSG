module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeTransport
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeQuotient
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitarySix
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitarySixCover
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitarySixReduced
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Q2ProofOne
public import CFSG.LocalAnalysis.StandardType.GGF4AutWeyl
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeRowDimUnitary
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeRowDimReduced
public import CFSG.LocalAnalysis.StandardType.GGTCJHolds
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkComp
public import CFSG.LocalAnalysis.StandardType.GGResE6DepUnitaryTwo
public import CFSG.LocalAnalysis.StandardType.GGResFixedWeylCentralizer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.Line63.H5
  CFSG.ClassicalGroups.UnitaryFlag

theorem ggAutomizer_redMk_eq
    {G : Type} [Group G] [Finite G] {X Bs H : Subgroup G}
    (hBs : IsElemAbelian 3 Bs) (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hHN : H ≤ Subgroup.normalizer (X : Set G))
    (hBH : Bs ≤ Subgroup.normalizer (H : Set G)) :
    ggAutomizer ((H.subgroupOf (Subgroup.normalizer (X : Set G))).map (redMk X))
      (redMkB hN).range =
        (ggAutomizer H Bs).map
          (MulAut.congr (MonoidHom.ofInjective (redMkB_injective hN hBs))).toMonoidHom := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let R := Subgroup.normalizer (X : Set G)
  let Br : Subgroup R := Bs.subgroupOf R
  let Hr : Subgroup R := H.subgroupOf R
  let Bb : Subgroup (RedGrp X) := (redMkB hN).range
  have hBmap : Br.map R.subtype = Bs := Subgroup.map_subgroupOf_eq_of_le hN
  have hHmap : Hr.map R.subtype = H := Subgroup.map_subgroupOf_eq_of_le hHN
  have hBrp : IsPGroup 3 Br := (isPGroup_of_isElemAbelian hBs).comap_subtype
  have hBrH : Br ≤ Subgroup.normalizer (Hr : Set R) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro a
    exact (Subgroup.mem_normalizer_iff.mp (hBH hb)) a
  have hBb : Br.map (redMk X) = Bb := by
    ext q
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b, hb⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨⟨b, hN b.2⟩, b.2, rfl⟩
  let eI : Br ≃* Bs := (Br.equivMapOfInjective R.subtype R.subtype_injective).trans
    (MulEquiv.subgroupCongr hBmap)
  let eb : Bs ≃* Bb := MonoidHom.ofInjective (redMkB_injective hN hBs)
  have her : ∀ b : Br, ((eI.trans eb) b : RedGrp X) = redMk X b := fun _ => rfl
  have hpker : ¬ 3 ∣ Nat.card (redMk X).ker := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (isPGroup_ker_redMk X)
    rw [hj]
    intro h
    exact (by norm_num : ¬ (3 : ℕ) ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h)
  have hr := ggAutomizer_map_of_coprime_card_ker hpker hBrp hBrH hBb (eI.trans eb) her
  have hi := F4AutWeyl.ggAutomizer_map_eq R.subtype_injective Hr Br hBmap
  rw [hHmap] at hi
  have he : (MulAut.congr eb).toMonoidHom.comp (MulAut.congr eI).toMonoidHom =
      (MulAut.congr (eI.trans eb)).toMonoidHom := by
    ext a b
    simp [MulAut.congr_apply, MulEquiv.trans_apply]
  change ggAutomizer (Hr.map (redMk X)) Bb = (ggAutomizer H Bs).map
    (MulAut.congr eb).toMonoidHom
  rw [hi, Subgroup.map_map]
  change ggAutomizer (Hr.map (redMk X)) Bb = (ggAutomizer Hr Br).map
    ((MulAut.congr eb).toMonoidHom.comp (MulAut.congr eI).toMonoidHom)
  rw [he]
  exact hr

theorem ggResTwoNodeSideDatum_of_redMk
    {G : Type} [Group G] [Finite G] {X Bs J : Subgroup G}
    (hBs : IsElemAbelian 3 Bs) (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hJX : J ≤ X) (hBJ : Bs ≤ Subgroup.normalizer (J : Set G))
    (hD : GGResTwoNodeSideDatum 3 (redMkB hN).range (redMkL X).range
      ((J.subgroupOf (Subgroup.normalizer (X : Set G))).map (redMk X))) :
    GGResTwoNodeSideDatum 3 Bs X J := by
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
  exact (GGResTwoNodeSideDatum.transport_iff
    (MonoidHom.ofInjective (redMkB_injective hN hBs)) hXaut hJaut).mpr hD

theorem exists_block_cover_of_unitary_six_two_side
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K X : Subgroup G} (hH : GGResHyp 3 B Bs x L D J y K)
    (hside : X = L ∨ X = K)
    (hLab : GGHasLabel ⟨.twA, 5, 1⟩ (X ⧸ Subgroup.center X))
    (hΛ : LargeEvenInLambda2 ⟨.twA, 5, 1⟩)
    (hJLab : GGHasLabel ⟨.twA, 3, 1⟩ (J ⧸ Subgroup.center J)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (X : Set G))
      (hNbar : (redMkB hN).range ≤
        Subgroup.normalizer ((redMkL X).range : Set (RedGrp X)))
      (φ : ↥(unitarySU 2 1 F 6) →* (redMkL X).range) (S : Finset (Fin 6)),
      Nat.card F = 4 ∧ UnitTB.Model φ ∧ S.card = 4 ∧
        ((J.subgroupOf (Subgroup.normalizer (X : Set G))).map (redMk X)) =
          (TableBUE.blockSU (K := F) (n := 1) S).map (((redMkL X).range).subtype.comp φ) ∧
        (∀ a ∈ (ggGamma (redMkL X).range hNbar).range,
          ∃ t : Fin 6 → F, LineU.ActsDiagU φ a t) ∧
        J ≤ X ∧ Bs ≤ Subgroup.normalizer (J : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hInn : GGInnerDiagOn Bs X := by
    rcases hside with hXL | hXK
    · rw [hXL]; exact hH.2.2.1.1
    · rw [hXK]; exact hH.2.2.1.2 y K hH.2.2.2.2.1
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
  have hcard := four_le_card_ggGamma_of_unitary_six_side hRig hLB hH hside
    (by norm_num) hLab hΛ
    ((prime_dvd_card_of_hasLabel_unitary Nat.prime_three (by norm_num)
      (by norm_num) (by norm_num : 3 ∣ 2 ^ 1 + 1) hJLab).trans
      (Subgroup.card_dvd_of_surjective (QuotientGroup.mk'_surjective _))) hN
  obtain ⟨hNbar, φ, hM, hdiag⟩ := exists_diagonal_cover_of_unitary_six_two_red
    hF hXperf θ hN hBs hBsI hcard
  obtain ⟨hJX, hBJ, C, hCB, hJC⟩ := exists_centralizer_subgroup_of_unitary_six_side
    hLB hH hside (by norm_num) hJLab
  obtain ⟨S, hS, hJblock⟩ := exists_blockSU_unitarySix_reduced hRig hF hBs hN
    hCB hJC hJLab hNbar φ hM hdiag
  exact ⟨F, hField, hFinite, inferInstance, hN, hNbar, φ, S,
    hF, hM, hS, hJblock, hdiag, hJX, hBJ⟩

theorem ggResTwoNodeSideDatum_unitary_six_two_side
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K X : Subgroup G} (hH : GGResHyp 3 B Bs x L D J y K)
    (hside : X = L ∨ X = K)
    (hLab : GGHasLabel ⟨.twA, 5, 1⟩ (X ⧸ Subgroup.center X))
    (hΛ : LargeEvenInLambda2 ⟨.twA, 5, 1⟩)
    (hJLab : GGHasLabel ⟨.twA, 3, 1⟩ (J ⧸ Subgroup.center J)) :
    GGResTwoNodeSideDatum 3 Bs X J := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨F, hField, hFinite, hChar, hN, hNbar, φ, S, hF, hM, hS,
    hJblock, hdiag, hJX, hBJ⟩ :=
      exists_block_cover_of_unitary_six_two_side hRig hLB hH hside hLab hΛ hJLab
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  have hd : GGResTwoNodeSideDatum 3 (redMkB hN).range (redMkL X).range
      ((J.subgroupOf (Subgroup.normalizer (X : Set G))).map (redMk X)) :=
    ggResTwoNodeSideDatum_of_diagonal_unitary_block (p := 3) (r := 5) (f := 1)
      (by simpa using hF) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (isElemAbelian_redB hN hH.1.tableB_facts.2.1)
      (redSC hN hH.1.tableB_facts.2.1 hH.1.2.1.2.2.2)
      hNbar hM hdiag S hS hJblock
  exact ggResTwoNodeSideDatum_of_redMk hH.1.tableB_facts.2.1 hN hJX hBJ hd

theorem ggResTwoNodeSideDatum_unitary_six_side_all
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K X : Subgroup G} (hH : GGResHyp 3 B Bs x L D J y K)
    (hside : X = L ∨ X = K) {f : ℕ} (hpq : 3 ∣ 2 ^ f + 1)
    (hLab : GGHasLabel ⟨.twA, 5, f⟩ (X ⧸ Subgroup.center X))
    (hΛ : LargeEvenInLambda2 ⟨.twA, 5, f⟩)
    (hJLab : GGHasLabel ⟨.twA, 3, f⟩ (J ⧸ Subgroup.center J)) :
    GGResTwoNodeSideDatum 3 Bs X J := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hf : f = 1
  · subst f
    exact ggResTwoNodeSideDatum_unitary_six_two_side hRig hLB hH hside hLab hΛ hJLab
  · exact ggResTwoNodeSideDatum_unitary_six_side hRig hLB hH hside hf hpq hLab hΛ hJLab

theorem GGResHyp.exists_twA3_label_of_unitary_six_L_ne_one
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hD : GGResLineJDatum 3 Bs J .A3)
    {f : ℕ} (hf : f ≠ 1) (hpq : 3 ∣ 2 ^ f + 1)
    (hLab : GGHasLabel ⟨.twA, 5, f⟩ (L ⧸ Subgroup.center L))
    (hΛ : LargeEvenInLambda2 ⟨.twA, 5, f⟩) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ ggResLineJLabel .A3 lab ∧
      GGHasLabel lab (J ⧸ Subgroup.center J) := by
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  obtain ⟨F, hField, hFinite, hChar, hN, φ, hF, hM, hdiag⟩ :=
    exists_diagonal_cover_of_unitary_six_L hRig hH hf hpq hLab hΛ
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  exact hH.exists_twA3_label_of_unitaryModel_L hD hpq hΛ hM hdiag

private theorem ggResLineJLabel_A3_of_iso_twA31 {lab : LargeEvenLabel}
    (h : GGLabelIso ⟨.twA, 3, 1⟩ lab) (hpq : 3 ∣ 2 ^ 1 + 1) :
    ggResLineJLabel .A3 lab := by
  unfold ggResLineJLabel
  rcases h with rfl | hBC | hDA | hAD | hD3A3 | hA3D3 | hD2A1 | hA1D2
  · exact Or.inr ⟨Or.inl rfl, rfl, hpq⟩
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  · obtain ⟨-, h2⟩ := hA3D3
    rw [h2]
    exact Or.inr ⟨Or.inr rfl, rfl, by simpa using hpq⟩
  · simp_all
  · simp_all

theorem GGResHyp.hasLabel_twA3_of_unitary_six_two_L
  {G : Type} [Group G] [Finite G]
  {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
  (hH : GGResHyp 3 B Bs x L D J y K)
  (hD : GGResLineJDatum 3 Bs J .A3)
  (hLab : GGHasLabel ⟨.twA, 5, 1⟩ (L ⧸ Subgroup.center L))
  (hΛ : LargeEvenInLambda2 ⟨.twA, 5, 1⟩) :
  GGHasLabel ⟨.twA, 3, 1⟩ (J ⧸ Subgroup.center J) := by
  classical
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hInn : GGInnerDiagOn Bs L := hH.2.2.1.1
  have hmark := ggInnerDiagOn_relabel hRig hInn hΛ hLab
  obtain ⟨hLperf, lab, hlab, hraw⟩ := hmark
  obtain ⟨R₀, _, I₀, F₀, _, _, _, hP₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨heq, -, -⟩ := hP₀
  subst lab
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨F, hField, hFinite, hFK, hQ⟩ := hraw
  let : Field F := hField
  let : Finite F := hFinite
  have hF4 : Nat.card F = 4 := by simpa using hFK
  have : CharP F 2 := charP_two_of_card (by simpa using hF4 : Nat.card F = 2 ^ 2)
  obtain ⟨hs, hna, θ, hP⟩ := hQ
  obtain ⟨-, hN, hBI⟩ := hP
  have hBs : IsElemAbelian 3 Bs := hH.1.tableB_facts.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hγcard : 3 ^ 4 ≤ Nat.card (ggGamma L hN).range :=
    four_le_card_ggGamma_of_unitary_six_L hRig hH (by norm_num) hLab hΛ hN
  obtain ⟨hNbar, φ, hM, hdiag⟩ :=
    exists_diagonal_cover_of_unitary_six_two_red hF4 hLperf θ hN hBs hBI hγcard
  let NX : Subgroup G := Subgroup.normalizer (L : Set G)
  let Xbar : Subgroup (RedGrp L) := (redMkL L).range
  let Bbar : Subgroup (RedGrp L) := (redMkB hN).range
  let Jbar : Subgroup (RedGrp L) := (J.subgroupOf NX).map (redMk L)
  have hJcomp : CFSG.Assembly.IsComponentOf J
      (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hH.1.2.2.1.2.2.2.2.2.1
  have hJX : J ≤ L := hJcomp.1.trans inf_le_left
  have hCB : D ≤ Bs := hH.1.2.2.1.1.trans hH.1.2.1.1
  obtain ⟨-, labJ, -, -, -, hΛJ, -, hHasJ⟩ :=
    ggNbr_label_J_of_tcj TCJ.ggTCJKnown_holds hH.1 hH.2.2.2.2.1
  obtain ⟨S, hS2, hJblock, hJq, hJbarLabJ⟩ :=
    exists_block_unitarySix_reduced hF4 hBs hN hCB hJcomp hHasJ hNbar φ hM hdiag
  have hNJ : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  have hJperf : commutator ↥J = ⊤ := hJcomp.2.2.1
  obtain ⟨hBJ, -⟩ := card_range_ggGamma_eq_redMk hN hJX hNJ hJperf
  obtain ⟨χ, hχsurj, hχker, hχdiag⟩ :=
    exists_diagCover_blockSU (f := 1) (d := 6) hM hNbar hdiag le_rfl S hJblock hBJ
  let hMχ : UnitTB.Model χ := ⟨hM.field, hχsurj, hχker⟩
  have hχdiagRange : ∀ a ∈ (ggGamma Jbar hBJ).range,
      ∃ t : Fin S.card → F, LineU.ActsDiagU χ a t := by
    intro a ha
    obtain ⟨b, rfl⟩ := ha
    exact hχdiag b
  have hd : 4 ≤ S.card := by
    by_contra hlt
    push Not at hlt
    have hk1 : 1 ≤ S.card := by omega
    have hk3 : S.card ≤ 3 := by omega
    haveI : Group.IsSolvable ↥(unitarySU 2 1 F S.card) :=
      WitSU.isSolvable_unitarySU_two_one hM.field hk1 hk3
    haveI : Group.IsSolvable ↥Jbar :=
      Group.isSolvable_of_surjective (f := χ) hχsurj
    haveI : Group.IsPerfect ↥Jbar := Group.isPerfect_def.mpr hJq.1
    haveI hsimple : IsSimpleGroup (↥Jbar ⧸ Subgroup.center ↥Jbar) := hJq.2
    haveI : Nontrivial (↥Jbar ⧸ Subgroup.center ↥Jbar) := inferInstance
    haveI : Nontrivial ↥Jbar :=
      (QuotientGroup.mk_surjective (s := Subgroup.center ↥Jbar)).nontrivial
    exact (Group.IsPerfect.not_isSolvable ↥Jbar) inferInstance
  have hBsbar : IsElemAbelian 3 Bbar := isElemAbelian_redB hN hBs
  have hSCbar : ∀ g ∈ Subgroup.centralizer (Bbar : Set (RedGrp L)),
      g ^ 3 = 1 → g ∈ Bbar := redSC hN hBs hSC
  have hF1 : Nat.card F = (2 ^ 1) ^ 2 := by rw [hF4]; norm_num
  have hcardFact := card_ggAutomizer_eq_factorial_of_unitaryModel
    (p := 3) (n := 1) (d := S.card) (F := F) (G := RedGrp L)
    hBsbar hSCbar hBJ hMχ hF1 (by norm_num) (by norm_num) hd hχdiagRange
  let eBs : ↥Bs ≃* ↥Bbar := MonoidHom.ofInjective (redMkB_injective hN hBs)
  have hJaut : ggAutomizer Jbar Bbar =
      (ggAutomizer J Bs).map (MulAut.congr eBs).toMonoidHom := by
    have h := ggAutomizer_redMk_eq hBs hN (hJX.trans Subgroup.le_normalizer) hNJ
    simpa [Jbar, Bbar, eBs] using h
  have hcard24 : Nat.card (ggAutomizer Jbar Bbar) = 24 := by
    rw [hJaut, Subgroup.card_map_of_injective (MulAut.congr eBs).injective,
      ggAutomizer_card_of_lineJDatum_A3 (p := 3) rfl hD]
  have hfact : S.card.factorial = 24 := by
    rw [← hcardFact]
    exact hcard24
  have hS4 : S.card = 4 := by
    have h4 : S.card.factorial = Nat.factorial 4 := by
      rw [hfact]; norm_num
    exact (Nat.factorial_inj (by omega : 1 < S.card)).mp h4
  have hJbarLabTwA : GGHasLabel ⟨.twA, 3, 1⟩
      (↥Jbar ⧸ Subgroup.center ↥Jbar) := by
    have h := ggHasLabel_of_unitaryModel hMχ (by omega : 3 ≤ S.card) (by
      intro hdm
      have := congrArg Prod.fst hdm
      omega)
    have hd1 : S.card - 1 = 3 := by omega
    simpa [hd1] using h
  have hΛtwA : LargeEvenInLambda2 ⟨.twA, 3, 1⟩ := by
    unfold LargeEvenInLambda2
    norm_num
  have hIso : GGLabelIso labJ ⟨.twA, 3, 1⟩ :=
    hRig labJ ⟨.twA, 3, 1⟩ (↥Jbar ⧸ Subgroup.center ↥Jbar)
      hΛJ hΛtwA hJbarLabJ hJbarLabTwA
  exact largeEvenRawDatum_of_ggLabelIso hIso hHasJ

theorem GGResHyp.exists_twA3_label_of_unitary_six_L_allfields
  {G : Type} [Group G] [Finite G]
  {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
  (hH : GGResHyp 3 B Bs x L D J y K)
  (hD : GGResLineJDatum 3 Bs J .A3)
  {f : ℕ} (hpq : 3 ∣ 2 ^ f + 1)
  (hLab : GGHasLabel ⟨.twA, 5, f⟩ (L ⧸ Subgroup.center L))
  (hΛ : LargeEvenInLambda2 ⟨.twA, 5, f⟩) :
  ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ ggResLineJLabel .A3 lab ∧
    GGHasLabel lab (J ⧸ Subgroup.center J) := by
  classical
  by_cases hf : f = 1
  · subst f
    have hJLab := hH.hasLabel_twA3_of_unitary_six_two_L hD hLab hΛ
    have hΛtwA : LargeEvenInLambda2 ⟨.twA, 3, 1⟩ := by
      unfold LargeEvenInLambda2
      norm_num
    exact ⟨⟨.twA, 3, 1⟩, hΛtwA,
      ggResLineJLabel_A3_of_iso_twA31 (Or.inl rfl) hpq, hJLab⟩
  · exact GGResHyp.exists_twA3_label_of_unitary_six_L_ne_one hH hD hf hpq hLab hΛ

theorem GGResHyp.exists_twA3_label_of_large_unitary_L_allfields
  {G : Type} [Group G] [Finite G]
  {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
  (hH : GGResHyp 3 B Bs x L D J y K)
  (hD : GGResLineJDatum 3 Bs J .A3)
  {r f : ℕ} (hr : 4 ≤ r)
  (hpq : 3 ∣ 2 ^ f + 1)
  (hLab : GGHasLabel ⟨.twA, r, f⟩ (L ⧸ Subgroup.center L))
  (hΛ : LargeEvenInLambda2 ⟨.twA, r, f⟩) :
  ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ ggResLineJLabel .A3 lab ∧
    GGHasLabel lab (J ⧸ Subgroup.center J) := by
  by_cases hr5 : r = 5
  · subst r
    exact GGResHyp.exists_twA3_label_of_unitary_six_L_allfields hH hD hpq hLab hΛ
  · exact GGResHyp.exists_twA3_label_of_large_unitary_L hH hD hr hr5 hpq hLab hΛ

theorem GGResHyp.unitary_six_two_L_facts
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twA, 5, 1⟩) 3 Bs L) :
    (∀ b : ↥Bs, (∀ φ ∈ ggAutomizer J Bs, φ b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G)) ∧
      24 ≤ Nat.card (ggAutomizer J Bs) ∧ Nat.card Bs ≤ 3 ^ 6 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  unfold GGInnerDiagOnLabel at hMark
  obtain ⟨hLperf, lab, hΛlab, hraw⟩ := hMark
  obtain ⟨R₀, _, I₀, F₀, _, _, _, hP₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨hlabeq, -, -⟩ := hP₀
  subst lab
  have hLab : GGHasLabel ⟨.twA, 5, 1⟩ (↥L ⧸ Subgroup.center ↥L) := by
    refine largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨-, -, θ, -, -, -⟩
    exact ⟨θ⟩
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨F, hField, hFinite, hFK, hQ⟩ := hraw
  let : Field F := hField
  let : Finite F := hFinite
  have hF4 : Nat.card F = 4 := by simpa using hFK
  have : CharP F 2 := charP_two_of_card (by simpa using hF4 : Nat.card F = 2 ^ 2)
  obtain ⟨hs, hna, θ, hP⟩ := hQ
  obtain ⟨-, hN, hBI⟩ := hP
  have hBs : IsElemAbelian 3 Bs := hH.1.tableB_facts.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hγcard : 3 ^ 4 ≤ Nat.card (ggGamma L hN).range :=
    four_le_card_ggGamma_of_unitary_six_L hRig hH (by norm_num) hLab hΛlab hN
  obtain ⟨hNbar, φ, hM, hdiag⟩ :=
    exists_diagonal_cover_of_unitary_six_two_red hF4 hLperf θ hN hBs hBI hγcard
  let NX : Subgroup G := Subgroup.normalizer (L : Set G)
  let Xbar : Subgroup (RedGrp L) := (redMkL L).range
  let Bbar : Subgroup (RedGrp L) := (redMkB hN).range
  let Jbar : Subgroup (RedGrp L) := (J.subgroupOf NX).map (redMk L)
  have hJcomp : CFSG.Assembly.IsComponentOf J
      (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hH.1.2.2.1.2.2.2.2.2.1
  have hJX : J ≤ L := hJcomp.1.trans inf_le_left
  have hCB : D ≤ Bs := hH.1.2.2.1.1.trans hH.1.2.1.1
  obtain ⟨-, labJ, -, -, -, hΛJ, -, hHasJ⟩ :=
    ggNbr_label_J_of_tcj TCJ.ggTCJKnown_holds hH.1 hH.2.2.2.2.1
  obtain ⟨S, hS2, hJblock, hJq, hJbarLabJ⟩ :=
    exists_block_unitarySix_reduced hF4 hBs hN hCB hJcomp hHasJ hNbar φ hM hdiag
  have hNJ : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  have hJperf : commutator ↥J = ⊤ := hJcomp.2.2.1
  obtain ⟨hBJ, _hcardGamma⟩ := card_range_ggGamma_eq_redMk hN hJX hNJ hJperf
  obtain ⟨χ, hχsurj, hχker, hχdiag⟩ :=
    exists_diagCover_blockSU (f := 1) (d := 6) hM hNbar hdiag le_rfl S hJblock hBJ
  let hMχ : UnitTB.Model χ := ⟨hM.field, hχsurj, hχker⟩
  have hχdiagRange : ∀ a ∈ (ggGamma Jbar hBJ).range,
      ∃ t : Fin S.card → F, LineU.ActsDiagU χ a t := by
    intro a ha
    obtain ⟨b, rfl⟩ := ha
    exact hχdiag b
  have hd : 4 ≤ S.card := by
    by_contra hlt
    push Not at hlt
    have hk1 : 1 ≤ S.card := by omega
    have hk3 : S.card ≤ 3 := by omega
    haveI : Group.IsSolvable ↥(unitarySU 2 1 F S.card) :=
      WitSU.isSolvable_unitarySU_two_one hM.field hk1 hk3
    haveI : Group.IsSolvable ↥Jbar :=
      Group.isSolvable_of_surjective (f := χ) hχsurj
    haveI : Group.IsPerfect ↥Jbar := Group.isPerfect_def.mpr hJq.1
    haveI hsimple : IsSimpleGroup (↥Jbar ⧸ Subgroup.center ↥Jbar) := hJq.2
    haveI : Nontrivial (↥Jbar ⧸ Subgroup.center ↥Jbar) := inferInstance
    haveI : Nontrivial ↥Jbar :=
      (QuotientGroup.mk_surjective (s := Subgroup.center ↥Jbar)).nontrivial
    exact (Group.IsPerfect.not_isSolvable ↥Jbar) inferInstance
  have hd3 : 3 ≤ S.card := by omega
  have hBsbar : IsElemAbelian 3 Bbar := isElemAbelian_redB hN hBs
  have hSCbar : ∀ g ∈ Subgroup.centralizer (Bbar : Set (RedGrp L)),
      g ^ 3 = 1 → g ∈ Bbar := redSC hN hBs hSC
  let eBs : ↥Bs ≃* ↥Bbar := MonoidHom.ofInjective (redMkB_injective hN hBs)
  have hJaut : ggAutomizer Jbar Bbar =
      (ggAutomizer J Bs).map (MulAut.congr eBs).toMonoidHom := by
    have h := ggAutomizer_redMk_eq hBs hN (hJX.trans Subgroup.le_normalizer) hNJ
    simpa [Jbar, Bbar, eBs] using h
  have hF1 : Nat.card F = (2 ^ 1) ^ 2 := by simpa using hF4
  have hcardFact := card_ggAutomizer_eq_factorial_of_unitaryModel
    (p := 3) (n := 1) (d := S.card) (F := F) (G := RedGrp L)
    hBsbar hSCbar hBJ hMχ hF1 (by norm_num) (by norm_num) hd hχdiagRange
  have hcardJ : Nat.card (ggAutomizer J Bs) = S.card.factorial := by
    rw [hJaut, Subgroup.card_map_of_injective (MulAut.congr eBs).injective] at hcardFact
    exact hcardFact
  have h24 : 24 ≤ Nat.card (ggAutomizer J Bs) := by
    rw [hcardJ]
    calc 24 = Nat.factorial 4 := by norm_num
      _ ≤ Nat.factorial S.card := Nat.factorial_le hd
  have hXimage : (L.subgroupOf NX).map (redMk L) = Xbar := by
    dsimp [Xbar]
    rw [redMkL, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hpack := card_range_ggGamma_eq_redMk hN le_rfl hN hLperf
  change ∃ hbar : Bbar ≤ Subgroup.normalizer
    (((L.subgroupOf NX).map (redMk L)) : Set (RedGrp L)),
    Nat.card (ggGamma L hN).range =
      Nat.card (ggGamma ((L.subgroupOf NX).map (redMk L)) hbar).range at hpack
  rw [hXimage] at hpack
  obtain ⟨_, hcardL'⟩ := hpack
  have hcapLbar : Nat.card (ggGamma Xbar hNbar).range ≤ 3 ^ 5 := by
    apply LineU.card_le_of_actsDiagU (f := 1) hM.field (by norm_num) hM.surj hM.ker
      (ggGamma Xbar hNbar).range
    · intro a ha
      obtain ⟨b, rfl⟩ := ha
      have hb3 : b ^ 3 = 1 := Subtype.ext (hBsbar.2 b b.2)
      rw [← map_pow, hb3, map_one]
    · exact hdiag
  have hcapL : Nat.card (ggGamma L hN).range ≤ 3 ^ 5 := by
    rw [hcardL']
    exact hcapLbar
  obtain ⟨hp, _, hxBs, hLx, _⟩ := hH.1.tableB_facts
  have hSstar : LargeEvenSStar 3 B x L := hH.1.1.2.2.2.2.2.2.1
  have hmul := card_range_ggGamma_mul_of hp hBs hxBs hSstar.2.2.1 hLx
    hSstar.2.2.2.2 hN
  have hcapBs : Nat.card Bs ≤ 3 ^ 6 := by
    rw [← hmul]
    calc Nat.card (ggGamma L hN).range * 3 ≤ 3 ^ 5 * 3 :=
        Nat.mul_le_mul_right 3 hcapL
      _ = 3 ^ 6 := by norm_num
  refine ⟨?_, h24, hcapBs⟩
  intro b hb
  let bbar : ↥Bbar := ⟨redMkB hN b, ⟨b, rfl⟩⟩
  have hfixbar : ∀ ψ ∈ ggAutomizer Jbar Bbar, ψ bbar = bbar := by
    intro ψ hψ
    rw [hJaut] at hψ
    obtain ⟨φ, hφ, rfl⟩ := hψ
    change (MulAut.congr eBs) φ bbar = bbar
    have hsymm : eBs.symm bbar = b := by
      apply eBs.injective
      rw [MulEquiv.apply_symm_apply]
      rfl
    change eBs (φ (eBs.symm bbar)) = bbar
    rw [hsymm, hb φ hφ]
    rfl
  have hcenbar : (bbar : RedGrp L) ∈
      Subgroup.centralizer (Jbar : Set (RedGrp L)) :=
    ggUnitaryModel_fix_mem_centralizer (K := F) (n := 1) (d := S.card) (p := 3)
      hBJ hBsbar hSCbar hMχ hd3 hχdiagRange bbar hfixbar
  letI : Group.IsPerfect ↥J := Group.isPerfect_def.mpr hJperf
  let bJ : ↥(Subgroup.normalizer (J : Set G)) := ⟨(b : G), hNJ b.2⟩
  let α : MulAut ↥J := J.normalizerMonoidHom bJ
  have hαcoe : ∀ jj : ↥J, ((α jj : ↥J) : G) =
      (b : G) * (jj : G) * (b : G)⁻¹ := by
    intro jj
    exact Subgroup.normalizerMonoidHom_apply_apply_coe J bJ jj
  have hcentral : ∀ jj : ↥J, jj⁻¹ * α jj ∈ Subgroup.center ↥J := by
    intro jj
    let bN : NX := ⟨(b : G), hN b.2⟩
    let jN : NX := ⟨(jj : G), hJX.trans Subgroup.le_normalizer jj.2⟩
    have hjbar : redMk L jN ∈ Jbar :=
      Subgroup.mem_map.mpr ⟨jN, Subgroup.mem_subgroupOf.mpr jj.2, rfl⟩
    have hcomm := (Subgroup.mem_centralizer_iff.mp hcenbar) (redMk L jN) hjbar
    have hbred : redMk L (jN⁻¹ * (bN * jN * bN⁻¹)) = 1 := by
      have hbN : redMk L bN = (bbar : RedGrp L) := rfl
      simp only [map_mul, map_inv, hbN]
      rw [← hcomm]
      group
    have hz : ((jN⁻¹ * (bN * jN * bN⁻¹) : NX) : G) ∈ twoCenter L :=
      (redMk_eq_one_iff L (jN⁻¹ * (bN * jN * bN⁻¹))).mp hbred
    rw [Subgroup.mem_center_iff]
    intro j'
    apply Subtype.ext
    have hzval : ((jj⁻¹ * α jj : ↥J) : G) =
        ((jN⁻¹ * (bN * jN * bN⁻¹) : NX) : G) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hαcoe]
      rfl
    change (j' : G) * ((jj⁻¹ * α jj : ↥J) : G) =
      ((jj⁻¹ * α jj : ↥J) : G) * (j' : G)
    rw [hzval]
    exact (hz.2.1 (j' : G) (hJX j'.2)).symm
  have hαone : α = 1 := by
    have h :=
      CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
        α.toMonoidHom hcentral
    have hpoint : ∀ jj : ↥J, α jj = (1 : MulAut ↥J) jj := by
      intro jj
      simpa using congrArg (fun f : ↥J →* ↥J => f jj) h
    exact MulEquiv.ext hpoint
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  have hαj : α ⟨j, hj⟩ = ⟨j, hj⟩ := by
    have := congrArg (fun f : MulAut ↥J => f ⟨j, hj⟩) hαone
    simpa using this
  have hval : (b : G) * (j : G) * (b : G)⁻¹ = (j : G) := by
    have h1 := congrArg (fun x : ↥J => (x : G)) hαj
    rw [hαcoe] at h1
    simpa using h1
  have hbj : (b : G) * (j : G) = (j : G) * (b : G) := by
    calc (b : G) * (j : G) =
        ((b : G) * (j : G) * (b : G)⁻¹) * (b : G) := by group
      _ = (j : G) * (b : G) := by rw [hval]
  exact hbj.symm


theorem GGResHyp.fix_mem_centralizer_J_of_unitary_six_two_L
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twA, 5, 1⟩) 3 Bs L) :
    ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer J Bs, φ b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G) :=
  (hH.unitary_six_two_L_facts hMark).1

theorem GGResHyp.twoNode_L_of_unitary_six_two_L_exactThree_E6_K
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twA, 5, 1⟩) 3 Bs L)
    (hD : GGResLeviDatumExact3 3 Bs K J L ggSelAny ggTypLE6) :
    GGResRowAt ggRowTwoNode 3 J L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨lab, hΛ, hLab, R, hR, I, F, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hMark
  have heq : lab = ⟨.twA, 5, 1⟩ := hP.1
  subst lab
  have hJLab := hH.hasLabel_twA3_of_unitary_six_two_L
    (e6_exactThree_GGResLineJDatum_A3 hD) hLab hΛ
  refine ⟨⟨.twA, 3, 1⟩, ⟨.twA, 5, 1⟩, ?_, hΛ, hJLab, hLab, ?_⟩
  · unfold LargeEvenInLambda2
    norm_num
  · unfold ggRowTwoNode
    exact Or.inr (Or.inl ⟨rfl, by norm_num, by norm_num, rfl⟩)

theorem GGResHyp.not_exactThree_L_A_of_unitary_six_two_L_card
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twA, 5, 1⟩) 3 Bs L)
    (h24 : 24 ≤ Nat.card ↥(ggAutomizer J Bs))
    : ¬ GGResLeviDatumExact3 3 Bs L J K ggSelAny (ggTypLADvd 3) := by
  intro hD
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS3, hA1, hA3, hWML, hCLL, hWMK, hCKK, htyp, hlin, hrefl, hpairL, hpairK, hsel,
    ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hdel, hclosJ⟩ := hD
  let := i1
  let := i2
  let := i3
  let := i4
  let := i5
  let := i6
  obtain ⟨hA, -⟩ := htyp
  obtain ⟨n, e, hn, he⟩ := hA
  have h720 : Nat.card ↥(ggAutomizer L Bs) = 720 :=
    original_unitSix_card720 hH rfl hMark
  have hcardML : Nat.card ML.Group = (n + 1).factorial := by
    rw [he]
    exact (Nat.card_congr
      (CoxeterMatrix.reindexGroupEquiv (CoxeterMatrix.A n) e).toEquiv).trans
      (l05nK3a_card_coxeterA n)
  have hcardML720 : Nat.card ML.Group = 720 :=
    (Nat.card_congr fL.toEquiv).trans h720
  have hfac : (n + 1).factorial = 720 := hcardML.symm.trans hcardML720
  have hn5 : n = 5 := by
    have h6 : n + 1 = 6 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hle : (n + 1).factorial ≤ Nat.factorial 5 := Nat.factorial_le (by omega)
        rw [hfac] at hle
        norm_num at hle
      · have hle : Nat.factorial 7 ≤ (n + 1).factorial := Nat.factorial_le (by omega)
        rw [hfac] at hle
        norm_num at hle
    omega
  subst ML
  have hcardAJ : Nat.card ↥(ggAutomizer J Bs) = (n - 3 + 1).factorial :=
    ggRes_typeA_deletedS_card_automizer (r := n) (k := 3) (by omega) e S hS3 hdel
      (fun i => φ (Sum.inl i)) fL hfL hclosJ
  have h6 : Nat.card ↥(ggAutomizer J Bs) = 6 := by
    rw [hcardAJ, hn5]
    norm_num
  omega

theorem GGResHyp.not_exactThree_K_A_of_unitary_six_two_L_bounds
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hfwd : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer J Bs, φ b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G))
    (h24 : 24 ≤ Nat.card ↥(ggAutomizer J Bs))
    (hBs6 : Nat.card Bs ≤ 3 ^ 6)
    : ¬ GGResLeviDatumExact3 3 Bs K J L ggSelAny (ggTypLADvd 3) := by
  intro hD
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS3, hA1, hA3, hWML, hCLL, hWMK, hCKK, htyp, hlin, hrefl, hpairL, hpairK, hsel,
    ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hdel, hclosJ⟩ := hD
  let := i1
  let := i2
  let := i3
  let := i4
  let := i5
  let := i6
  obtain ⟨hA, h3dvd⟩ := htyp
  obtain ⟨n, e, hn, he⟩ := hA
  have hΛn : Fintype.card Λ = n := by
    simpa using (Fintype.card_congr e).symm
  have h3dvd' : 3 ∣ n + 1 := by
    simpa [hΛn] using h3dvd
  have haxis : Matrix.rank (CL.map (Int.castRingHom (ZMod 3))) + 1 ≤
      Module.finrank (ZMod 3) V :=
    ggResK_rank_core_add_one hH (fun i w => hlin (Sum.inl i) w) hpairL hCLL.1 hclosL
  obtain ⟨hdim, -, -, -, -, -⟩ :=
    ggRes_exactThree_singular_chart_of_axis_bound hH.1 ι
      (fun i => φ (Sum.inl i)) (fun i => h (Sum.inl i)) (fun i => α (Sum.inl i))
      hWML hCLL (fun i w => hlin (Sum.inl i) w) (fun i => hrefl (Sum.inl i)) hpairL
      haxis S hS3 hclosJ hfwd
  letI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hcardBs : Nat.card Bs = 3 ^ n := by
    calc Nat.card Bs = Nat.card V := card_eq_of_ggLin ι
      _ = 3 ^ Module.finrank (ZMod 3) V :=
        (FiniteField.pow_finrank_eq_natCard 3 V).symm
      _ = 3 ^ n := by rw [hdim, hΛn]
  have hn6 : n ≤ 6 := by
    have hle : 3 ^ n ≤ 3 ^ 6 := by simpa [hcardBs] using hBs6
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hle
  have hJne : ggAutomizer J Bs ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at h24
    omega
  have hT : Nonempty {i : Λ // i ∉ S} := by
    by_contra hne
    have hrange : Set.range (fun j : {i : Λ // i ∉ S} => φ (Sum.inl j)) = ∅ := by
      rw [Set.range_eq_empty_iff]
      exact not_nonempty_iff.mp hne
    apply hJne
    rw [hclosJ, hrange, Subgroup.closure_empty]
  have hTcard : 1 ≤ Fintype.card {i : Λ // i ∉ S} := by
    have hpos := Fintype.card_pos_iff.mpr hT
    omega
  have hcomp : Fintype.card {i : Λ // i ∉ S} = Fintype.card Λ - S.card := by
    have hsub : Fintype.card {i : Λ // i ∈ S} = S.card := by
      rw [Fintype.card_subtype]
      simp
    change Fintype.card {i : Λ // i ∉ S} = Fintype.card Λ - S.card
    rw [Fintype.card_subtype_compl (fun i : Λ => i ∈ S), hsub]
  have hΛ3 : 3 < Fintype.card Λ := by omega
  have hn3 : 3 < n := by omega
  subst ML
  have hcardAJ : Nat.card ↥(ggAutomizer J Bs) = (n - 3 + 1).factorial :=
    ggRes_typeA_deletedS_card_automizer (r := n) (k := 3) hn3 e S hS3 hdel
      (fun i => φ (Sum.inl i)) fL hfL hclosJ
  have h24' : 24 ≤ (n - 3 + 1).factorial := by
    rw [← hcardAJ]
    exact h24
  have hn6ge : 6 ≤ n := by
    by_contra hlt
    have hn5 : n ≤ 5 := by omega
    have hle1 : n - 3 + 1 ≤ 3 := by omega
    have hle2 : (n - 3 + 1).factorial ≤ Nat.factorial 3 := Nat.factorial_le hle1
    norm_num at hle2
    omega
  have hn_eq : n = 6 := by omega
  rw [hn_eq] at h3dvd'
  norm_num at h3dvd'


section UnitarySixTwoExactThree


theorem GGResHyp.not_exactThree_L_of_unitary_six_two_L
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twA, 5, 1⟩) 3 Bs L)
    : ¬ GGResLeviDatumExact3 3 Bs L J K ggSelAny ggTypAny := by
  intro hD
  have hfacts := hH.unitary_six_two_L_facts hMark
  obtain ⟨hfwd, h24, -⟩ := hfacts
  obtain ⟨hsplit, -⟩ := ggResExact3_typed_dichotomy_L_of_fixed hH hfwd hD
  rcases hsplit with hA | ⟨-, hE6⟩
  · exact GGResHyp.not_exactThree_L_A_of_unitary_six_two_L_card hH hMark h24 hA
  · exact original_unitSix_not_exactThree_E6_L hH rfl hMark hE6

theorem GGResHyp.not_exactThree_K_A_of_unitary_six_two_L
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twA, 5, 1⟩) 3 Bs L)
    : ¬ GGResLeviDatumExact3 3 Bs K J L ggSelAny (ggTypLADvd 3) := by
  intro hD
  obtain ⟨hfwd, h24, hBs6⟩ := hH.unitary_six_two_L_facts hMark
  exact GGResHyp.not_exactThree_K_A_of_unitary_six_two_L_bounds hH hfwd h24 hBs6 hD

theorem GGResHyp.not_exactThree_either_of_unitary_six_two_L
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twA, 5, 1⟩) 3 Bs L)
    (hrow : ¬ GGResRowAt ggRowTwoNode 3 J L) :
    ¬ (GGResLeviDatumExact3 3 Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 3 Bs K J L ggSelAny ggTypAny) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rintro (hL | hK)
  · exact hH.not_exactThree_L_of_unitary_six_two_L hMark hL
  · have hfwd := hH.fix_mem_centralizer_J_of_unitary_six_two_L hMark
    obtain ⟨hsplit, -⟩ := ggResExact3_typed_dichotomy_K_base_of_fixed hH hfwd hK
    rcases hsplit with hA | ⟨-, hE6⟩
    · exact hH.not_exactThree_K_A_of_unitary_six_two_L hMark hA
    · exact hrow (hH.twoNode_L_of_unitary_six_two_L_exactThree_E6_K hMark hE6)

theorem GGResHyp.not_exactThree_either_of_unitary_L_allfields
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hU : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1) p Bs L)
    (hntwo : ¬ GGResRowAt ggRowTwoNode p J L)
    (hnSU2 : ¬ GGResRowAt ggRowSUCorank2 p J L)
    (hnSU3 : ¬ GGResRowAt ggRowSUCorank3 p J L) :
    ¬ (GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) := by
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hU
  obtain ⟨R, _, I, F, _, _, θ, hpred, _, _⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨htag, hrank, hpn⟩ := hpred
  by_cases hn : lab.n = 1
  · by_cases hr : lab.rank = 5
    · have hp3 : p = 3 := by
        have hdiv : p ∣ 3 := by simpa [hn] using hpn
        exact (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp hdiv
      subst p
      have heq : lab = ⟨.twA, 5, 1⟩ := by cases lab; simp_all
      apply hH.not_exactThree_either_of_unitary_six_two_L _ hntwo
      refine ⟨hperf, lab, hΛ, ?_⟩
      exact largeEvenRawDatum_mono (fun R _ I F hq => by
        obtain ⟨hs, hna, θ, -, hN, hact⟩ := hq
        exact ⟨hs, hna, θ, heq, hN, hact⟩) hraw
    · apply hH.not_exactThree_either_of_unitary_label_qTwo _ hntwo hnSU2 hnSU3
      refine ⟨hperf, lab, hΛ, ?_⟩
      exact largeEvenRawDatum_mono (fun R _ I F hq => by
        obtain ⟨hs, hna, θ, -, hN, hact⟩ := hq
        exact ⟨hs, hna, θ, ⟨htag, hrank, hn, hr, hpn⟩, hN, hact⟩) hraw
  · apply hH.not_exactThree_either_of_unitary_label_qGeFour
    refine ⟨hperf, lab, hΛ, ?_⟩
    have hn2 : 2 ≤ lab.n := by have := hΛ.1; omega
    exact largeEvenRawDatum_mono (fun R _ I F hq => by
      obtain ⟨hs, hna, θ, -, hN, hact⟩ := hq
      exact ⟨hs, hna, θ, ⟨htag, hrank, hn2, hpn⟩, hN, hact⟩) hraw

end UnitarySixTwoExactThree

end CFSG.StandardType

end
