module

public import CFSG.LocalAnalysis.StandardType.GGQ2TableBI1Tor
public import CFSG.LocalAnalysis.StandardType.GGResILineInputs
public import CFSG.LocalAnalysis.StandardType.GGTPNLineDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDefs
import CFSG.LocalAnalysis.StandardType.GGTBTorAIndUFourTwo
import CFSG.LocalAnalysis.StandardType.GGTBTorCHolds
import CFSG.LocalAnalysis.StandardType.GGTBTorD
import CFSG.LocalAnalysis.StandardType.GGTBTorRelDHolds
import CFSG.LocalAnalysis.StandardType.GGTwA5ThreeFrame
import CFSG.LocalAnalysis.StandardType.GGResIPumpLineA3Rows
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenTwE6Three
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGNbrU63Setup
import CFSG.LocalAnalysis.StandardType.GGQ2TwoNodeI1Rank
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnola
import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallPosWeylSys
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
import CFSG.LocalAnalysis.StandardType.GGCoxeterForkProofBCDExt
import CFSG.LocalAnalysis.StandardType.GGTableBBstar
import CFSG.LocalAnalysis.StandardType.GGStdSubExist
import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallE8
import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallRankDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem exists_ggQ2LDatum_of_markTorW [Fact (Nat.Prime 3)] {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J)
    {X : Subgroup G} {u : G} (hu1 : u ≠ 1)
    (hBX : Bs ⊓ Subgroup.centralizer (X : Set G) = Subgroup.zpowers u)
    {S : ℕ → LargeEvenLabel → Prop} (hMark : GGInnerDiagOnLabel S 3 Bs X) {s N : ℕ}
    (hs3 : 3 ≤ s) {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    (hall : ∀ lab, LargeEvenInLambda2 lab → S 3 lab →
      LargeEvenLabelAll lab fun R _ I _ => GGTorusTorW 3 s 3 N C M R I)
    (hr : ∀ hN : Bs ≤ Subgroup.normalizer (X : Set G), 3 ^ s ≤ Nat.card (ggGamma X hN).range)
    {lab' : LargeEvenLabel} (hlab' : GGQ2LabelWeyl lab' M) :
    ∃ D : GGQ2LDatum 3 Bs X u, D.Shape := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := hMark
  obtain ⟨R₀, iR₀, I₀, F₀, hQ₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ₀, hS, -⟩ := hQ₀
  obtain ⟨R, iR, I, F, hQ, hWtor⟩ := largeEvenRawDatum_exists (hall lab hlab hS _ hraw)
  obtain ⟨-, -, θ, -, hN, hBsI⟩ := hQ
  have hTB := ggTorusTBGroup_of_card hcfg hs3 hperf θ hN
    (fun b hb => ggLAut_mem_of_induces X θ hN hBsI hb) (hr hN)
  obtain ⟨-, hBs, -, -, -⟩ := hcfg.tableB_facts
  obtain ⟨D', -, -, hsh⟩ := exists_ggQ2LDatum_of_torData (p := 3) (by norm_num) hBs
    hcfg.2.1.2.2.2 hu1 hBX hN hM hC (hWtor ↥X (ggQuotHom θ) (ggGamma X hN).range hTB) hlab'
  exact ⟨D', hsh⟩

theorem largeEvenLabelAll_twA4_two_torW :
    LargeEvenLabelAll ⟨.twA, 4, 1⟩ fun R _ I _ =>
      GGTorusTorW 3 3 3 4 (CartanMatrix.A 4) (CoxeterMatrix.A 4) R I := by
  have hE : ggTorEnn 3 ⟨.twA, 4, 1⟩ = 1 := by norm_num [ggTorEnn]
  have hM : ggTorM ⟨.twA, 4, 1⟩ = 3 := by norm_num [ggTorM]
  have hΛ : LargeEvenInLambda2 ⟨.twA, 4, 1⟩ := by
    unfold LargeEvenInLambda2
    norm_num
  have h := ggTBTorAInd_holds 3 (by norm_num) (by norm_num) ⟨.twA, 4, 1⟩ hΛ
    (Or.inr rfl) (by norm_num) (by rw [hM])
  simpa [hE, hM] using h

theorem largeEvenLabelAll_twA5_two_torW :
    LargeEvenLabelAll ⟨.twA, 5, 1⟩ fun R _ I _ =>
      GGTorusTorW 3 4 3 5 (CartanMatrix.A 5) (CoxeterMatrix.A 5) R I := by
  simpa using ggTorusTorW_uni_six_three_label_all (f := 1) (by norm_num) (by norm_num)

theorem largeEvenLabelAll_C4_two_torW :
    LargeEvenLabelAll ⟨.C, 4, 1⟩ fun R _ I _ =>
      GGTorusTorW 3 3 3 4 (CartanMatrix.C 4) (CoxeterMatrix.B 4) R I := by
  have hE : ggTorEnn 3 ⟨.C, 4, 1⟩ = 1 := by norm_num [ggTorEnn]
  have hM : ggTorMpm 3 ⟨.C, 4, 1⟩ = 3 := by norm_num [ggTorMpm]
  have hΛ : LargeEvenInLambda2 ⟨.C, 4, 1⟩ := by
    unfold LargeEvenInLambda2
    norm_num
  have h := ggTBTorC_holds 3 (by norm_num) (by norm_num) ⟨.C, 4, 1⟩ hΛ
    (Or.inr rfl) (by norm_num)
  simpa [hE, hM] using h

theorem largeEvenLabelAll_D4_two_torW :
    LargeEvenLabelAll ⟨.D, 4, 1⟩ fun R _ I _ =>
      GGTorusTorW 3 3 3 4 (CartanMatrix.D 4) (ggCoxeterMatrixD 4) R I := by
  have hE : ggTorEnn 3 ⟨.D, 4, 1⟩ = 1 := by norm_num [ggTorEnn]
  have hM : ggTorMpm 3 ⟨.D, 4, 1⟩ = 3 := by norm_num [ggTorMpm]
  have hΛ : LargeEvenInLambda2 ⟨.D, 4, 1⟩ := by
    unfold LargeEvenInLambda2
    norm_num
  have h := ggTBTorD_holds 3 (by norm_num) (by norm_num) ⟨.D, 4, 1⟩ hΛ
    (Or.inl ⟨rfl, Or.inr ⟨by norm_num, by norm_num⟩⟩)
  simpa [hE, hM] using h

theorem largeEvenLabelAll_D5_two_torW :
    LargeEvenLabelAll ⟨.D, 5, 1⟩ fun R _ I _ =>
      GGTorusTorW 3 4 3 4 (CartanMatrix.B 4) (CoxeterMatrix.B 4) R I := by
  have hM : ggTorMpm 3 ⟨.D, 5, 1⟩ = 3 := by norm_num [ggTorMpm]
  have hΛ : LargeEvenInLambda2 ⟨.D, 5, 1⟩ := by
    unfold LargeEvenInLambda2
    norm_num
  have h := ggTBTorRelD_holds 3 (by norm_num) (by norm_num) ⟨.D, 5, 1⟩ hΛ
    (Or.inl ⟨rfl, by norm_num, by norm_num⟩)
  simpa [hM] using h

theorem ggTablePRow_three_A3_two {labJ labX : LargeEvenLabel}
    (hJ : ggResLineJLabel .A3 labJ) (hJn : labJ.n = 1) (hrow : GGTablePRow 3 labJ labX) :
    labX = ⟨.twA, 4, 1⟩ ∨ labX = ⟨.twA, 5, 1⟩ ∨ labX = ⟨.C, 4, 1⟩ ∨ labX = ⟨.D, 4, 1⟩ ∨
      labX = ⟨.D, 5, 1⟩ := by
  rcases ggTablePRow_three_A3 hJ hrow with ⟨-, -, hdvd, -⟩ | ⟨-, -, hdvd, -⟩ |
    ⟨-, -, hdvd, hX⟩ | ⟨-, -, hdvd, hX⟩
  · rw [hJn] at hdvd
    norm_num at hdvd
  · rw [hJn] at hdvd
    norm_num at hdvd
  · rcases hX with h | h | h | h | h | ⟨-, h3n⟩
    · exact Or.inl (by rw [h, hJn])
    · exact Or.inr (Or.inl (by rw [h, hJn]))
    · exact Or.inr (Or.inr (Or.inl (by rw [h, hJn])))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [h, hJn]))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (by rw [h, hJn]))))
    · exfalso
      omega
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [hX, hJn]))))

@[expose] def GGQ2TwA3TwoLabel (lab : LargeEvenLabel) : Prop :=
  lab = ⟨.twA, 4, 1⟩ ∨ lab = ⟨.twA, 5, 1⟩ ∨ lab = ⟨.C, 4, 1⟩ ∨ lab = ⟨.D, 4, 1⟩ ∨
    lab = ⟨.D, 5, 1⟩

theorem GGQ2TwA3TwoLabel.inLambda2 {lab : LargeEvenLabel} (h : GGQ2TwA3TwoLabel lab) :
    LargeEvenInLambda2 lab := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> simp [LargeEvenInLambda2]

theorem exists_ggQ2LDatum_of_twA3Label
    [Fact (Nat.Prime 3)] (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J)
    {X : Subgroup G} {u : G} (hu1 : u ≠ 1)
    (hBX : Bs ⊓ Subgroup.centralizer (X : Set G) = Subgroup.zpowers u)
    (hInn : GGInnerDiagOn Bs X) {labX : LargeEvenLabel} (hlab : GGQ2TwA3TwoLabel labX)
    (hhasX : GGHasLabel labX (↥X ⧸ Subgroup.center ↥X))
    (hr : ∀ hN : Bs ≤ Subgroup.normalizer (X : Set G), 3 ^ 4 ≤ Nat.card (ggGamma X hN).range) :
    ∃ M : GGQ2LDatum 3 Bs X u, M.Shape := by
  have hmk := ggInnerDiagOn_relabel hRig hInn hlab.inLambda2 hhasX
  have hMark : GGInnerDiagOnLabel (fun _ lab => lab = labX) 3 Bs X :=
    largeEvenMarking_mono (fun lab R _ I F θ hP => ⟨hP.1, hP.2⟩) hmk
  have hr3 : ∀ hN : Bs ≤ Subgroup.normalizer (X : Set G),
      3 ^ 3 ≤ Nat.card (ggGamma X hN).range :=
    fun hN => (Nat.pow_le_pow_right (by norm_num) (by norm_num)).trans (hr hN)
  rcases hlab with rfl | rfl | rfl | rfl | rfl
  · exact exists_ggQ2LDatum_of_markTorW hcfg hu1 hBX hMark le_rfl
      (CFSG.TwoNodeSmall.pws_ggIsWeylMatrix_A 4 (by norm_num)) (ggIntCartan_A 4)
      (fun lab _ h => h ▸ largeEvenLabelAll_twA4_two_torW) hr3 (lab' := ⟨.twA, 4, 1⟩)
      ⟨Equiv.refl _, rfl⟩
  · exact exists_ggQ2LDatum_of_markTorW hcfg hu1 hBX hMark (by norm_num)
      (CFSG.TwoNodeSmall.pws_ggIsWeylMatrix_A 5 (by norm_num)) (ggIntCartan_A 5)
      (fun lab _ h => h ▸ largeEvenLabelAll_twA5_two_torW) hr (lab' := ⟨.twA, 5, 1⟩)
      ⟨Equiv.refl _, rfl⟩
  · exact exists_ggQ2LDatum_of_markTorW hcfg hu1 hBX hMark le_rfl
      (CFSG.TwoNodeSmall.pws_ggIsWeylMatrix_B 4 (by norm_num)) (ggIntCartan_C 4)
      (fun lab _ h => h ▸ largeEvenLabelAll_C4_two_torW) hr3 (lab' := ⟨.C, 4, 1⟩)
      ⟨Equiv.refl _, rfl⟩
  · exact exists_ggQ2LDatum_of_markTorW hcfg hu1 hBX hMark le_rfl
      (CFSG.TwoNodeSmall.pws_ggIsWeylMatrix_D 4 (by norm_num)) (ggIntCartan_D 4)
      (fun lab _ h => h ▸ largeEvenLabelAll_D4_two_torW) hr3 (lab' := ⟨.D, 4, 1⟩)
      ⟨Equiv.refl _, rfl⟩
  · exact exists_ggQ2LDatum_of_markTorW hcfg hu1 hBX hMark (by norm_num)
      (CFSG.TwoNodeSmall.pws_ggIsWeylMatrix_B 4 (by norm_num)) (ggIntCartan_B 4)
      (fun lab _ h => h ▸ largeEvenLabelAll_D5_two_torW) hr (lab' := ⟨.B, 4, 1⟩)
      ⟨Equiv.refl _, rfl⟩

theorem exists_ggQ2LDatum_of_twA3Row
    [Fact (Nat.Prime 3)] (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J)
    {X : Subgroup G} {u : G} (hu1 : u ≠ 1)
    (hBX : Bs ⊓ Subgroup.centralizer (X : Set G) = Subgroup.zpowers u)
    (hInn : GGInnerDiagOn Bs X) {labJ labX : LargeEvenLabel} (hJ : ggResLineJLabel .A3 labJ)
    (hJn : labJ.n = 1) (hhasX : GGHasLabel labX (↥X ⧸ Subgroup.center ↥X))
    (hrow : GGTablePRow 3 labJ labX)
    (hr : ∀ hN : Bs ≤ Subgroup.normalizer (X : Set G), 3 ^ 4 ≤ Nat.card (ggGamma X hN).range) :
    ∃ M : GGQ2LDatum 3 Bs X u, M.Shape :=
  exists_ggQ2LDatum_of_twA3Label hRig hcfg hu1 hBX hInn (ggTablePRow_three_A3_two hJ hJn hrow)
    hhasX hr

theorem ggQ2_nbrDatum_twA3_of_tpLine
    [Fact (Nat.Prime 3)] (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) (hTP : GGNbrTablePNbrInputI1On GGRegimeLine) {G : Type} [Group G]
    [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hI1 : GGQTwoI1 Bs D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr 3 B x D J y K) (hcard : Nat.card Bs = 3 ^ 5) {labJ : LargeEvenLabel}
    (hΛJ : LargeEvenInLambda2 labJ) (hJ : ggResLineJLabel .A3 labJ) (hJn : labJ.n = 1)
    (hhasJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J)) :
    ∃ M : GGQ2LDatum 3 Bs K y, M.Shape := by
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  have hIDA : GGInnerDiagAll 3 B Bs x L D J := hS.1.2.2.1
  have hInnK : GGInnerDiagOn Bs K := hIDA.2 y K hnb
  have hBK : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y :=
    ggQ2_inf_centralizer_nbr_eq_of_I1 hLB hP hS.1 hI1 hnb
  have hy1 : y ≠ 1 := hnb.1.2.2.1
  have hI1' : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D := fun b hb =>
    hI1 b hb.1 fun j hj => (Subgroup.mem_centralizer_iff.mp hb.2 j hj).symm
  obtain ⟨labK₀, hΛK₀, hhasK₀, -⟩ := largeEvenMarking_exists_hasLabel hInnK
  have hreg : GGRegimeLine 3 (Nat.card Bs) labJ labK₀ := ⟨rfl, hcard.le, .A3, hJ⟩
  obtain ⟨labJ', labK', hΛJ', -, hrow, hhasJ', hhasK'⟩ :=
    hTP G 3 B Bs x L D J y K hcfg hIDA.1 hInnK hnb hI1' labJ labK₀ hΛJ hΛK₀ hreg hhasJ hhasK₀
  have hiso := hRig labJ labJ' _ hΛJ hΛJ' hhasJ hhasJ'
  have hJn' : labJ'.n = 1 := by
    have hrk : labJ.rank = 3 := by
      rcases hJ with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> exact h
    rcases hiso.n_cases with h | ⟨-, h⟩ | h <;> omega
  have hy3 : orderOf y = 3 := by
    have hyBs : y ∈ Bs := (hBK.ge (Subgroup.mem_zpowers y)).1
    exact orderOf_eq_prime (hcfg.tableB_facts.2.1.2 y hyBs) hy1
  have hr : ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G),
      3 ^ 4 ≤ Nat.card (ggGamma K hN).range := by
    intro hN
    have h1 := NbrU63.card_range_ggGamma_mul_card_inf hN
    rw [hBK, Nat.card_zpowers, hy3, hcard] at h1
    have h2 : Nat.card (ggGamma K hN).range * 3 = 3 ^ 4 * 3 := by
      rw [h1]
      norm_num
    exact (Nat.eq_of_mul_eq_mul_right (by norm_num) h2).ge
  exact exists_ggQ2LDatum_of_twA3Row hRig hcfg hy1 hBK hInnK (ggResLineJLabel_of_iso hJ hiso) hJn'
    hhasK' hrow hr

@[expose] def GGQ2TablePAtLTwA3 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting 3 B Bs x L D J → GGQTwoI1 Bs D J → Nat.card Bs ≤ 3 ^ 5 →
    ∀ {y : G} {K : Subgroup G}, GGNbr 3 B x D J y K →
    ∀ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ → labJ.tag = .twA → labJ.rank = 3 →
      3 ∣ 2 ^ labJ.n + 1 → GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) →
      ∃ labL : LargeEvenLabel, GGQ2TwA3TwoLabel labL ∧ GGHasLabel labL (↥L ⧸ Subgroup.center ↥L)

theorem ggQ2_LDatum_twA3_of_tablePAtL
    [Fact (Nat.Prime 3)] (hRig : GGLabelRigidInput) (hPL : GGQ2TablePAtLTwA3) {G : Type}
    [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hI1 : GGQTwoI1 Bs D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr 3 B x D J y K) (hcard : Nat.card Bs = 3 ^ 5) {labJ : LargeEvenLabel}
    (hΛJ : LargeEvenInLambda2 labJ) (htJ : labJ.tag = .twA) (hrJ : labJ.rank = 3)
    (hpq : 3 ∣ 2 ^ labJ.n + 1) (hhasJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J)) :
    ∃ M : GGQ2LDatum 3 Bs L x, M.Shape := by
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  obtain ⟨labL, hlab, hhasL⟩ := hPL hS hI1 hcard.le hnb labJ hΛJ htJ hrJ hpq hhasJ
  obtain ⟨hp3, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hSS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  refine exists_ggQ2LDatum_of_twA3Label hRig hcfg hSS.2.2.1
    (inf_centralizer_eq_zpowers_of_elemAbelian hp3 hBs hxBs hSS.2.2.1 hLx hSS.2.2.2.2)
    hS.1.2.2.1.1 hlab hhasL fun hN => ?_
  have hmul := card_range_ggGamma_mul_of hp3 hBs hxBs hSS.2.2.1 hLx hSS.2.2.2.2 hN
  rw [hcard] at hmul
  norm_num at hmul ⊢
  omega

end CFSG.StandardType

end
