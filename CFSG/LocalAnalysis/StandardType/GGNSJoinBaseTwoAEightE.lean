module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueSix
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1WeylE
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
import CFSG.LocalAnalysis.StandardType.GGFrameEndJoin
import CFSG.LocalAnalysis.StandardType.GGTableBRank
import CFSG.LocalAnalysis.StandardType.GGSpNbrKGMark
import CFSG.LocalAnalysis.StandardType.GGSecFiveBWeylInfType
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoRowE
import CFSG.LocalAnalysis.StandardType.GGForkA8NotRefl
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrOfEnnola
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseTwoE

public section

namespace CFSG.StandardType

open CFSG.Assembly FrameRoute

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
  {𝒦 : Finset (Subgroup G)}

theorem GGSecFiveRouteCfg.weylAtJoin_of_reindex (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) {ι' : Type} {M' : CoxeterMatrix ι'}
    (σ : ι' ≃ ι) (hM : M = M'.reindex σ) : GGSecFiveWeylAtJoin p B Bs x L D J M' := by
  subst hM
  by_cases h𝒦 : 𝒦.Nonempty
  · exact ⟨𝒦, hcfg.2.2.2.1, h𝒦,
      GGWeylOfType.of_reindex (M := M') (e := σ) (A := ggAutomizerJoin L Bs 𝒦) ⟨e, hpres.2⟩⟩
  · rw [Finset.not_nonempty_iff_eq_empty] at h𝒦
    subst h𝒦
    exact (hcfg.weylAt_of_card_le_one (by simp) e hpres).of_reindex.toJoin

theorem GGConfig.innerDiagOnLabel_torusRank
    (hconf : GGConfig 3 B Bs x L D J) {P : ℕ → LargeEvenLabel → Prop}
    (hP : ∀ lab, P 3 lab → lab.tag = .twA ∧ lab.n = 1) (h : GGInnerDiagOnLabel P 3 Bs L) :
    GGInnerDiagOnLabel (fun p lab => P p lab ∧
      ggUnitaryTorusRank 3 (lab.rank + 1) + 1 ≤ LargeEvenTwoLocalRank 3 G) 3 Bs L := by
  obtain ⟨-, -, -, hLx, -⟩ := hconf.tableB_facts
  have hS : LargeEvenSStar 3 B x L := hconf.1.2.2.2.2.2.2.1
  refine largeEvenMarking_mono_labelAll
    (P' := fun lab R _ _ _ => lab.n = 1 → lab.tag = .twA →
      GGTorusLift 3 (ggUnitaryTorusRank 3 (lab.rank + 1)) R)
    (fun lab hΛ => largeEvenLabelAll_imp fun hn1 => largeEvenLabelAll_imp fun htag =>
      largeEvenLabelAll_torusLift_twA hΛ htag Nat.prime_three (by rw [hn1]; norm_num))
    ?_ h
  intro lab R _ I F θ _ hPr hlift
  obtain ⟨htag, hn1⟩ := hP lab hPr.1
  exact ⟨⟨hPr.1, succ_le_twoLocalRank_of_torusLift Nat.prime_three hLx (hS.1.1.2 x hS.2.1)
    hS.2.2.1 h.1 θ (hlift hn1 htag)⟩, hPr.2⟩

theorem GGSecFiveRouteCfg.false_of_twA8_E7
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (hb1 : GGFrameTBNumerologyInput)
    (hb1' : GGFrameTBVacuousInput) (hrig : GGLabelRigidInput)
    (hR : GGSecFiveRestHyp 3 B Bs x L D J) (hW : GGSecFiveWeylCase 3 B Bs x D J)
    (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    (hJ : GGSecFiveWeylAtJoin 3 B Bs x L D J CoxeterMatrix.E₇)
    (hm : LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .twA ∧ lab.rank = 8 ∧ lab.n = 1)) :
    False := by
  classical
  obtain ⟨lab₁, hΛ₁, hhas₁, R₁, _, I₁, F₁, θ₁, hP₁⟩ :=
    largeEvenMarking_exists_hasLabel
      ((ggFrameEndLabelJoinInput_of_tableB hTBF hWI hb1 hb1' G B Bs x L D J hR hW hq).1 hJ)
  obtain ⟨lab₂, hΛ₂, hhas₂, R₂, _, I₂, F₂, θ₂, hP₂⟩ := largeEvenMarking_exists_hasLabel hm
  have hiso := hrig lab₁ lab₂ (↥L ⧸ Subgroup.center ↥L) hΛ₁ hΛ₂ hhas₁ hhas₂
  obtain ⟨t₁, l₁, n₁⟩ := lab₁
  obtain ⟨t₂, l₂, n₂⟩ := lab₂
  obtain rfl := hP₂.1
  obtain rfl := hP₂.2.1
  obtain rfl := hP₂.2.2
  rcases hP₁.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2 <;>
    simp [GGLabelIso] at hiso

theorem GGSecFiveRouteCfg.lt_bstar_of_twA8_E8
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (hb1 : GGFrameTBNumerologyInput)
    (hb1' : GGFrameTBVacuousInput) (hrig : GGLabelRigidInput) (hPU : GGPumpupInput)
    (hO : GGOuterThreeRankInput) (hTCJ : GGTCJKnown)
    (hR : GGSecFiveRestHyp 3 B Bs x L D J) (hW : GGSecFiveWeylCase 3 B Bs x D J)
    (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    (hJ : GGSecFiveWeylAtJoin 3 B Bs x L D J CoxeterMatrix.E₈)
    (hm : LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .twA ∧ lab.rank = 8 ∧ lab.n = 1)) :
    B < Bs := by
  have hcard := (fsPoint_unitaryNine hTBF hWI hb1 hb1' hrig hPU hO hTCJ hR hW hq hJ hm).1
  refine lt_of_le_of_ne hR.1.2.1.1 fun hBBs => ?_
  have hpos : 0 < Nat.card B := Nat.card_pos
  rw [← hBBs] at hcard
  omega

private theorem rowP_ESU_three_imp {lab : LargeEvenLabel}
    (h : ggRowP_ESU 3 lab ∧ lab.n = 1 ∧ 3 ∣ lab.rank + 1 ∧ lab.rank ≠ 5) :
    lab.tag = .twA ∧ lab.n = 1 := by
  obtain ⟨⟨⟨ht, -⟩ | ⟨hd, hr⟩, -⟩, hn1, hdvd, -⟩ := h
  · exact ⟨ht, hn1⟩
  · rw [hr] at hdvd
    exact absurd hdvd (by norm_num)

private theorem rowP_ESU_three_imp' {lab : LargeEvenLabel}
    (h : (ggRowP_ESU 3 lab ∧ lab.n = 1 ∧ 3 ∣ lab.rank + 1 ∧ lab.rank ≠ 5) ∧
      ggUnitaryTorusRank 3 (lab.rank + 1) + 1 ≤ LargeEvenTwoLocalRank 3 G) :
    lab.tag = .twA ∧ 3 ≤ lab.rank ∧ lab.n = 1 ∧ 3 ∣ lab.rank + 1 ∧ lab.rank ≠ 5 ∧
      ggUnitaryTorusRank 3 (lab.rank + 1) + 1 ≤ LargeEvenTwoLocalRank 3 G := by
  obtain ⟨⟨⟨ht, h3le⟩ | ⟨hd, hr3⟩, -⟩, hn1, hdvd, hne5⟩ := h.1
  · exact ⟨ht, h3le, hn1, hdvd, hne5, h.2⟩
  · rw [hr3] at hdvd
    exact absurd hdvd (by norm_num)

private theorem eq_five_of_torusRank {l r : ℕ} (h3 : 3 ≤ l) (hdvd : 3 ∣ l + 1)
    (hrank : ggUnitaryTorusRank 3 (l + 1) + 1 ≤ r) (hr : r ≤ 6) : l = 5 := by
  unfold ggUnitaryTorusRank at hrank
  rw [if_pos hdvd] at hrank
  obtain ⟨k, hk⟩ := hdvd
  omega

private theorem rank_eq_eight_of_torusRank {l r n : ℕ} (h3 : 3 ≤ l) (hdvd : 3 ∣ l + 1)
    (hne5 : l ≠ 5) (hrank : ggUnitaryTorusRank 3 (l + 1) + 1 ≤ r) (hr : r ≤ n) (hn : n ≤ 8) :
    l = 8 := by
  unfold ggUnitaryTorusRank at hrank
  rw [if_pos hdvd] at hrank
  obtain ⟨k, hk⟩ := hdvd
  omega

omit [Finite G] in
private theorem innerDiagOnLabel_labQTwo_of_rowP
    (h : GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ 3 ∣ lab.rank + 1 ∧
      lab.rank ≠ 5) 3 Bs L) : GGInnerDiagOnLabel GGLabQTwo 3 Bs L :=
  h.mono' fun lab hl => by
    have hn1 : lab.n = 1 := hl.2.1
    unfold GGLabQTwo
    omega

private theorem marking_eight_of_torusRank {n : ℕ}
    (h' : GGInnerDiagOnLabel (fun p lab => (ggRowP_ESU p lab ∧ lab.n = 1 ∧ 3 ∣ lab.rank + 1 ∧
      lab.rank ≠ 5) ∧ ggUnitaryTorusRank 3 (lab.rank + 1) + 1 ≤ LargeEvenTwoLocalRank 3 G)
      3 Bs L)
    (hr : LargeEvenTwoLocalRank 3 G ≤ n) (hn : n ≤ 8) :
    LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .twA ∧ lab.rank = 8 ∧ lab.n = 1) := by
  refine (h'.mono' (T := fun _ lab => lab.tag = .twA ∧ lab.rank = 8 ∧ lab.n = 1) ?_).toMarking
  intro lab hl
  obtain ⟨⟨⟨⟨ht, h3le⟩ | ⟨hd, hr3⟩, -⟩, hn1, hdvd, hne5⟩, hrank⟩ := hl
  · exact ⟨ht, rank_eq_eight_of_torusRank h3le hdvd hne5 hrank hr hn, hn1⟩
  · rw [hr3] at hdvd
    exact absurd hdvd (by norm_num)

private theorem largeEvenTwoLocalRank_le_of_weyl
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) (hTBF : GGTBFixInput)
    (hWI : GGNbrInnerWeylInput) {A : Subgroup (MulAut ↥Bs)}
    (hA : ggAutomizerJoin L Bs 𝒦 ≤ A) {ι' : Type} [Fintype ι'] {M' : CoxeterMatrix ι'}
    (hW' : GGWeylOfType 3 M' A) : LargeEvenTwoLocalRank 3 G ≤ Fintype.card ι' := by
  have hS : LargeEvenSStar 3 B x L := hcfg.1.1.1.2.2.2.2.2.2.1
  have hBc : Nat.card B = 3 ^ LargeEvenTwoLocalRank 3 G := hS.1.2.1
  have hBle : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hcfg.1.1.2.1.1
  have hle : Nat.card Bs ≤ 3 ^ Fintype.card ι' :=
    hcfg.card_le_pow_of_weylOfType hTBF hWI hA hW'
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp (by rw [← hBc]; exact hBle.trans hle)

private theorem false_typeE6_of_torusRank
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) (hTBF : GGTBFixInput)
    (hWI : GGNbrInnerWeylInput) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e) {σ : Fin 6 ≃ ι}
    (hM : M = CoxeterMatrix.E₆.reindex σ) {P : ℕ → LargeEvenLabel → Prop}
    (hP : ∀ lab, P 3 lab → lab.tag = .twA ∧ 3 ≤ lab.rank ∧ lab.n = 1 ∧ 3 ∣ lab.rank + 1 ∧
      lab.rank ≠ 5 ∧ ggUnitaryTorusRank 3 (lab.rank + 1) + 1 ≤ LargeEvenTwoLocalRank 3 G)
    (h : GGInnerDiagOnLabel P 3 Bs L) : False := by
  have hW' : GGWeylOfType 3 CoxeterMatrix.E₆ (ggAutomizerJoin L Bs 𝒦) := by
    subst hM
    exact GGWeylOfType.of_reindex ⟨e, hpres.2⟩
  have hr : LargeEvenTwoLocalRank 3 G ≤ 6 := by
    simpa using largeEvenTwoLocalRank_le_of_weyl hcfg hTBF hWI le_rfl hW'
  obtain ⟨lab, -, -, -, -, -, -, -, hl, -⟩ := largeEvenMarking_exists_hasLabel h
  obtain ⟨ht, h3le, hn1, hdvd, hne5, hrank⟩ := hP lab hl
  exact hne5 (eq_five_of_torusRank h3le hdvd hrank hr)

private theorem false_typeE7_of_torusRank
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) (hTBF : GGTBFixInput)
    (hWI : GGNbrInnerWeylInput) (hb1 : GGFrameTBNumerologyInput)
    (hb1' : GGFrameTBVacuousInput) (hrig : GGLabelRigidInput)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e) {σ : Fin 7 ≃ ι}
    (hM : M = CoxeterMatrix.E₇.reindex σ)
    (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L) (hW : GGSecFiveWeylCase 3 B Bs x D J)
    (h' : GGInnerDiagOnLabel (fun p lab => (ggRowP_ESU p lab ∧ lab.n = 1 ∧ 3 ∣ lab.rank + 1 ∧
      lab.rank ≠ 5) ∧ ggUnitaryTorusRank 3 (lab.rank + 1) + 1 ≤ LargeEvenTwoLocalRank 3 G)
      3 Bs L) : False := by
  have hJ : GGSecFiveWeylAtJoin 3 B Bs x L D J CoxeterMatrix.E₇ :=
    hcfg.weylAtJoin_of_reindex hpres σ hM
  have hW' : GGWeylOfType 3 CoxeterMatrix.E₇ (ggAutomizerJoin L Bs 𝒦) := by
    subst hM
    exact GGWeylOfType.of_reindex ⟨e, hpres.2⟩
  have hr : LargeEvenTwoLocalRank 3 G ≤ 7 := by
    simpa using largeEvenTwoLocalRank_le_of_weyl hcfg hTBF hWI le_rfl hW'
  have hm := marking_eight_of_torusRank h' hr (by norm_num : 7 ≤ 8)
  exact (GGSecFiveRouteCfg.false_of_twA8_E7 hTBF hWI hb1 hb1' hrig hcfg.1 hW hq hJ hm).elim

private theorem lt_typeE8_of_torusRank
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) (hTBF : GGTBFixInput)
    (hWI : GGNbrInnerWeylInput) (hb1 : GGFrameTBNumerologyInput)
    (hb1' : GGFrameTBVacuousInput) (hrig : GGLabelRigidInput) (hPU : GGPumpupInput)
    (hO : GGOuterThreeRankInput) (hTCJ : GGTCJKnown)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e) {σ : Fin 8 ≃ ι}
    (hM : M = CoxeterMatrix.E₈.reindex σ)
    (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L) (hW : GGSecFiveWeylCase 3 B Bs x D J)
    (h' : GGInnerDiagOnLabel (fun p lab => (ggRowP_ESU p lab ∧ lab.n = 1 ∧ 3 ∣ lab.rank + 1 ∧
      lab.rank ≠ 5) ∧ ggUnitaryTorusRank 3 (lab.rank + 1) + 1 ≤ LargeEvenTwoLocalRank 3 G)
      3 Bs L) : B < Bs := by
  have hJ : GGSecFiveWeylAtJoin 3 B Bs x L D J CoxeterMatrix.E₈ :=
    hcfg.weylAtJoin_of_reindex hpres σ hM
  have hW' : GGWeylOfType 3 CoxeterMatrix.E₈ (ggAutomizerJoin L Bs 𝒦) := by
    subst hM
    exact GGWeylOfType.of_reindex ⟨e, hpres.2⟩
  have hr : LargeEvenTwoLocalRank 3 G ≤ 8 := by
    simpa using largeEvenTwoLocalRank_le_of_weyl hcfg hTBF hWI le_rfl hW'
  have hm := marking_eight_of_torusRank h' hr le_rfl
  exact GGSecFiveRouteCfg.lt_bstar_of_twA8_E8 hTBF hWI hb1 hb1' hrig hPU hO hTCJ hcfg.1 hW hq
    hJ hm

theorem GGSecFiveRouteCfg.lt_bstar_of_twA_dvd_typeE
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (hb1 : GGFrameTBNumerologyInput)
    (hb1' : GGFrameTBVacuousInput) (hrig : GGLabelRigidInput) (hPU : GGPumpupInput)
    (hO : GGOuterThreeRankInput) (hTCJ : GGTCJKnown)
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hE : GGIsWeylMatrixE M)
    (h : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ 3 ∣ lab.rank + 1 ∧ lab.rank ≠ 5) p Bs L) :
    B < Bs := by
  have hp3 := NSJoin.eq_three_of_innerDiagOnLabel_n_one hcfg.1.1.tableB_facts.1
    (fun _ hl => ⟨hl.2.1, hl.1.2⟩) h
  subst p
  have h' := hcfg.1.1.innerDiagOnLabel_torusRank
    (P := fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ 3 ∣ lab.rank + 1 ∧ lab.rank ≠ 5)
    (fun lab hl => rowP_ESU_three_imp hl) h
  have hq := innerDiagOnLabel_labQTwo_of_rowP h
  have hW := ggSecFiveWeylCase_of_prime_three hcfg.1.1 hcfg.2.1
  rcases hE with ⟨σ, hM⟩ | ⟨σ, hM⟩ | ⟨σ, hM⟩
  · exact (false_typeE6_of_torusRank hcfg hTBF hWI hpres hM
      (fun lab hl => rowP_ESU_three_imp' hl) h').elim
  · exact (false_typeE7_of_torusRank hcfg hTBF hWI hb1 hb1' hrig hpres hM hq hW h').elim
  · exact lt_typeE8_of_torusRank hcfg hTBF hWI hb1 hb1' hrig hPU hO hTCJ hpres hM hq hW h'

end CFSG.StandardType
