module

public import CFSG.LocalAnalysis.StandardType.GGQ2TwoNodeBigCell
import CFSG.LocalAnalysis.StandardType.GGQ2TableBI1Tor
import CFSG.LocalAnalysis.StandardType.GGTDLabels
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySplitRefl
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenCore
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenTwE6Three
import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
import CFSG.LocalAnalysis.StandardType.GGTableBBstar
import CFSG.LocalAnalysis.StandardType.GGQ2LDatumDims
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy
import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeLinearNbr
import CFSG.LocalAnalysis.StandardType.GGTwoNodeRowDimLinear
import CFSG.LocalAnalysis.StandardType.GGNbrLangTorARankBound

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


theorem ggQ2TwAHeartDatumInput_holds (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) : GGQ2TwAHeartDatumInput := by
  intro G _ _ p _ hp B Bs x L D J hS hI1 X u hXu N hN hrow huX
  subst hp
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  have hIDA : GGInnerDiagAll 3 B Bs x L D J := hS.1.2.2.1
  obtain ⟨-, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hX : X = L ∨ ∃ y, GGNbr 3 B x D J y X := hXu.imp And.left fun h => ⟨u, h⟩
  have hInnX : GGInnerDiagOn Bs X := by
    rcases hXu with ⟨rfl, -⟩ | hnb
    · exact hIDA.1
    · exact hIDA.2 u X hnb
  have hu1 : u ≠ 1 := by
    rcases hXu with ⟨-, rfl⟩ | hnb
    · exact hcfg.1.2.2.2.2.2.2.1.2.2.1
    · exact hnb.1.2.2.1
  have hBX : Bs ⊓ Subgroup.centralizer (X : Set G) = Subgroup.zpowers u := by
    rcases hXu with ⟨rfl, rfl⟩ | hnb
    · obtain ⟨hp3, -, hxBs, hLx, -⟩ := hcfg.tableB_facts
      have hSstar := hcfg.1.2.2.2.2.2.2.1
      exact inf_centralizer_eq_zpowers_of_elemAbelian hp3 hBs hxBs hSstar.2.2.1 hLx
        hSstar.2.2.2.2
    · exact ggQ2_inf_centralizer_nbr_eq_of_I1 hLB hP hS.1 hI1 hnb
  have hNX : Bs ≤ Subgroup.normalizer (X : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hInnX
  have hle := ggQ2_card_bstar_le_of_I1_twA hRig hLB hcfg hIDA hI1 hX (by omega) hrow
  obtain ⟨labX, labJ, hmX, -, -, hXt, hrk, hn, hpd, hpq, hNJ⟩ := hrow
  have hN1 : N - 1 = labX.rank := by omega
  have hdvd : 3 ∣ labX.rank + 1 := by
    rw [← hN1, show N - 1 + 1 = N by omega, ← hNJ]
    exact hpd
  have hpqX : 3 ∣ 2 ^ labX.n + 1 := by
    rw [hn]
    exact hpq
  rw [hN1] at hle ⊢
  obtain ⟨lX, hΛX, hhasX, -, -, -, -, -, hEX⟩ := largeEvenMarking_exists_hasLabel hmX
  subst hEX
  obtain ⟨tX, rX, nX⟩ := lX
  dsimp only at hXt hN1 hdvd hpqX hle ⊢
  subst hXt
  have hm : ggTorM ⟨.twA, rX, nX⟩ = 2 ^ nX + 1 := by
    simp [ggTorM]
  have hm3 : 3 ∣ ggTorM ⟨.twA, rX, nX⟩ := by
    rw [hm]
    exact hpqX
  have hmOdd : Odd (ggTorM ⟨.twA, rX, nX⟩) := by
    have hn1 : 1 ≤ nX := hΛX.1
    rw [hm]
    exact (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
  have hE : ggTorEnn 3 ⟨.twA, rX, nX⟩ = 1 := by
    unfold ggTorEnn
    dsimp only
    rw [if_pos hpqX]
  have hs : rX - 1 - ggTorEnn 3 ⟨.twA, rX, nX⟩ = ggUnitaryTorusRank 3 (rX + 1) := by
    rw [hE]
    simp only [ggUnitaryTorusRank, if_pos hdvd]
    omega
  have hTorW := ggTorusTorW_uni_label (p := 3) (n := nX) (l := rX) Nat.prime_three hΛX
    (by omega) hdvd hm3 (by omega)
  rw [hs] at hTorW
  have hLift : LargeEvenLabelAll ⟨.twA, rX, nX⟩ fun R _ _ _ =>
      GGTorusLift 3 (ggUnitaryTorusRank 3 (rX + 1)) R :=
    largeEvenLabelAll_torusLift_twA (lab := ⟨.twA, rX, nX⟩) hΛX rfl Nat.prime_three hpqX
  obtain ⟨R, _, θ, I, F, hBsI, hlift, hTW⟩ :=
    exists_innerDiagDatum_of_labelAll hRig hInnX hΛX hhasX (largeEvenLabelAll_and hLift hTorW) hNX
  have hTB : GGTorusTBGroup 3 (ggUnitaryTorusRank 3 (rX + 1)) R I X (ggQuotHom θ)
      (ggGamma X hNX).range := by
    rcases hX with rfl | ⟨y, hnb⟩
    · exact ggTorusTBGroup_of_L hcfg hmX.1 θ hNX hBsI hlift
    · exact ggTorusTBGroup_of_nbr hcfg hnb hmX.1 θ hNX hBsI hlift
  obtain ⟨M, -, ⟨e, hC⟩, hshape⟩ :=
    exists_ggQ2LDatum_of_torData_of_not_mem (p := 3) (C := CartanMatrix.A rX)
      (M := CoxeterMatrix.A rX) (lab := ⟨.twA, rX, nX⟩) (by norm_num) hBs hSC hu1 hBX hNX hmOdd
      hm3 (Or.inl ⟨rX, Equiv.refl _, by omega, Or.inl rfl⟩) (ggIntCartan_A rX)
      (hTW ↥X (ggQuotHom θ) (ggGamma X hNX).range hTB) huX
      (by simp only [GGQ2LabelWeyl]; exact ⟨Equiv.refl _, rfl⟩)
  refine ⟨M, e, hC, hshape.resolve_left fun hF => ?_⟩
  have hΛ : Fintype.card M.Λ = rX := by
    rw [← Fintype.card_congr e, Fintype.card_fin]
  rw [M.card_eq_pow_finrank, ggQ2LD_dim_nonheart M (Or.inl hF), hΛ] at hle
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hle
  omega

theorem ggQ2s08_noNbrBig_holds (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) (h5 : GGQTwoCentralizerInput) (hK : GGReflClassOmegaInput)
    (hdLab : GGCoxeterLabelInput) (hWA : GGTBFixNbrXInput) (hTBF : GGTBFixInput)
    (hRGq : ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
      {L D J : Subgroup G} {y : G} {K : Subgroup G}, GGQTwoSetting p B Bs x L D J →
        GGNbr p B x D J y K → GGReflGenerated p (ggAutomizer K Bs)) :
    GGQ2S08NoNbrCell GGQ2S08PosTwABig :=
  ggQ2s08_noNbrBig_of_heartDatum hRig hLB hP h5 hK hdLab hWA hTBF hRGq
    (ggQ2TwAHeartDatumInput_holds hRig hLB hP)

theorem ggQ2_card_bstar_le_of_I1_A (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hIDA : GGInnerDiagAll p B Bs x L D J)
    (hI1 : GGQTwoI1 Bs D J) {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K) {N : ℕ}
    (h7 : 7 ≤ N) (hrow : GGQ2S08RowA p N K J) :
    Nat.card Bs ≤ p ^ (N - 1) := by
  have hp : p.Prime := Fact.out
  obtain ⟨labX, labJ, hmX, hmJ, hJt, hXt, hrk, hn, -, hpq, hNJ⟩ := hrow
  obtain ⟨lX, hΛX, hhasX, -, -, -, -, -, hEX⟩ := largeEvenMarking_exists_hasLabel hmX
  obtain ⟨lJ, -, hhasJ, -, -, -, -, -, hEJ⟩ := largeEvenMarking_exists_hasLabel hmJ
  subst hEX hEJ
  obtain ⟨tX, rX, nX⟩ := lX
  obtain ⟨tJ, rJ, nJ⟩ := lJ
  dsimp only at hJt hXt hrk hn hpq hNJ hΛX hhasX hhasJ
  subst hJt hXt hrk hn
  have hBsJ : Bs ≤ Subgroup.normalizer (J : Set G) :=
    GGDichotomy.le_normalizer_stdSub
      (fun a ha b hb => congrArg Subtype.val
        (hcfg.tableB_facts.2.1.1.is_comm.comm (⟨a, ha⟩ : ↥Bs) ⟨b, hb⟩))
      hcfg.2.1.1 hcfg.2.2.1 (GGDichotomy.le_normalizer_of_innerDiagOn hIDA.1)
  have hJLab : GGHasLabel ⟨.A, rJ + 2 - 2, nX⟩ (J ⧸ Subgroup.center J) := by
    simpa only [Nat.add_sub_cancel] using hhasJ
  obtain ⟨F, hField, hFinite, -, hN, φ, S, -, -, hker, hdiag, hS, hJ⟩ :=
    exists_corank_two_block_of_large_linear_K_of_cfg hRig hLB hcfg hIDA hnb (by omega) hpq hhasX
      hΛX hJLab
  let : Field F := hField
  let : Finite F := hFinite
  have hcap := TypeANbrDvd.card_range_ggGamma_le hp φ
    (show J = TypeANbrDvd.blockImage S K φ from hJ) hN hBsJ le_rfl hker (by omega : 2 ≤ S.card)
    hdiag (fun b => Subtype.ext (hcfg.tableB_facts.2.1.2 b b.2))
  rw [hS] at hcap
  calc Nat.card Bs = Nat.card (ggGamma J hBsJ).range * p ^ 2 :=
        (ggQ2_card_bstar_eq_of_I1 hcfg hI1 hBsJ).symm
    _ ≤ p ^ (rJ + 2 - 1 - 1) * p ^ 2 := Nat.mul_le_mul_right _ hcap
    _ = p ^ (N - 1) := by
      rw [← pow_add]
      congr 1
      omega

theorem ggQ2_tnBigSel_nbr_of_rowA (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp : p = 3)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J)
    (hI1 : GGQTwoI1 Bs D J) {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K) {N : ℕ}
    (h12 : 12 ≤ N) (hrow : GGQ2S08RowA p N K J) (hyK : y ∉ K) : GGQ2TNBigSel p Bs K y := by
  subst hp
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  have hIDA : GGInnerDiagAll 3 B Bs x L D J := hS.1.2.2.1
  obtain ⟨-, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hInnK : GGInnerDiagOn Bs K := hIDA.2 y K hnb
  have hBK : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y :=
    ggQ2_inf_centralizer_nbr_eq_of_I1 hLB hP hS.1 hI1 hnb
  have hNK : Bs ≤ Subgroup.normalizer (K : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hInnK
  have hle := ggQ2_card_bstar_le_of_I1_A hRig hLB hcfg hIDA hI1 hnb (by omega) hrow
  obtain ⟨labX, labJ, hmX, -, -, hXt, hrk, hn, hpd, hpq, hNJ⟩ := hrow
  have hN1 : N - 1 = labX.rank := by omega
  have hdvd : 3 ∣ labX.rank + 1 := by
    rw [← hN1, show N - 1 + 1 = N by omega, ← hNJ]
    exact hpd
  have hpqX : 3 ∣ 2 ^ labX.n - 1 := by
    rw [hn]
    exact hpq
  rw [hN1] at hle
  obtain ⟨lX, hΛX, hhasX, -, -, -, -, -, hEX⟩ := largeEvenMarking_exists_hasLabel hmX
  subst hEX
  obtain ⟨tX, rX, nX⟩ := lX
  dsimp only at hXt hN1 hdvd hpqX hle
  subst hXt
  have hm : ggTorM ⟨.A, rX, nX⟩ = 2 ^ nX - 1 := by
    simp [ggTorM]
  have hm3 : 3 ∣ ggTorM ⟨.A, rX, nX⟩ := by
    rw [hm]
    exact hpqX
  have hmOdd : Odd (ggTorM ⟨.A, rX, nX⟩) := by
    have hn1 : 1 ≤ nX := hΛX.1
    rw [hm]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  have hE : ggTorEnn 3 ⟨.A, rX, nX⟩ = 0 := by
    unfold ggTorEnn
    dsimp only
    rw [if_neg]
    intro h
    have h2 : 3 ∣ (2 ^ nX + 1) - (2 ^ nX - 1) := Nat.dvd_sub h hpqX
    have h3 : (2 ^ nX + 1) - (2 ^ nX - 1) = 2 := by
      have := Nat.one_le_two_pow (n := nX)
      omega
    rw [h3] at h2
    omega
  have hs : rX - 1 - ggTorEnn 3 ⟨.A, rX, nX⟩ = rX + 1 - 2 := by
    rw [hE]
    omega
  have hTorW := ggTorusTorW_lin_label (p := 3) (n := nX) (l := rX) Nat.prime_three (by norm_num)
    (by omega) hm3
  rw [hs] at hTorW
  have hLift : LargeEvenLabelAll ⟨.A, rX, nX⟩ fun R _ _ _ => GGTorusLift 3 (rX + 1 - 2) R :=
    largeEvenLabelAll_torusLift_typeA (lab := ⟨.A, rX, nX⟩) Nat.prime_three rfl (by omega) hpqX
  obtain ⟨R, _, θ, I, F, hBsI, hlift, hTW⟩ :=
    exists_innerDiagDatum_of_labelAll hRig hInnK hΛX hhasX (largeEvenLabelAll_and hLift hTorW) hNK
  have hTB : GGTorusTBGroup 3 (rX + 1 - 2) R I K (ggQuotHom θ) (ggGamma K hNK).range :=
    ggTorusTBGroup_of_nbr hcfg hnb hmX.1 θ hNK hBsI hlift
  obtain ⟨M, -, ⟨e, hC⟩, hshape⟩ :=
    exists_ggQ2LDatum_of_torData_of_not_mem (p := 3) (C := CartanMatrix.A rX)
      (M := CoxeterMatrix.A rX) (lab := ⟨.twA, rX, nX⟩) (by norm_num) hBs hSC hnb.1.2.2.1 hBK hNK
      hmOdd hm3 (Or.inl ⟨rX, Equiv.refl _, by omega, Or.inl rfl⟩) (ggIntCartan_A rX)
      (hTW ↥K (ggQuotHom θ) (ggGamma K hNK).range hTB) hyK
      (by simp only [GGQ2LabelWeyl]; exact ⟨Equiv.refl _, rfl⟩)
  have hΛ : Fintype.card M.Λ = rX := by
    rw [← Fintype.card_congr e, Fintype.card_fin]
  have hB : M.ShapeB := by
    rcases hshape with hF | hB | hC'
    · rw [M.card_eq_pow_finrank, ggQ2LD_dim_nonheart M (Or.inl hF), hΛ] at hle
      have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hle
      omega
    · exact hB
    · rw [M.card_of_shapeC hC', hΛ] at hle
      have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hle
      omega
  exact ⟨M, rX, by omega, hdvd, e, hC, hB⟩

theorem ggQ2s08_noNbrABigK_holds (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) (h5 : GGQTwoCentralizerInput) (hK : GGReflClassOmegaInput)
    (hdLab : GGCoxeterLabelInput) (hTBF : GGTBFixInput)
    (hRGq : ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
      {L D J : Subgroup G} {y : G} {K : Subgroup G}, GGQTwoSetting p B Bs x L D J →
        GGNbr p B x D J y K → GGReflGenerated p (ggAutomizer K Bs))
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp : p = 3) {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J) (hI1 : GGQTwoI1 Bs D J)
    {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K) (hpos : GGQ2S08PosABig p K J)
    (hyK : y ∉ K) : False := by
  obtain ⟨N, h12, hrow⟩ := hpos
  exact ggQ2_tnBigK_false hLB hP h5 hK hdLab hTBF hp hS hI1 hnb (hRGq hS hnb)
    (ggQ2_tnBigSel_nbr_of_rowA hRig hLB hP hp hS hI1 hnb h12 hrow hyK)

end CFSG.StandardType

end
