module

public import CFSG.LocalAnalysis.StandardType.GGQ2TwoNodeSixCell
public import Certificates.Certificate10010
public import Certificates.Certificate10011
import CFSG.LocalAnalysis.StandardType.GGQ2TwoNodeI1Rank
import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitarySides
import CFSG.LocalAnalysis.StandardType.GGTwoNodeRowDimUnitary
import CFSG.LocalAnalysis.StandardType.GGTwA5ThreeFrame
import CFSG.LocalAnalysis.StandardType.GGPZNbrResRest
import CFSG.LocalAnalysis.StandardType.GGD5LabelJ
import CFSG.LocalAnalysis.StandardType.GGQ2TableBI1Tor
import CFSG.LocalAnalysis.StandardType.GGQ2LDatumDims
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGTableBBstar
import CFSG.LocalAnalysis.StandardType.GGStdSubExist
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171InnerU6U42
import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.Mathlib.GroupTheory.Automorphism.ConjCommute
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171Facts

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2_card_gammaJ_le_of_u42
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    (hJ : GGHasLabel ⟨.twA, 3, 1⟩ (↥J ⧸ Subgroup.center ↥J))
    (hN : Bs ≤ Subgroup.normalizer (J : Set G)) :
    Nat.card (ggGamma J hN).range ≤ 3 ^ 3 := by
  obtain ⟨-, -, hinner⟩ := lup10d_labelCore_of_labelJ (p := 3) hS rfl hJ
  have hBs : IsElemAbelian 3 Bs := hS.1.1.tableB_facts.2.1
  have hcat : CFSG.Yardstones.Md0ec50421ce4.catalogIs (↥J ⧸ Subgroup.center ↥J)
      CFSG.LocalAnalysis.GLTheoremA.S9.isU4two := by
    unfold GGHasLabel CFSG.StandardType.LargeEvenRawDatum at hJ
    obtain ⟨K, hKfield, hKfinite, hKcard, ⟨e⟩⟩ := hJ
    let : Field K := hKfield
    let : Finite K := hKfinite
    have hK4 : Nat.card K = 4 := by simpa using hKcard
    exact CFSG.LocalAnalysis.GLTheoremA.CatB.catalogIs_u4two_of_statedProj hK4 e
  have hInn : (ggGamma J hN).range ≤ (MulAut.conj : ↥J →* MulAut ↥J).range := by
    rintro _ ⟨b, rfl⟩
    obtain ⟨j, hj, hjk⟩ := hinner b b.2
    refine ⟨⟨j, hj⟩, MulEquiv.ext fun k => Subtype.ext ?_⟩
    rw [ggGamma_coe]
    exact (hjk k k.2).symm
  have hE : IsElemAbelian 3 (ggGamma J hN).range := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, b₁, rfl⟩ ⟨_, b₂, rfl⟩
      refine Subtype.ext ?_
      change ggGamma J hN b₁ * ggGamma J hN b₂ = ggGamma J hN b₂ * ggGamma J hN b₁
      rw [← map_mul, ← map_mul, hBs.1.is_comm.comm b₁ b₂]
    · rintro _ ⟨b, rfl⟩
      have hb : b ^ 3 = 1 := Subtype.ext (hBs.2 b b.2)
      rw [← map_pow, hb, map_one]
  let e : ↥J ⧸ Subgroup.center ↥J ≃* (MulAut.conj : ↥J →* MulAut ↥J).range :=
    (QuotientGroup.quotientMulEquivOfEq (mulAut_conj_ker (G := ↥J)).symm).trans
      (QuotientGroup.quotientKerEquivRange _)
  have hle := CFSG.LocalAnalysis.GLTheoremA.T171U6.u42Rank_holds _ hcat
    (((ggGamma J hN).range.subgroupOf (MulAut.conj : ↥J →* MulAut ↥J).range).map
      e.symm.toMonoidHom)
    ((hE.subgroupOf _).map e.symm.toMonoidHom)
  rw [Subgroup.card_map_of_injective e.symm.injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hInn).toEquiv] at hle
  exact hle.trans (by norm_num)

theorem ggQ2_card_bstar_le_of_I1_twA_six
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hI1 : GGQTwoI1 Bs D J) {X : Subgroup G} {u : G}
    (hXu : (X = L ∧ u = x) ∨ GGNbr 3 B x D J u X) (hrow : GGQ2S08RowTwA 3 6 X J) :
    Nat.card Bs ≤ 3 ^ 5 := by
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  have hIDA : GGInnerDiagAll 3 B Bs x L D J := hS.1.2.2.1
  obtain ⟨labX, labJ, hmX, hmJ, hJt, hXt, hrk, hn, -, hpq, hNJ⟩ := hrow
  have hnX : labX.n < 2 ∨ GGNbr 3 B x D J u X := by
    rcases hXu with ⟨rfl, -⟩ | hnb
    · exact Or.inl (ggQ2_labQTwo_of_marking_twA hRig hS hXt hmX)
    · exact Or.inr hnb
  obtain ⟨lX, hΛX, hhasX, -, -, -, -, -, hEX⟩ := largeEvenMarking_exists_hasLabel hmX
  obtain ⟨lJ, -, hhasJ, -, -, -, -, -, hEJ⟩ := largeEvenMarking_exists_hasLabel hmJ
  subst hEX hEJ
  obtain ⟨tX, rX, nX⟩ := lX
  obtain ⟨tJ, rJ, nJ⟩ := lJ
  dsimp only at hJt hXt hrk hn hpq hNJ hΛX hhasX hhasJ hnX
  subst hJt hXt hrk hn
  obtain rfl : rJ = 3 := by omega
  have hBsJ : Bs ≤ Subgroup.normalizer (J : Set G) :=
    GGDichotomy.le_normalizer_stdSub
      (fun a ha b hb => congrArg Subtype.val
        (hcfg.tableB_facts.2.1.1.is_comm.comm (⟨a, ha⟩ : ↥Bs) ⟨b, hb⟩))
      hcfg.2.1.1 hcfg.2.2.1 (GGDichotomy.le_normalizer_of_innerDiagOn hIDA.1)
  have hBsp : ∀ b ∈ Bs, b ^ 3 = 1 := fun b hb => hcfg.tableB_facts.2.1.2 b hb
  have hcap : Nat.card (ggGamma J hBsJ).range ≤ 3 ^ 3 := by
    rcases (show nX = 1 ∨ 2 ≤ nX by have : 1 ≤ nX := hΛX.1; omega) with rfl | h2
    · exact ggQ2_card_gammaJ_le_of_u42 hS hhasJ hBsJ
    · have hnb := hnX.resolve_left (by omega)
      have hmk := ggInnerDiagOn_relabel hRig (hIDA.2 u X hnb) hΛX hhasX
      have hmk' : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twA, 3 + 2, nX⟩) 3 Bs X :=
        largeEvenMarking_mono (fun lab R _ I F θ hP => ⟨hP.1, hP.2⟩) hmk
      obtain ⟨F, hField, hFinite, -, hN, φ, S, -, hM, hJ, hS', hdiag⟩ :=
        exists_corank_two_block_of_large_unitary_K_of_cfg_of_rank hRig hLB hcfg hIDA hnb
          (r := 3 + 2) (f := nX) (by omega)
          (Or.inr ⟨by omega, fun hN => ggTwA5Three_rank hLB hP hcfg hnb (Or.inr rfl) hmk'
            ⟨rfl, rfl, hpq⟩ hN⟩) hpq (by norm_num) hhasX hΛX hhasJ
      let : Field F := hField
      let : Finite F := hFinite
      calc Nat.card (ggGamma J hBsJ).range ≤ 3 ^ (S.card - 1) :=
            card_range_ggGamma_le hM hN hdiag le_rfl S (by omega) hJ hBsJ Nat.prime_three hBsp
        _ = 3 ^ 3 := by rw [hS']
  calc Nat.card Bs = Nat.card (ggGamma J hBsJ).range * 3 ^ 2 :=
        (ggQ2_card_bstar_eq_of_I1 hcfg hI1 hBsJ).symm
    _ ≤ 3 ^ 3 * 3 ^ 2 := Nat.mul_le_mul_right _ hcap
    _ = 3 ^ 5 := by norm_num

private theorem ggQ2tn6h_torData_L
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J) (hInn : GGInnerDiagOn Bs L)
    {labL : LargeEvenLabel} (hΛ : LargeEvenInLambda2 labL)
    (hl : GGHasLabel labL (↥L ⧸ Subgroup.center ↥L))
    (htag : labL.tag = .twA ∧ labL.rank = 5 ∧ 3 ∣ 2 ^ labL.n + 1) :
    ∃ (f : ℕ) (hN : Bs ≤ Subgroup.normalizer (L : Set G)), 1 ≤ f ∧ 3 ∣ 2 ^ f + 1 ∧
      GGTorusTorData (2 ^ f + 1) 5 (CartanMatrix.A 5) (CoxeterMatrix.A 5) ↥L
        (ggGamma L hN).range := by
  obtain ⟨htw, hr5, hdvd⟩ := htag
  have hmk := ggInnerDiagOn_relabel hRig hInn hΛ hl
  have hmark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧
      3 ∣ ggTorM lab) 3 Bs L := by
    refine largeEvenMarking_mono (fun lab R _ I F θ hP => ?_) hmk
    obtain ⟨hlab, hN', hBsI⟩ := hP
    subst hlab
    exact ⟨⟨htw, hr5, by simpa [ggTorM, htw] using hdvd⟩, hN', hBsI⟩
  have hM : GGInnerDiagOnLab GGUnitDvd63Label 3 Bs L := by
    refine largeEvenMarking_mono (fun lab R _ I F θ hP => ?_) hmk
    obtain ⟨hlab, hN', hBsI⟩ := hP
    subst hlab
    exact ⟨⟨⟨htw, by omega, hdvd, by omega⟩, hr5, rfl⟩,
      Or.inr (Or.inl ⟨by simp [LargeEvenUntwisted, htw], by simp [htw], hdvd⟩), hN', hBsI⟩
  obtain ⟨f, hf, hpq, -, hN, hTor⟩ := ggTwA5Three_torData hcfg hmark fun hN => by
    have hcard := Line63.H5.ggUnitDvd63BstarRankInput_holds G 3 B Bs x L D J hcfg hM
    obtain ⟨hp', hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
    have hSS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
    have hmul := card_range_ggGamma_mul_of hp' hBs hxBs hSS.2.2.1 hLx hSS.2.2.2.2 hN
    rw [← hmul, pow_succ] at hcard
    exact Nat.le_of_mul_le_mul_right hcard hp'.pos
  exact ⟨f, hN, hf, hpq, hTor⟩

theorem ggQ2TwAHeartDatumSixInput_holds
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput) :
    GGQ2TwAHeartDatumSixInput := by
  intro G _ _ p _ hp B Bs x L D J hS hI1 X u hXu hrow huX
  subst hp
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  have hIDA : GGInnerDiagAll 3 B Bs x L D J := hS.1.2.2.1
  obtain ⟨-, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
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
  have hle := ggQ2_card_bstar_le_of_I1_twA_six hRig hLB hP hS hI1 hXu hrow
  obtain ⟨labX, labJ, hmX, -, -, hXt, hrk, hn, -, hpq, hNJ⟩ := hrow
  obtain ⟨lX, hΛX, hhasX, -, -, -, -, -, hEX⟩ := largeEvenMarking_exists_hasLabel hmX
  subst hEX
  have htag : lX.tag = .twA ∧ lX.rank = 5 ∧ 3 ∣ 2 ^ lX.n + 1 :=
    ⟨hXt, by omega, by rw [hn]; exact hpq⟩
  obtain ⟨f, hN, hf, hpqf, hTor⟩ : ∃ (f : ℕ) (hN : Bs ≤ Subgroup.normalizer (X : Set G)),
      1 ≤ f ∧ 3 ∣ 2 ^ f + 1 ∧ GGTorusTorData (2 ^ f + 1) 5 (CartanMatrix.A 5)
        (CoxeterMatrix.A 5) ↥X (ggGamma X hN).range := by
    rcases hXu with ⟨rfl, -⟩ | hnb
    · exact ggQ2tn6h_torData_L hRig hcfg hInnX hΛX hhasX htag
    · exact ggTwA5Three_torDataNbr hRig hLB hP hcfg hnb hInnX hΛX hhasX htag
  obtain ⟨M, -, ⟨e, hC⟩, hshape⟩ :=
    exists_ggQ2LDatum_of_torData_of_not_mem (p := 3) (C := CartanMatrix.A 5)
      (M := CoxeterMatrix.A 5) (lab := ⟨.twA, 5, f⟩) (by norm_num) hBs hSC hu1 hBX hN
      ((Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one) hpqf
      (Or.inl ⟨5, Equiv.refl _, by omega, Or.inl rfl⟩) (ggIntCartan_A 5) hTor huX
      (by simp only [GGQ2LabelWeyl]; exact ⟨Equiv.refl _, rfl⟩)
  have hΛ : Fintype.card M.Λ = 5 := by
    rw [← Fintype.card_congr e, Fintype.card_fin]
  refine ⟨M, e, hC, ?_⟩
  rcases hshape with hF | hB | hC'
  · rw [M.card_eq_pow_finrank, ggQ2LD_dim_nonheart M (Or.inl hF), hΛ] at hle
    exact absurd ((Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hle) (by omega)
  · exact hB
  · rw [M.card_of_shapeC hC', hΛ] at hle
    exact absurd ((Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hle) (by omega)

theorem ggQ2s08_tn6_holds
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hNC : GGLNoncyclicInput) (h5 : GGQTwoCentralizerInput) (hK : GGReflClassOmegaInput)
    (hCavH : GGQ2CavOfTBHeartInner) (hTP : GGNbrTablePNbrInputI1On GGRegimeLine)
    (hPL : GGQ2TablePAtLTwA3) :
    GGQ2S08TNCell (GGQ2S08PosTwA 6) :=
  ggQ2s08_tn6_of_tableP hRig hLB hP hNC h5 hK hCavH hTP hPL
    (ggQ2TwAHeartDatumSixInput_holds hRig hLB hP)

end CFSG.StandardType

end
