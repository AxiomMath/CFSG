module

public import CFSG.LocalAnalysis.StandardType.GGF4H4JBlockLinear
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsu
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosAdapter
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDiag
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosTransport
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosTransportAux
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosRankAux2
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSCornerMain
import CFSG.LocalAnalysis.StandardType.GGNSJoinJA2AAuxBlock
public import CFSG.LocalAnalysis.StandardType.GGNSJoinJA2AAuxCover
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeBlock
import CFSG.LocalAnalysis.StandardType.GGNSJoinJA2AAuxRank
import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUModel
import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepFrame
import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepResidual
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabelPSU
import CFSG.RankThree.PartOne.KFOUT3.L12Levi
import Certificates.Certificate117
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPieces
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniComp
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Pieces
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
import CFSG.RankThree.PartTwo.Sec12.Notation
import CFSG.RankThree.PartTwo.Sec4.Item47Diag
import CFSG.RankThree.PartTwo.Sec4.Item47Statement
import CFSG.RankThree.PartTwo.Sec4.Item47Witness
import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.SectionRank.OddCover (diagHom)

theorem ggF4JB_unitary_block
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p f : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {ks : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J ks) (hf : 2 ≤ f)
    (hpf : p ∣ 2 ^ f + 1) (hLlab : GGHasLabel ⟨.twA, 3, f⟩ (L ⧸ Subgroup.center L)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (hK : Nat.card K = (2 ^ f) ^ 2)
      (ψ : Su K 2 f 4 →* G) (P : Finset (Fin 4)),
      GGNSLocalHyp p B Bs K f 4 ψ ∧ GGActsDiagonally (p := 2) (f := f) ψ Bs ∧ ψ.range = L ∧
        P.card = 3 ∧ J = (TableBUE.blockSU (K := K) (n := f) P).map (nsJA2Cover hK ψ) := by
  classical
  have hInn : GGInnerDiagOn Bs L := hcfg.1.2.2.1.1
  have hΛ : LargeEvenInLambda2 (⟨.twA, 3, f⟩ : LargeEvenLabel) :=
    ⟨le_trans (by norm_num : 1 ≤ 2) hf, by norm_num, fun h => absurd h (by norm_num)⟩
  have hInnLabel : GGInnerDiagOnLabel
      (fun p' lab => lab = (⟨.twA, 3, f⟩ : LargeEvenLabel) ∧ p' ∣ 2 ^ f + 1) p Bs L := by
    unfold GGInnerDiagOnLabel
    exact largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨⟨h.1, hpf⟩, h.2⟩)
      (ggInnerDiagOn_relabel hRig hInn hΛ hLlab)
  have hP : ∀ p' lab, (lab = (⟨.twA, 3, f⟩ : LargeEvenLabel) ∧ p' ∣ 2 ^ f + 1) →
      ggRowP_ESU p' lab ∧ ¬ (lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5)) := by
    rintro p' lab ⟨rfl, hdvd⟩
    refine ⟨⟨Or.inl ⟨rfl, le_rfl⟩, by simpa using hdvd⟩, ?_⟩
    rintro ⟨hn1, -⟩
    have hf1 : f = 1 := by simpa using hn1
    omega
  obtain ⟨lab, K, hKfield, hKfin, hKchar, f', n, ψ, hPlab, hn, hf', hKcard, hn4, hker,
    hrange, hdvd, hacts, -⟩ := ggNSLie_cover_of_esu_pred (X := L) hP hInnLabel
  obtain ⟨rfl, -⟩ := hPlab
  have hf'' : f' = f := by simpa using hf'
  rw [← hf'']
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨3, by simpa using hn⟩
  have hn3 : m + 1 = 3 + 1 := by simpa using hn
  have hm3 : m = 3 := by omega
  have hloc : GGNSLocalHyp p B Bs K f' (m + 1) ψ :=
    ggNSLocalHyp_of_routeCfg (X := L) hcfg (Or.inl rfl) hKcard hn4 hker hrange hdvd hacts
  obtain ⟨c, hd⟩ := ggNSLocal_exists_diag ggSecFiveNSCornerInput_holds hloc
  let ψc : Su K 2 f' (m + 1) →* G := ψ.comp (MulAut.conj c).toMonoidHom
  have h' : GGNSLocalHyp p B Bs K f' (m + 1) ψc := hloc.comp_conj c
  have hrange' : ψc.range = L := by
    change (ψ.comp (MulAut.conj c).toMonoidHom).range = L
    rw [ggNSPosPD_range_comp_conj, hrange]
  have hufd : UnitaryFieldData 2 f' K := ggNSPosPC_ufd h'
  have hDleBs : D ≤ Bs := hcfg.1.1.2.2.1.1.trans hcfg.1.1.2.1.1
  let ψ' : ↥(unitarySU 2 f' K (m + 1)) →* G := nsJA2Cover h'.card ψc
  let δwit : (e : G) → e ∈ Bs → Fin (m + 1) → Kˣ := fun e he =>
    Classical.choose (nsJA2Cover_mem_suPairs h'.card
      (Classical.choose_spec (hd e he)).1 (Classical.choose_spec (hd e he)).2)
  let δ : G → Fin (m + 1) → Kˣ := fun e => if he : e ∈ Bs then δwit e he else 1
  have hδ : ∀ e ∈ (D : Set G), (e, diagHom (m + 1) (δ e)) ∈ SUTorus.suPairs ψ' := by
    intro e he
    have heB : e ∈ Bs := hDleBs he
    have hδe : δ e = δwit e heB := by
      simp only [δ]
      exact dif_pos heB
    rw [hδe]
    exact Classical.choose_spec (nsJA2Cover_mem_suPairs h'.card
      (Classical.choose_spec (hd e heB)).1 (Classical.choose_spec (hd e heB)).2)
  have hcomp0 : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hcfg.1.1.2.2.1.2.2.2.2.2.1
  have hJcomp : IsComponentOf J (ψ'.range ⊓ Subgroup.centralizer (D : Set G)) := by
    simpa [ψ', nsJA2Cover_range h'.card ψc, hrange'] using hcomp0
  obtain ⟨i, hiJ⟩ := SUTorus.exists_le_map_blockSU hufd h'.prime h'.dvd
    (nsJA2Cover_ker_le h'.card h'.ker) hδ hJcomp
  let P : Finset (Fin (m + 1)) := LinTorus.diagClass (D : Set G) δ i
  let Y : Subgroup G := (TableBUE.blockSU (K := K) (n := f') P).map ψ'
  have hiJ' : J ≤ Y := hiJ
  have hmem : i ∈ P := LinTorus.self_mem_diagClass (D : Set G) δ i
  by_cases hP2 : P.card ≤ 2
  ·
    haveI : Nontrivial (Fin (m + 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
    obtain ⟨a, b, hab, hPsub⟩ := nsJA2_exists_pair_of_card_le_two hmem hP2
    have hYpair : Y ≤ (ggSuPairBlock K 2 f' (m + 1) a b).map ψc := by
      simpa [Y, ψ'] using nsJA2Cover_map_blockSU_le_pairBlock h'.card ψc hPsub
    exact (nsJA2_false_of_le_pairBlock hcfg h' hd hab (hiJ'.trans hYpair)).elim
  have h3 : 3 ≤ P.card := by omega
  have hVq : (P.card, 2 ^ f') ≠ (3, 2) := by
    intro hEq
    have hq2 : 2 ^ f' = 2 := congrArg Prod.snd hEq
    have hf1 : f' = 1 := (Nat.pow_eq_self_iff (by norm_num)).mp hq2
    omega
  have hker' : ψ'.ker ≤ Subgroup.center ↥(unitarySU 2 f' K (m + 1)) :=
    nsJA2Cover_ker_le h'.card h'.ker
  have hJeqY : J = Y := by
    have hEq := nsJA2_eq_of_blockSU_of_card_three_le hufd hker' hδ hJcomp hiJ' h3 hVq
    simpa [P, Y] using hEq
  have hPle : P.card ≤ 4 := by
    calc P.card ≤ Fintype.card (Fin (m + 1)) := P.card_le_univ
      _ = m + 1 := Fintype.card_fin _
      _ = 4 := by omega
  have hne4 : P.card ≠ 4 := by
    intro hP4
    have hPuniv : P = Finset.univ :=
      Finset.eq_univ_of_card P (by rw [hP4, Fintype.card_fin]; omega)
    have hYtop : Y = ψ'.range := by
      change (TableBUE.blockSU (K := K) (n := f') P).map ψ' = ψ'.range
      rw [hPuniv, SUTorus.blockSU_univ, Subgroup.map_top]
    have hLrange : ψ'.range = L := by
      change (nsJA2Cover h'.card ψc).range = L
      rw [nsJA2Cover_range, hrange']
    have hJeqL : J = L := hJeqY.trans (hYtop.trans hLrange)
    have hpre : LargeEvenStdSubPre p B x L D J := hcfg.1.1.2.2.1
    have hDp : Nat.card D = p := by
      rw [hpre.2.2.2.2.2.2, hJeqL, ← hrange']
      exact h'.cent
    have hsq : p ^ 2 = p := by rw [← hpre.2.2.1, hDp]
    have hlt : p < p ^ 2 := by
      rw [pow_two]
      calc p = p * 1 := (Nat.mul_one p).symm
        _ < p * p := Nat.mul_lt_mul_of_pos_left h'.prime.one_lt h'.prime.pos
    omega
  have hP3 : P.card = 3 := by omega
  subst hm3
  exact ⟨K, hKfield, hKfin, hKchar, h'.card, ψc, P, h', hd, hrange', hP3, hJeqY⟩

theorem ggF4JB_unitary
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p f : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {ks : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J ks) (hf : 2 ≤ f)
    (hpf : p ∣ 2 ^ f + 1) (hLlab : GGHasLabel ⟨.twA, 3, f⟩ (L ⧸ Subgroup.center L)) :
    GGHasLabel ⟨.twA, 2, f⟩ (J ⧸ Subgroup.center J) ∧
      Nat.card (Subgroup.center J) = Nat.gcd 3 (2 ^ f + 1) := by
  classical
  obtain ⟨K, hKfield, hKfin, hKchar, hK, ψc, P, h', -, -, hP3, hJeqY⟩ :=
    ggF4JB_unitary_block hRig hcfg hf hpf hLlab
  have hufd : UnitaryFieldData 2 f K := ggNSPosPC_ufd h'
  let ψ' : ↥(unitarySU 2 f K 4) →* G := nsJA2Cover hK ψc
  let Y : Subgroup G := (TableBUE.blockSU (K := K) (n := f) P).map ψ'
  have hker' : ψ'.ker ≤ Subgroup.center ↥(unitarySU 2 f K 4) :=
    nsJA2Cover_ker_le hK h'.ker
  have h3 : 3 ≤ P.card := by omega
  have hVq : (P.card, 2 ^ f) ≠ (3, 2) := by
    intro hEq
    have hq2 : 2 ^ f = 2 := congrArg Prod.snd hEq
    have hf1 : f = 1 := (Nat.pow_eq_self_iff (by norm_num)).mp hq2
    omega
  have hlabY : GGHasLabel ⟨.twA, 2, f⟩ (Y ⧸ Subgroup.center Y) := by
    obtain ⟨e⟩ := SUTorus.nonempty_mulEquiv_quotient_center_blockSU hufd hker' h3 hVq
    have hP31 : P.card = 2 + 1 := by omega
    exact CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.ggHasLabel_twA (b := 2) (m := f)
      hK (hP31 ▸ e)
  refine ⟨?_, ?_⟩
  · exact hJeqY.symm ▸ hlabY
  · obtain ⟨i₀, -, hi₀⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := P) (t := Finset.univ) (by rw [Finset.card_univ, Fintype.card_fin]; omega)
    have hframe : SURep.GGFrameKer ψ' :=
      SURep.ggFrameKer_of_ker_le_center hK (by omega) (by
        intro hEq
        have h1 : 4 = 3 := congrArg Prod.fst hEq
        omega) hker'
    obtain ⟨eU⟩ := SURep.nonempty_map_blockSU_equiv hufd hframe hi₀
    have hcenterY : Nat.card (Subgroup.center Y) = Nat.gcd 3 (2 ^ f + 1) := by
      have hcen : Nat.card (Subgroup.center Y) =
          Nat.card (Subgroup.center ↥(unitarySU 2 f K P.card)) :=
        Nat.card_congr (Subgroup.centerCongr eU).toEquiv
      rw [hcen, hP3]
      exact CFSG.RankThree.PartOne.KFOUT3.card_center_unitarySU_three hufd (by omega)
    exact hJeqY.symm ▸ hcenterY

theorem ggF4JBUnitaryHalf_holds
    (hRig : GGLabelRigidInput) : GGF4JBUnitaryHalf := by
  intro G _ _ p f B Bs x L D J ks hcfg hf hpf hLlab
  exact ggF4JB_unitary hRig hcfg hf hpf hLlab

theorem ggF4H4JBlock_holds
    (hMp : GGInnerDiagMpInput) (hRig : GGLabelRigidInput) :
    GGF4H4JBlock :=
  ggF4H4JBlock_of_unitary_half hMp (ggF4JBUnitaryHalf_holds hRig)

end CFSG.StandardType

end
