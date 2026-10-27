module

public import CFSG.LocalAnalysis.StandardType.GGSporKCommDataF
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenCensus
public import Certificates.Certificate716100
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSeven
public import CFSG.YGroups.Y443.Tri.Finiteness
import CFSG.LocalAnalysis.StandardType.GGSporKCommDataSylow
import CFSG.LocalAnalysis.StandardType.GGSporKCommDataDich
import CFSG.LocalAnalysis.StandardType.GGSporKM7Irr
public import CFSG.Certificates.InvariantMerge
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.HardMathSupport.Foote.E27.TableSylow
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterTwoA
public import CFSG.LocalAnalysis.AGLEmbedding.CoverWeakGenData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeGen
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicData
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.RankThree.Chevalley.SteinbergBIE7ThreeA1
public import CFSG.RankThree.OddKernel.SporadicKernelCases
public import CFSG.RankThree.PartOne.K1214.OmegaAlg
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.Walter.Defs
public import CFSG.YGroups.Y443.Native.Parabolic2CheckB
public import CFSG.YGroups.Y443.Native.Parabolic2CheckW
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Monster.B.Pinned CFSG.Monster.Generated
  CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenCensus
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenFlag
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenData

@[expose] def m7M : Matrix (Fin 4) (Fin 4) (ZMod 7) :=
  !![0, 6, 1, 1; 1, 0, 6, 0; 6, 1, 0, 0; 6, 0, 0, 0]

private theorem m7r_conj {w : List CFSG.Monster.AxisCount.Native.Gen} {x : Gmat}
    (h : gw m7hW * gw w = x * gw m7hW) :
    gw m7hW * gw w * (gw m7hW)⁻¹ = x := by
  rw [h, mul_assoc, mul_inv_cancel, mul_one]

private theorem m7r_intro_gq1 : gq 1 = gw wq1 := rfl
private theorem m7r_intro_gq2 : gq 2 = gw wq2 := rfl
private theorem m7r_intro_gq3 : gq 3 = gw wq3 := rfl
private theorem m7r_intro_gq4 : gq 4 = gw wq4 := rfl
private theorem m7r_intro_gq5 : gq 5 = gw wq5 := rfl

private theorem m7r_comm5_of
    (n : ℕ) (hi : n < 6) (hj : n < 5)
    (hword : Timmesfeld.Mon7.wordOfVec 6 (Timmesfeld.Mon7.cw7[n * 6 + 5]!) = [5]) :
    gq n * gq 5 = gq 5 * gq n := by
  have h := gq_conj (i := n) (j := 5) hi (by norm_num) hj
  rw [hword] at h
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  exact (mul_inv_eq_iff_eq_mul).1 h

private theorem m7r_comm1 :
    gq 1 * gq 5 = gq 5 * gq 1 :=
  m7r_comm5_of 1 (by norm_num) (by norm_num) (by decide +kernel)

private theorem m7r_comm2 :
    gq 2 * gq 5 = gq 5 * gq 2 :=
  m7r_comm5_of 2 (by norm_num) (by norm_num) (by decide +kernel)

private theorem m7r_comm3 :
    gq 3 * gq 5 = gq 5 * gq 3 :=
  m7r_comm5_of 3 (by norm_num) (by norm_num) (by decide +kernel)

private theorem m7r_comm4 :
    gq 4 * gq 5 = gq 5 * gq 4 :=
  m7r_comm5_of 4 (by norm_num) (by norm_num) (by decide +kernel)

private theorem m7r_bcomm_of_conj {a b z : Gmat} {w : ℕ}
    (h : a * b * a⁻¹ = b * z ^ w) (ha : a * z = z * a) (hb : b * z = z * b) :
    bcomm a b = z ^ w := by
  have haz : Commute a z := ha
  have h2 : a * b = b * z ^ w * a := (mul_inv_eq_iff_eq_mul).1 h
  have h5 : (a⁻¹ * b * a) * z ^ w = b := by
    calc (a⁻¹ * b * a) * z ^ w
        = a⁻¹ * b * (a * z ^ w) := by group
      _ = a⁻¹ * b * (z ^ w * a) := by rw [← (haz.pow_right w).eq]
      _ = a⁻¹ * (b * z ^ w * a) := by group
      _ = a⁻¹ * (a * b) := by rw [← h2]
      _ = b := by group
  have h4 : a⁻¹ * b * a = b * (z ^ w)⁻¹ := (eq_mul_inv_iff_mul_eq).2 h5
  calc bcomm a b = (a⁻¹ * b * a)⁻¹ * b := by rw [bcomm]; group
    _ = (b * (z ^ w)⁻¹)⁻¹ * b := by rw [h4]
    _ = z ^ w := by group

private theorem m7r_bcomm_pair
    (i j : ℕ) (hi : i < 6) (hj : j < 6) (hij : i < j)
    (w : ℕ) (hword : Timmesfeld.Mon7.wordOfVec 6 (Timmesfeld.Mon7.cw7[i * 6 + j]!) =
      j :: List.replicate w 5)
    (hci : gq i * gq 5 = gq 5 * gq i) (hcj : gq j * gq 5 = gq 5 * gq j) :
    bcomm (gq i) (gq j) = gq 5 ^ w := by
  have h := gq_conj (i := i) (j := j) hi hj hij
  rw [hword] at h
  simp only [List.map_cons, List.map_replicate, List.prod_cons, List.prod_replicate] at h
  exact m7r_bcomm_of_conj h hci hcj

private theorem m7r_diag (a : Gmat) : bcomm a a = gq 5 ^ 0 := by
  rw [bcomm, pow_zero]; group

private theorem m7r_bc12 :
    bcomm (gq 1) (gq 2) = gq 5 ^ 6 :=
  m7r_bcomm_pair 1 2 (by norm_num) (by norm_num) (by norm_num) 6 (by decide +kernel)
    m7r_comm1 m7r_comm2

private theorem m7r_bc13 :
    bcomm (gq 1) (gq 3) = gq 5 ^ 1 :=
  m7r_bcomm_pair 1 3 (by norm_num) (by norm_num) (by norm_num) 1 (by decide +kernel)
    m7r_comm1 m7r_comm3

private theorem m7r_bc14 :
    bcomm (gq 1) (gq 4) = gq 5 ^ 1 :=
  m7r_bcomm_pair 1 4 (by norm_num) (by norm_num) (by norm_num) 1 (by decide +kernel)
    m7r_comm1 m7r_comm4

private theorem m7r_bc23 :
    bcomm (gq 2) (gq 3) = gq 5 ^ 6 :=
  m7r_bcomm_pair 2 3 (by norm_num) (by norm_num) (by norm_num) 6 (by decide +kernel)
    m7r_comm2 m7r_comm3

private theorem m7r_bc24 :
    bcomm (gq 2) (gq 4) = gq 5 ^ 0 :=
  m7r_bcomm_pair 2 4 (by norm_num) (by norm_num) (by norm_num) 0 (by decide +kernel)
    m7r_comm2 m7r_comm4

private theorem m7r_bc34 :
    bcomm (gq 3) (gq 4) = gq 5 ^ 0 :=
  m7r_bcomm_pair 3 4 (by norm_num) (by norm_num) (by norm_num) 0 (by decide +kernel)
    m7r_comm3 m7r_comm4

private theorem m7r_inv_pow
    (w : ℕ) (hw : w ≤ 7) :
    (gq 5 ^ w)⁻¹ = gq 5 ^ (7 - w) := by
  have h7 : gq 5 ^ 7 = 1 := gq_pow (i := 5) (by norm_num)
  have h : gq 5 ^ w * gq 5 ^ (7 - w) = 1 := by
    rw [← pow_add]
    have : w + (7 - w) = 7 := by omega
    rw [this, h7]
  refine mul_right_cancel (b := gq 5 ^ w) ?_
  rw [inv_mul_cancel, ← pow_add]
  have : 7 - w + w = 7 := by omega
  rw [this, h7]

private theorem m7r_bc21 :
    bcomm (gq 2) (gq 1) = gq 5 ^ 1 := by
  rw [bcomm_swap, m7r_bc12, m7r_inv_pow 6 (by norm_num)]

private theorem m7r_bc31 :
    bcomm (gq 3) (gq 1) = gq 5 ^ 6 := by
  rw [bcomm_swap, m7r_bc13, m7r_inv_pow 1 (by norm_num)]

private theorem m7r_bc32 :
    bcomm (gq 3) (gq 2) = gq 5 ^ 1 := by
  rw [bcomm_swap, m7r_bc23, m7r_inv_pow 6 (by norm_num)]

private theorem m7r_bc41 :
    bcomm (gq 4) (gq 1) = gq 5 ^ 6 := by
  rw [bcomm_swap, m7r_bc14, m7r_inv_pow 1 (by norm_num)]

private theorem m7r_bc42 :
    bcomm (gq 4) (gq 2) = gq 5 ^ 0 := by
  rw [bcomm_swap, m7r_bc24, pow_zero, inv_one]

private theorem m7r_bc43 :
    bcomm (gq 4) (gq 3) = gq 5 ^ 0 := by
  rw [bcomm_swap, m7r_bc34, pow_zero, inv_one]


private theorem m7r_bcv00 :
    bcomm (gq 1) (gq 1) = gq 5 ^ (m7M 0 0).val := by
  rw [show (m7M 0 0).val = 0 from by decide +kernel]
  exact m7r_diag (gq 1)

private theorem m7r_bcv01 :
    bcomm (gq 1) (gq 2) = gq 5 ^ (m7M 0 1).val := by
  rw [show (m7M 0 1).val = 6 from by decide +kernel]
  exact m7r_bc12

private theorem m7r_bcv02 :
    bcomm (gq 1) (gq 3) = gq 5 ^ (m7M 0 2).val := by
  rw [show (m7M 0 2).val = 1 from by decide +kernel]
  exact m7r_bc13

private theorem m7r_bcv03 :
    bcomm (gq 1) (gq 4) = gq 5 ^ (m7M 0 3).val := by
  rw [show (m7M 0 3).val = 1 from by decide +kernel]
  exact m7r_bc14

private theorem m7r_bcv10 :
    bcomm (gq 2) (gq 1) = gq 5 ^ (m7M 1 0).val := by
  rw [show (m7M 1 0).val = 1 from by decide +kernel]
  exact m7r_bc21

private theorem m7r_bcv11 :
    bcomm (gq 2) (gq 2) = gq 5 ^ (m7M 1 1).val := by
  rw [show (m7M 1 1).val = 0 from by decide +kernel]
  exact m7r_diag (gq 2)

private theorem m7r_bcv12 :
    bcomm (gq 2) (gq 3) = gq 5 ^ (m7M 1 2).val := by
  rw [show (m7M 1 2).val = 6 from by decide +kernel]
  exact m7r_bc23

private theorem m7r_bcv13 :
    bcomm (gq 2) (gq 4) = gq 5 ^ (m7M 1 3).val := by
  rw [show (m7M 1 3).val = 0 from by decide +kernel]
  exact m7r_bc24

private theorem m7r_bcv20 :
    bcomm (gq 3) (gq 1) = gq 5 ^ (m7M 2 0).val := by
  rw [show (m7M 2 0).val = 6 from by decide +kernel]
  exact m7r_bc31

private theorem m7r_bcv21 :
    bcomm (gq 3) (gq 2) = gq 5 ^ (m7M 2 1).val := by
  rw [show (m7M 2 1).val = 1 from by decide +kernel]
  exact m7r_bc32

private theorem m7r_bcv22 :
    bcomm (gq 3) (gq 3) = gq 5 ^ (m7M 2 2).val := by
  rw [show (m7M 2 2).val = 0 from by decide +kernel]
  exact m7r_diag (gq 3)

private theorem m7r_bcv23 :
    bcomm (gq 3) (gq 4) = gq 5 ^ (m7M 2 3).val := by
  rw [show (m7M 2 3).val = 0 from by decide +kernel]
  exact m7r_bc34

private theorem m7r_bcv30 :
    bcomm (gq 4) (gq 1) = gq 5 ^ (m7M 3 0).val := by
  rw [show (m7M 3 0).val = 6 from by decide +kernel]
  exact m7r_bc41

private theorem m7r_bcv31 :
    bcomm (gq 4) (gq 2) = gq 5 ^ (m7M 3 1).val := by
  rw [show (m7M 3 1).val = 0 from by decide +kernel]
  exact m7r_bc42

private theorem m7r_bcv32 :
    bcomm (gq 4) (gq 3) = gq 5 ^ (m7M 3 2).val := by
  rw [show (m7M 3 2).val = 0 from by decide +kernel]
  exact m7r_bc43

private theorem m7r_bcv33 :
    bcomm (gq 4) (gq 4) = gq 5 ^ (m7M 3 3).val := by
  rw [show (m7M 3 3).val = 0 from by decide +kernel]
  exact m7r_diag (gq 4)


theorem m7h_conj :
    gw m7hW * gq 1 * (gw m7hW)⁻¹ = gq 1 * gq 2 * gq 4 ^ 2 ∧
      gw m7hW * gq 2 * (gw m7hW)⁻¹ = gq 2 * gq 3 ∧
      gw m7hW * gq 3 * (gw m7hW)⁻¹ = gq 1 ^ 4 * gq 3 * gq 4 ^ 5 ∧
      gw m7hW * gq 4 * (gw m7hW)⁻¹ = gq 1 ^ 2 * gq 4 ^ 3 ∧
      gw m7hW * gq 5 * (gw m7hW)⁻¹ = gq 5 := by
  have hp := Certificates.certificate716100
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h := agreeAll_sound hp
      (wq1 ++ m7hW, m7hW ++ CFSG.YGroups.Y443.powL 2 wq4 ++ wq2 ++ wq1)
      (by simp [m7hPairs])
    have h1 : gw m7hW * gw wq1 =
        (gw wq1 * gw wq2 * gw wq4 ^ 2) * gw m7hW := by
      simp only [gw_append, gw_powL'] at h
      rw [h]; group
    rw [m7r_intro_gq1, m7r_intro_gq2, m7r_intro_gq4]
    exact m7r_conj h1
  · have h := agreeAll_sound hp
      (wq2 ++ m7hW, m7hW ++ wq3 ++ wq2)
      (by simp [m7hPairs])
    have h1 : gw m7hW * gw wq2 = (gw wq2 * gw wq3) * gw m7hW := by
      simp only [gw_append, gw_powL'] at h
      rw [h]; group
    rw [m7r_intro_gq2, m7r_intro_gq3]
    exact m7r_conj h1
  · have h := agreeAll_sound hp
      (wq3 ++ m7hW, m7hW ++ CFSG.YGroups.Y443.powL 5 wq4 ++ wq3 ++
        CFSG.YGroups.Y443.powL 4 wq1)
      (by simp [m7hPairs])
    have h1 : gw m7hW * gw wq3 =
        (gw wq1 ^ 4 * gw wq3 * gw wq4 ^ 5) * gw m7hW := by
      simp only [gw_append, gw_powL'] at h
      rw [h]; group
    rw [m7r_intro_gq1, m7r_intro_gq3, m7r_intro_gq4]
    exact m7r_conj h1
  · have h := agreeAll_sound hp
      (wq4 ++ m7hW, m7hW ++ CFSG.YGroups.Y443.powL 3 wq4 ++ CFSG.YGroups.Y443.powL 2 wq1)
      (by simp [m7hPairs])
    have h1 : gw m7hW * gw wq4 = (gw wq1 ^ 2 * gw wq4 ^ 3) * gw m7hW := by
      simp only [gw_append, gw_powL'] at h
      rw [h]; group
    rw [m7r_intro_gq1, m7r_intro_gq4]
    exact m7r_conj h1
  · have h := agreeAll_sound hp
      (wq5 ++ m7hW, m7hW ++ wq5)
      (by simp [m7hPairs])
    have h1 : gw m7hW * gw wq5 = gw wq5 * gw m7hW := by
      simp only [gw_append, gw_powL'] at h
      exact h
    rw [m7r_intro_gq5]
    exact m7r_conj h1

theorem gq_commData :
    CommData 7 ![gq 1, gq 2, gq 3, gq 4] (gq 5) m7M := by
  have hz5 : gq 5 ≠ 1 := by
    have h0 := orb_conj (k := 0) (by norm_num)
    have h1 : Timmesfeld.Mon7.orbWord[0]! = [5] := by decide +kernel
    rw [h1, gw_Wrho] at h0
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h0
    rw [show gw (wq[5]!) = gq 5 from rfl] at h0
    intro h1
    rw [h1, isConj_one_right] at h0
    split_ifs at h0
    · exact zG_ne_one h0
    · exact dG_ne_one h0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact gq_pow (i := 1) (by norm_num)
    · exact gq_pow (i := 2) (by norm_num)
    · exact gq_pow (i := 3) (by norm_num)
    · exact gq_pow (i := 4) (by norm_num)
  · haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact orderOf_eq_prime (gq_pow (i := 5) (by norm_num)) hz5
  · intro i
    fin_cases i
    · exact m7r_comm1
    · exact m7r_comm2
    · exact m7r_comm3
    · exact m7r_comm4
  · intro i j
    fin_cases i <;> fin_cases j
    · exact m7r_bcv00
    · exact m7r_bcv01
    · exact m7r_bcv02
    · exact m7r_bcv03
    · exact m7r_bcv10
    · exact m7r_bcv11
    · exact m7r_bcv12
    · exact m7r_bcv13
    · exact m7r_bcv20
    · exact m7r_bcv21
    · exact m7r_bcv22
    · exact m7r_bcv23
    · exact m7r_bcv30
    · exact m7r_bcv31
    · exact m7r_bcv32
    · exact m7r_bcv33
  · have hdet : m7M.det = 1 := by decide +kernel
    rw [hdet]
    exact isUnit_one
  · have h1 : gq 1 ∈ Subgroup.closure (Set.range (![gq 1, gq 2, gq 3, gq 4] : Fin 4 → Gmat)) :=
      Subgroup.subset_closure ⟨0, rfl⟩
    have h3 : gq 3 ∈ Subgroup.closure (Set.range (![gq 1, gq 2, gq 3, gq 4] : Fin 4 → Gmat)) :=
      Subgroup.subset_closure ⟨2, rfl⟩
    have hb : bcomm (gq 1) (gq 3) ∈
        Subgroup.closure (Set.range (![gq 1, gq 2, gq 3, gq 4] : Fin 4 → Gmat)) := by
      rw [bcomm]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.inv_mem _ h1) (Subgroup.inv_mem _ h3)) h1) h3
    rw [show gq 5 = bcomm (gq 1) (gq 3) from by rw [m7r_bc13, pow_one]]
    exact hb

private theorem m7l_cw1 : Timmesfeld.Mon7.wordOfVec 6 (Timmesfeld.Mon7.cw7[1]!) =
    [1, 2, 5, 5, 5] := by
  decide +kernel

private theorem m7l_cw2 : Timmesfeld.Mon7.wordOfVec 6 (Timmesfeld.Mon7.cw7[2]!) =
    [2, 3, 5, 5, 5, 5] := by
  decide +kernel

private theorem m7l_cw3 : Timmesfeld.Mon7.wordOfVec 6 (Timmesfeld.Mon7.cw7[3]!) =
    [3, 4, 5, 5, 5, 5, 5] := by
  decide +kernel

private theorem m7l_cw4 : Timmesfeld.Mon7.wordOfVec 6 (Timmesfeld.Mon7.cw7[4]!) =
    [4, 5, 5] := by
  decide +kernel

private theorem m7l_cw5 : Timmesfeld.Mon7.wordOfVec 6 (Timmesfeld.Mon7.cw7[5]!) = [5] := by
  decide +kernel

private theorem m7l_gq_mem (hD : CommData 7 ![gq 1, gq 2, gq 3, gq 4] (gq 5) m7M)
    (k : Fin 6) (hk0 : k ≠ 0) :
    gq k.val ∈ Subgroup.closure (Set.range ![gq 1, gq 2, gq 3, gq 4]) := by
  fin_cases k
  · exact absurd rfl hk0
  · exact Subgroup.subset_closure ⟨0, rfl⟩
  · exact Subgroup.subset_closure ⟨1, rfl⟩
  · exact Subgroup.subset_closure ⟨2, rfl⟩
  · exact Subgroup.subset_closure ⟨3, rfl⟩
  · exact hD.mem_z

private theorem m7l_q0_conj_mem
    (hD : CommData 7 ![gq 1, gq 2, gq 3, gq 4] (gq 5) m7M) (i : Fin 4) :
    (gq 0) * (![gq 1, gq 2, gq 3, gq 4] i) * (gq 0)⁻¹ ∈
      Subgroup.closure (Set.range ![gq 1, gq 2, gq 3, gq 4]) := by
  fin_cases i
  · have hc := gq_conj (i := 0) (j := 1) (by norm_num) (by norm_num) (by norm_num)
    rw [m7l_cw1] at hc
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, inv_inv,
      Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons]
    rw [hc]
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    simp only [List.mem_map] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    have hklt : k < 6 := by omega
    have hk0 : k ≠ 0 := by omega
    exact m7l_gq_mem hD ⟨k, hklt⟩ (by rintro h; exact hk0 (Fin.ext_iff.1 h))
  · have hc := gq_conj (i := 0) (j := 2) (by norm_num) (by norm_num) (by norm_num)
    rw [m7l_cw2] at hc
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, inv_inv,
      Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons]
    rw [hc]
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    simp only [List.mem_map] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    have hklt : k < 6 := by omega
    have hk0 : k ≠ 0 := by omega
    exact m7l_gq_mem hD ⟨k, hklt⟩ (by rintro h; exact hk0 (Fin.ext_iff.1 h))
  · have hc := gq_conj (i := 0) (j := 3) (by norm_num) (by norm_num) (by norm_num)
    rw [m7l_cw3] at hc
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, inv_inv,
      Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons]
    rw [hc]
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    simp only [List.mem_map] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    have hklt : k < 6 := by omega
    have hk0 : k ≠ 0 := by omega
    exact m7l_gq_mem hD ⟨k, hklt⟩ (by rintro h; exact hk0 (Fin.ext_iff.1 h))
  · have hc := gq_conj (i := 0) (j := 4) (by norm_num) (by norm_num) (by norm_num)
    rw [m7l_cw4] at hc
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, inv_inv,
      Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons]
    rw [hc]
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    simp only [List.mem_map] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    have hklt : k < 6 := by omega
    have hk0 : k ≠ 0 := by omega
    exact m7l_gq_mem hD ⟨k, hklt⟩ (by rintro h; exact hk0 (Fin.ext_iff.1 h))

private theorem m7l_h_conj_mem
    (hD : CommData 7 ![gq 1, gq 2, gq 3, gq 4] (gq 5) m7M) (i : Fin 4) :
    (gw m7hW) * (![gq 1, gq 2, gq 3, gq 4] i) * (gw m7hW)⁻¹ ∈
      Subgroup.closure (Set.range ![gq 1, gq 2, gq 3, gq 4]) := by
  have hh := m7h_conj
  fin_cases i
  · simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, inv_inv,
      Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons]
    rw [hh.1]
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (m7l_gq_mem hD (k := 1) (by decide))
        (m7l_gq_mem hD (k := 2) (by decide)))
      (Subgroup.pow_mem _ (m7l_gq_mem hD (k := 4) (by decide)) 2)
  · simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, inv_inv,
      Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons]
    rw [hh.2.1]
    exact Subgroup.mul_mem _ (m7l_gq_mem hD (k := 2) (by decide))
      (m7l_gq_mem hD (k := 3) (by decide))
  · simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, inv_inv,
      Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons]
    rw [hh.2.2.1]
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.pow_mem _ (m7l_gq_mem hD (k := 1) (by decide)) 4)
        (m7l_gq_mem hD (k := 3) (by decide)))
      (Subgroup.pow_mem _ (m7l_gq_mem hD (k := 4) (by decide)) 5)
  · simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, inv_inv,
      Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons]
    rw [hh.2.2.2.1]
    exact Subgroup.mul_mem _
      (Subgroup.pow_mem _ (m7l_gq_mem hD (k := 1) (by decide)) 2)
      (Subgroup.pow_mem _ (m7l_gq_mem hD (k := 4) (by decide)) 3)

private theorem m7l_mem_normalizer {b : Gmat}
    (hb : ∀ i, b * (![gq 1, gq 2, gq 3, gq 4] i) * b⁻¹ ∈
      Subgroup.closure (Set.range ![gq 1, gq 2, gq 3, gq 4])) :
    b ∈ Subgroup.normalizer
      (Subgroup.closure (Set.range ![gq 1, gq 2, gq 3, gq 4]) : Set Gmat) := by
  have hb' : ∀ i, (b⁻¹)⁻¹ * (![gq 1, gq 2, gq 3, gq 4] i) * b⁻¹ ∈
      Subgroup.closure (Set.range ![gq 1, gq 2, gq 3, gq 4]) :=
    fun i => by simpa only [inv_inv] using hb i
  have h : b⁻¹ ∈ Subgroup.normalizer
      (Subgroup.closure (Set.range ![gq 1, gq 2, gq 3, gq 4]) : Set Gmat) :=
    mem_normalizer_of_conj (fun g hg => CommData.conj_mem hb' hg)
  simpa only [inv_inv] using Subgroup.inv_mem _ h

private theorem m7l_hz (hD : CommData 7 ![gq 1, gq 2, gq 3, gq 4] (gq 5) m7M) :
    bcomm (![gq 1, gq 2, gq 3, gq 4] 0) (![gq 1, gq 2, gq 3, gq 4] 2) = gq 5 := by
  rw [hD.bcomm_q]
  have h : (m7M 0 2).val = 1 := by decide +kernel
  rw [h, pow_one]

private theorem m7l_L_le_normalizer
    (hD : CommData 7 ![gq 1, gq 2, gq 3, gq 4] (gq 5) m7M) :
    Subgroup.closure ({gq 0, gq 1, gq 2, gq 3, gq 4, gw m7hW} : Set Gmat) ≤
      Subgroup.normalizer
        (Subgroup.closure (Set.range ![gq 1, gq 2, gq 3, gq 4]) : Set Gmat) := by
  rw [Subgroup.closure_le]
  intro b hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7l_mem_normalizer (m7l_q0_conj_mem hD)
  · exact Subgroup.le_normalizer (Subgroup.subset_closure ⟨0, rfl⟩)
  · exact Subgroup.le_normalizer (Subgroup.subset_closure ⟨1, rfl⟩)
  · exact Subgroup.le_normalizer (Subgroup.subset_closure ⟨2, rfl⟩)
  · exact Subgroup.le_normalizer (Subgroup.subset_closure ⟨3, rfl⟩)
  · exact m7l_mem_normalizer (m7l_h_conj_mem hD)

private theorem m7l_L_le_centralizer
    (hD : CommData 7 ![gq 1, gq 2, gq 3, gq 4] (gq 5) m7M) :
    Subgroup.closure ({gq 0, gq 1, gq 2, gq 3, gq 4, gw m7hW} : Set Gmat) ≤
      Subgroup.centralizer ({gq 5} : Set Gmat) := by
  have hh := m7h_conj
  rw [Subgroup.closure_le]
  intro b hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · have hc := gq_conj (i := 0) (j := 5) (by norm_num) (by norm_num) (by norm_num)
    rw [m7l_cw5] at hc
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hc
    exact Subgroup.mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 hc)
  · exact Subgroup.mem_centralizer_singleton_iff.2 (hD.comm_z 0)
  · exact Subgroup.mem_centralizer_singleton_iff.2 (hD.comm_z 1)
  · exact Subgroup.mem_centralizer_singleton_iff.2 (hD.comm_z 2)
  · exact Subgroup.mem_centralizer_singleton_iff.2 (hD.comm_z 3)
  · exact Subgroup.mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 hh.2.2.2.2)

private theorem m7l_factorization :
    (Nat.card Gmat).factorization 7 = 6 := by
  have h : CFSG.Open.monsterOrder = 7 ^ 6 *
      (2 ^ 46 * 3 ^ 20 * 5 ^ 9 * 11 ^ 2 * 13 ^ 3 * 17 * 19 * 23 * 29 * 31 * 41 * 47 * 59 *
        71) := by
    norm_num [CFSG.Open.monsterOrder]
  rw [CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder, h,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

private theorem m7l_actMat_q0 :
    CommData.actMat 7 ![gq 1, gq 2, gq 3, gq 4] (gq 5) m7M (gq 0)⁻¹ =
      !![1, 1, 0, 0; 0, 1, 1, 0; 0, 0, 1, 1; 0, 0, 0, 1] := by
  have hD := gq_commData
  apply CommData.actMat_eq hD (R := !![1, 1, 0, 0; 0, 1, 1, 0; 0, 0, 1, 1; 0, 0, 0, 1])
    (c := ![3, 4, 5, 2])
  intro i
  fin_cases i
  · have hc := gq_conj (i := 0) (j := 1) (by norm_num) (by norm_num) (by norm_num)
    rw [m7l_cw1] at hc
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hc
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, inv_inv,
      Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons]
    rw [hc]
    simp [List.ofFn_succ, List.prod_cons, pow_succ, mul_assoc,
      Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons,
      show (1 : ZMod 7).val = 1 by decide +kernel]
  · have hc := gq_conj (i := 0) (j := 2) (by norm_num) (by norm_num) (by norm_num)
    rw [m7l_cw2] at hc
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hc
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, inv_inv,
      Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons]
    rw [hc]
    simp [List.ofFn_succ, List.prod_cons, pow_succ, mul_assoc,
      Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons,
      show (1 : ZMod 7).val = 1 by decide +kernel]
  · have hc := gq_conj (i := 0) (j := 3) (by norm_num) (by norm_num) (by norm_num)
    rw [m7l_cw3] at hc
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hc
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, inv_inv,
      Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons]
    rw [hc]
    simp [List.ofFn_succ, List.prod_cons, pow_succ, mul_assoc,
      Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons,
      show (1 : ZMod 7).val = 1 by decide +kernel]
  · have hc := gq_conj (i := 0) (j := 4) (by norm_num) (by norm_num) (by norm_num)
    rw [m7l_cw4] at hc
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hc
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, inv_inv,
      Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons]
    rw [hc]
    simp [List.ofFn_succ, List.prod_cons, pow_succ, mul_assoc,
      Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons,
      show (1 : ZMod 7).val = 1 by decide +kernel]

private theorem m7l_actMat_h :
    CommData.actMat 7 ![gq 1, gq 2, gq 3, gq 4] (gq 5) m7M (gw m7hW)⁻¹ =
      !![1, 1, 0, 2; 0, 1, 1, 0; 4, 0, 1, 5; 2, 0, 0, 3] := by
  have hD := gq_commData
  have hh := m7h_conj
  apply CommData.actMat_eq hD (R := !![1, 1, 0, 2; 0, 1, 1, 0; 4, 0, 1, 5; 2, 0, 0, 3])
    (c := fun _ => 0)
  intro i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, inv_inv,
      Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons]
    rw [hh.1]
    simp [List.ofFn_succ, List.prod_cons, pow_succ, mul_assoc,
      Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons,
      show (1 : ZMod 7).val = 1 by decide +kernel,
      show (2 : ZMod 7).val = 2 by decide +kernel]
  · simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, inv_inv,
      Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons]
    rw [hh.2.1]
    simp [List.ofFn_succ, List.prod_cons, pow_succ, mul_assoc,
      Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons,
      show (1 : ZMod 7).val = 1 by decide +kernel]
  · simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, inv_inv,
      Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons]
    rw [hh.2.2.1]
    simp [List.ofFn_succ, List.prod_cons, pow_succ, mul_assoc,
      Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons,
      show (1 : ZMod 7).val = 1 by decide +kernel,
      show (4 : ZMod 7).val = 4 by decide +kernel,
      show (5 : ZMod 7).val = 5 by decide +kernel]
  · simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, inv_inv,
      Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons]
    rw [hh.2.2.2.1]
    simp [List.ofFn_succ, List.prod_cons, pow_succ, mul_assoc,
      Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons,
      show (2 : ZMod 7).val = 2 by decide +kernel,
      show (3 : ZMod 7).val = 3 by decide +kernel]

private theorem m7l_f1f4_of_dich
    (hdich : ∀ N : Subgroup Gmat, N ≤ Subgroup.closure (Set.range ![gq 1, gq 2, gq 3, gq 4]) →
      gq 0 ^ 6 ∈ Subgroup.normalizer (N : Set Gmat) →
      gw m7hW ^ 6 ∈ Subgroup.normalizer (N : Set Gmat) →
        N ≤ Subgroup.zpowers (gq 5) ∨ N = Subgroup.closure (Set.range ![gq 1, gq 2, gq 3, gq 4]))
    (hno : ∀ C : Subgroup Gmat,
      ¬ LargeEvenPComponent 7 (Subgroup.centralizer ({gq 5} : Set Gmat)) C) :
    BMPCentralF1At 7 (gq 5) ∧ BMPCentralF4At 7 (gq 5) := by
  haveI hp7 : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  haveI hfin : Finite Gmat := inferInstance
  have hD : CommData 7 ![gq 1, gq 2, gq 3, gq 4] (gq 5) m7M := gq_commData
  have hG : (Nat.card Gmat).factorization 7 = 6 := m7l_factorization
  let Q : Subgroup Gmat := Subgroup.closure (Set.range ![gq 1, gq 2, gq 3, gq 4])
  let L : Subgroup Gmat :=
    Subgroup.closure ({gq 0, gq 1, gq 2, gq 3, gq 4, gw m7hW} : Set Gmat)
  let x0 : Gmat := (gq 0)⁻¹
  let S : Subgroup Gmat := Q ⊔ Subgroup.zpowers x0
  have hQL : Q ≤ L := by
    dsimp only [Q, L]
    refine Subgroup.closure_mono ?_
    rintro x ⟨i, rfl⟩
    fin_cases i <;> simp
  have hLN : L ≤ Subgroup.normalizer (Q : Set Gmat) := by
    dsimp only [L, Q]
    exact m7l_L_le_normalizer hD
  have hLz : ∀ l ∈ L, l * (gq 5) * l⁻¹ ∈ Subgroup.zpowers (gq 5) := by
    intro l hl
    have hcl : l * gq 5 = gq 5 * l :=
      Subgroup.mem_centralizer_singleton_iff.1
        (m7l_L_le_centralizer hD (by dsimp only [L] at hl; exact hl))
    rw [hcl, mul_assoc, mul_inv_cancel, mul_one]
    exact Subgroup.mem_zpowers (gq 5)
  have hgq0pow : gq 0 ^ 7 = 1 := gq_pow (i := 0) (by norm_num)
  have hx0not : x0 ∉ Q := by
    intro hxQ
    have h1 : CommData.actMat 7 ![gq 1, gq 2, gq 3, gq 4] (gq 5) m7M x0 = 1 :=
      hD.actMat_of_mem (by dsimp only [Q] at hxQ; exact hxQ)
    have h2 : (!![1, 1, 0, 0; 0, 1, 1, 0; 0, 0, 1, 1; 0, 0, 0, 1] :
        Matrix (Fin 4) (Fin 4) (ZMod 7)) = 1 := m7l_actMat_q0.symm.trans h1
    have h01 := congrFun (congrFun h2 0) 1
    simp [Matrix.one_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Fin.reduceFinMk] at h01
  have hgq0ne : gq 0 ≠ 1 := by
    intro h1
    exact hx0not (by dsimp only [x0]; rw [h1, inv_one]; exact Subgroup.one_mem Q)
  have hx0pow : orderOf x0 = 7 := by
    dsimp only [x0]
    rw [orderOf_inv]
    exact orderOf_eq_prime hgq0pow hgq0ne
  have hx0pow7 : x0 ^ 7 = 1 := by
    rw [← hx0pow]
    exact pow_orderOf_eq_one x0
  have hconj : ∀ g ∈ Q, x0⁻¹ * g * x0 ∈ Q := by
    intro g hg
    have h : gq 0 * g * (gq 0)⁻¹ ∈ Q :=
      CommData.conj_mem (fun i => by simpa only [inv_inv] using m7l_q0_conj_mem hD i) hg
    rwa [show gq 0 * g * (gq 0)⁻¹ = x0⁻¹ * g * x0 by dsimp only [x0]; rw [inv_inv]] at h
  have hScard : Nat.card S = 7 ^ (Nat.card Gmat).factorization 7 := by
    have hS : Nat.card S = Nat.card Q * 7 := by
      dsimp only [S]
      exact card_sup_zpowers hx0pow hx0not hconj
    rw [hS]
    have hQ : Nat.card Q = 7 ^ 5 := by
      dsimp only [Q]
      simpa using hD.card_eq
    rw [hQ, hG]
    norm_num
  have hx0N : x0 ∈ Subgroup.normalizer (Q : Set Gmat) := by
    have h : gq 0 ∈ Subgroup.normalizer (Q : Set Gmat) :=
      m7l_mem_normalizer (m7l_q0_conj_mem hD)
    simpa only [x0] using Subgroup.inv_mem _ h
  have hSN : S ≤ Subgroup.normalizer (Q : Set Gmat) := by
    dsimp only [S]
    exact sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 hx0N)
  have hx0L : x0 ∈ L := by
    dsimp only [L]
    exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
  have hSL : S ≤ L := by
    dsimp only [S]
    exact sup_le hQL (Subgroup.zpowers_le.2 hx0L)
  have hL : (Nat.card Gmat).factorization 7 ≤ (Nat.card L).factorization 7 := by
    have hSdvd : Nat.card S ∣ Nat.card L := Subgroup.card_dvd_of_le hSL
    have hle := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2 hSdvd 7
    rw [hScard, Nat.Prime.factorization_pow Nat.prime_seven, Finsupp.single_eq_same] at hle
    exact hle
  have hx0conj : ∀ i, x0⁻¹ * (![gq 1, gq 2, gq 3, gq 4] i) * x0 ∈
      Subgroup.closure (Set.range ![gq 1, gq 2, gq 3, gq 4]) := by
    intro i
    simpa only [x0, inv_inv] using m7l_q0_conj_mem hD i
  have hx0M : CommData.actMat 7 ![gq 1, gq 2, gq 3, gq 4] (gq 5) m7M x0 ≠ 1 := by
    intro h1
    have h2 : (!![1, 1, 0, 0; 0, 1, 1, 0; 0, 0, 1, 1; 0, 0, 0, 1] :
        Matrix (Fin 4) (Fin 4) (ZMod 7)) = 1 := m7l_actMat_q0.symm.trans h1
    have h01 := congrFun (congrFun h2 0) 1
    simp [Matrix.one_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Fin.reduceFinMk] at h01
  have hSC : S ⊓ Subgroup.centralizer (Q : Set Gmat) = Subgroup.zpowers (gq 5) := by
    dsimp only [S, Q]
    exact commData_sup_zpowers_inf_centralizer hD hx0pow7 hx0conj hx0M
  have hSCle : Nat.card ↥(S ⊓ Subgroup.centralizer (Q : Set Gmat)) ≤ 7 := by
    rw [hSC, Nat.card_zpowers, hD.orderOf_z]
  have hCQ : ∀ P : Subgroup Gmat,
      P ≤ Subgroup.centralizer (Q : Set Gmat) → IsPGroup 7 P → Nat.card P ≤ 7 :=
    commData_card_le_of_sylow hScard hSN hSCle
  have hdich' : ∀ N : Subgroup Gmat, N ≤ Q →
      (∀ a ∈ L, a ^ 6 ∈ Subgroup.normalizer (N : Set Gmat)) →
        N ≤ Subgroup.zpowers (gq 5) ∨ N = Q := by
    intro N hNQ hN
    have hgq0L : gq 0 ∈ L := by
      dsimp only [L]
      exact Subgroup.subset_closure (by simp)
    have hhL : gw m7hW ∈ L := by
      dsimp only [L]
      exact Subgroup.subset_closure (by simp)
    exact hdich N (by dsimp only [Q] at hNQ; exact hNQ) (hN (gq 0) hgq0L) (hN (gw m7hW) hhL)
  have hg1 : LargeEvenPPrimeCore 7 ↥(Subgroup.centralizer ({gq 5} : Set Gmat)) = ⊥ := by
    have h :=
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.oPrimeCoreTrivialAt_seven_Gmat_of_classes
        CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenCensus.monsterSevenClasses
        (gq 5) hD.orderOf_z
    exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp h
  exact bmPCentralF1At_F4At_of_commData Nat.prime_seven (by norm_num) hD
    (i₀ := 0) (j₀ := 2) (m7l_hz hD) L hQL hLN hLz hL hCQ (m := 6) (by norm_num) hdich' hg1 hno

private theorem m7d_gq0_six :
    gq 0 ^ 6 = (gq 0)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← pow_succ', show 6 + 1 = 7 by norm_num]
  exact gq_pow (i := 0) (by norm_num)

private theorem m7d_h_inv_conj_mem
    (hD : CommData 7 ![gq 1, gq 2, gq 3, gq 4] (gq 5) m7M) :
    ∀ g ∈ Subgroup.closure (Set.range ![gq 1, gq 2, gq 3, gq 4]),
      (gw m7hW)⁻¹ * g * gw m7hW ∈
        Subgroup.closure (Set.range ![gq 1, gq 2, gq 3, gq 4]) := by
  have hN : gw m7hW ∈ Subgroup.normalizer
      (Subgroup.closure (Set.range ![gq 1, gq 2, gq 3, gq 4]) : Set Gmat) :=
    m7l_mem_normalizer (m7l_h_conj_mem hD)
  have hinv := Subgroup.inv_mem _ hN
  intro g hg
  simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp hinv g).mp hg

private theorem m7d_conj_mem
    (hD : CommData 7 ![gq 1, gq 2, gq 3, gq 4] (gq 5) m7M) :
    ∀ i j, (![gq 0 ^ 6, gw m7hW ^ 6] i)⁻¹ * ![gq 1, gq 2, gq 3, gq 4] j *
        ![gq 0 ^ 6, gw m7hW ^ 6] i ∈
      Subgroup.closure (Set.range ![gq 1, gq 2, gq 3, gq 4]) := by
  intro i j
  fin_cases i
  · change (gq 0 ^ 6)⁻¹ * ![gq 1, gq 2, gq 3, gq 4] j * gq 0 ^ 6 ∈
      Subgroup.closure (Set.range ![gq 1, gq 2, gq 3, gq 4])
    rw [m7d_gq0_six, inv_inv]
    exact m7l_q0_conj_mem hD j
  · change (gw m7hW ^ 6)⁻¹ * ![gq 1, gq 2, gq 3, gq 4] j * gw m7hW ^ 6 ∈
      Subgroup.closure (Set.range ![gq 1, gq 2, gq 3, gq 4])
    exact conj_pow_mem (m7d_h_inv_conj_mem hD) 6
      (Subgroup.subset_closure (Set.mem_range_self j))

private theorem m7d_actMat_q0 :
    CommData.actMat 7 ![gq 1, gq 2, gq 3, gq 4] (gq 5) m7M (gq 0 ^ 6) =
      !![1, 1, 0, 0; 0, 1, 1, 0; 0, 0, 1, 1; 0, 0, 0, 1] := by
  rw [m7d_gq0_six]
  exact m7l_actMat_q0

private theorem m7d_actMat_h
    (hD : CommData 7 ![gq 1, gq 2, gq 3, gq 4] (gq 5) m7M) :
    CommData.actMat 7 ![gq 1, gq 2, gq 3, gq 4] (gq 5) m7M (gw m7hW) =
      !![3, 4, 3, 0; 2, 6, 1, 4; 5, 2, 6, 3; 5, 2, 5, 5] := by
  let A : Matrix (Fin 4) (Fin 4) (ZMod 7) :=
    !![1, 1, 0, 2; 0, 1, 1, 0; 4, 0, 1, 5; 2, 0, 0, 3]
  let B : Matrix (Fin 4) (Fin 4) (ZMod 7) :=
    !![3, 4, 3, 0; 2, 6, 1, 4; 5, 2, 6, 3; 5, 2, 5, 5]
  have hA : CommData.actMat 7 ![gq 1, gq 2, gq 3, gq 4] (gq 5) m7M (gw m7hW)⁻¹ = A :=
    m7l_actMat_h
  have hxG := m7d_h_inv_conj_mem hD
  have hhinv : ∀ i, ((gw m7hW)⁻¹)⁻¹ * ![gq 1, gq 2, gq 3, gq 4] i * (gw m7hW)⁻¹ ∈
      Subgroup.closure (Set.range ![gq 1, gq 2, gq 3, gq 4]) :=
    fun i => by simpa only [inv_inv] using m7l_h_conj_mem hD i
  have h1 : CommData.actMat 7 ![gq 1, gq 2, gq 3, gq 4] (gq 5) m7M (gw m7hW) * A = 1 := by
    have hm := CommData.actMat_mul hD (b := gw m7hW) (c := (gw m7hW)⁻¹)
      (fun i => hxG _ (Subgroup.subset_closure (Set.mem_range_self i))) hhinv
    rw [mul_inv_cancel, CommData.actMat_one hD, hA] at hm
    exact hm.symm
  have hAB : A * B = 1 := by decide +kernel
  have hfin : CommData.actMat 7 ![gq 1, gq 2, gq 3, gq 4] (gq 5) m7M (gw m7hW) = B := by
    calc
      CommData.actMat 7 ![gq 1, gq 2, gq 3, gq 4] (gq 5) m7M (gw m7hW)
          = CommData.actMat 7 ![gq 1, gq 2, gq 3, gq 4] (gq 5) m7M (gw m7hW) * 1 :=
            (mul_one _).symm
      _ = CommData.actMat 7 ![gq 1, gq 2, gq 3, gq 4] (gq 5) m7M (gw m7hW) * (A * B) := by
            rw [hAB]
      _ = (CommData.actMat 7 ![gq 1, gq 2, gq 3, gq 4] (gq 5) m7M (gw m7hW) * A) * B :=
            (mul_assoc _ _ _).symm
      _ = 1 * B := by rw [h1]
      _ = B := one_mul B
  simpa only [B] using hfin

private theorem m7d_actMat_h_pow
    (hD : CommData 7 ![gq 1, gq 2, gq 3, gq 4] (gq 5) m7M) (k : ℕ) :
    CommData.actMat 7 ![gq 1, gq 2, gq 3, gq 4] (gq 5) m7M (gw m7hW ^ k) =
      (CommData.actMat 7 ![gq 1, gq 2, gq 3, gq 4] (gq 5) m7M (gw m7hW)) ^ k := by
  have hxG := m7d_h_inv_conj_mem hD
  induction k with
  | zero => rw [pow_zero, pow_zero, CommData.actMat_one hD]
  | succ k ih =>
    rw [pow_succ']
    rw [CommData.actMat_mul hD (b := gw m7hW) (c := gw m7hW ^ k)
      (fun i => hxG _ (Subgroup.subset_closure (Set.mem_range_self i)))
      (fun i => conj_pow_mem hxG k (Subgroup.subset_closure (Set.mem_range_self i)))]
    rw [ih, pow_succ']

private theorem m7d_actMat_h6
    (hD : CommData 7 ![gq 1, gq 2, gq 3, gq 4] (gq 5) m7M) :
    CommData.actMat 7 ![gq 1, gq 2, gq 3, gq 4] (gq 5) m7M (gw m7hW ^ 6) =
      !![3, 4, 3, 0; 2, 6, 1, 4; 5, 2, 6, 3; 5, 2, 5, 5] := by
  rw [m7d_actMat_h_pow hD 6, m7d_actMat_h hD]
  decide +kernel

private theorem m7d_irreducible
    (hD : CommData 7 ![gq 1, gq 2, gq 3, gq 4] (gq 5) m7M) :
    ∀ W : Submodule (ZMod 7) (Fin 4 → ZMod 7),
      (∀ i, ∀ v ∈ W, Matrix.vecMul v
        (CommData.actMat 7 ![gq 1, gq 2, gq 3, gq 4] (gq 5) m7M
          (![gq 0 ^ 6, gw m7hW ^ 6] i)) ∈ W) →
      W = ⊥ ∨ W = ⊤ := by
  intro W hW
  refine m7_quot_irreducible W ?_ ?_
  · intro v hv
    have h := hW 0 v hv
    change Matrix.vecMul v (CommData.actMat 7 ![gq 1, gq 2, gq 3, gq 4] (gq 5) m7M
      (gq 0 ^ 6)) ∈ W at h
    rwa [m7d_actMat_q0] at h
  · intro v hv
    have h := hW 1 v hv
    change Matrix.vecMul v (CommData.actMat 7 ![gq 1, gq 2, gq 3, gq 4] (gq 5) m7M
      (gw m7hW ^ 6)) ∈ W at h
    rwa [m7d_actMat_h6 hD] at h

private theorem m7d_dich :
    ∀ N : Subgroup Gmat, N ≤ Subgroup.closure (Set.range ![gq 1, gq 2, gq 3, gq 4]) →
      gq 0 ^ 6 ∈ Subgroup.normalizer (N : Set Gmat) →
      gw m7hW ^ 6 ∈ Subgroup.normalizer (N : Set Gmat) →
        N ≤ Subgroup.zpowers (gq 5) ∨
          N = Subgroup.closure (Set.range ![gq 1, gq 2, gq 3, gq 4]) := by
  intro N hNQ h0 hh
  haveI hp7 : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hD : CommData 7 ![gq 1, gq 2, gq 3, gq 4] (gq 5) m7M := gq_commData
  refine commData_dich_of_irred (hD := hD) (i₀ := 0) (j₀ := 2) (hz := m7l_hz hD)
    (a := ![gq 0 ^ 6, gw m7hW ^ 6]) (m7d_conj_mem hD) (m7d_irreducible hD) N hNQ ?_
  refine (Fin.forall_fin_two).2 ⟨?_, ?_⟩
  · change gq 0 ^ 6 ∈ Subgroup.normalizer (N : Set Gmat)
    exact h0
  · change gw m7hW ^ 6 ∈ Subgroup.normalizer (N : Set Gmat)
    exact hh

theorem gmat_bmPCentralF1At_F4At_q5
    (hno : ∀ C : Subgroup Gmat,
      ¬ LargeEvenPComponent 7 (Subgroup.centralizer ({gq 5} : Set Gmat)) C) :
    BMPCentralF1At 7 (gq 5) ∧ BMPCentralF4At 7 (gq 5) :=
  m7l_f1f4_of_dich m7d_dich hno

end CFSG.StandardType.SporadicShape
