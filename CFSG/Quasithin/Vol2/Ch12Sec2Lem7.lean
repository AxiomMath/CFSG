module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem7One
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem7StmtsNoN
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem8Cases
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitStmts
public import CFSG.Quasithin.Vol2.Ch12Sec2Action
public import CFSG.Quasithin.Vol2.Ch1Nine
public import CFSG.Quasithin.Vol2.Ch1Eight
public import CFSG.Quasithin.Vol2.Ch1Chief
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.Quasithin.Vol2.Ch1Prop121
public import CFSG.Quasithin.H13.VolIA36
public import CFSG.Quasithin.H13.VolIAltCoverSeven
public import CFSG.Quasithin.H13.L1332Inputs
public import CFSG.Quasithin.Background.G2L2
public import CFSG.Quasithin.Background.G64NatSec
public import CFSG.Quasithin.Background.B4ModelsWitness
public import Certificates.Certificate13
public import Certificates.Certificate14
public import Certificates.Certificate15
public import Certificates.Certificate16
public import Certificates.Certificate17
public import Certificates.Certificate18
public import Certificates.Certificate19
public import Certificates.Certificate20
public import Certificates.Certificate21
public import Certificates.Certificate22
public import Certificates.Certificate23
public import Certificates.Certificate24
public import Certificates.Certificate25
public import Certificates.Certificate26
public import Certificates.Certificate27
public import Certificates.Certificate28
public import Certificates.Certificate29
public import Certificates.Certificate30
public import Certificates.Certificate31
public import Certificates.Certificate32
public import Certificates.Certificate33
public import Certificates.Certificate34
public import Certificates.Certificate35
public import Certificates.Certificate36
public import Certificates.Certificate37
public import Certificates.Certificate38
public import Certificates.Certificate39
public import Certificates.Certificate40
public import Certificates.Certificate41
public import Certificates.Certificate43
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123
public import Certificates.Certificate3017
public import Certificates.Certificate3029
public import Certificates.Certificate3084
public import Certificates.Certificate3086
public import Certificates.Certificate3119
public import Certificates.Certificate3120
public import Certificates.Certificate3139
public import Certificates.Certificate3167
public import Certificates.Certificate3168
public import Certificates.Certificate3172
public import Certificates.Certificate8010
public import Certificates.Certificate8011
public import Certificates.Certificate8012
public import Certificates.Certificate8013
public import Certificates.Certificate8014
public import Certificates.Certificate8015
public import Certificates.Certificate8016
public import Certificates.Certificate8017
public import Certificates.Certificate8018
public import Certificates.Certificate8019
public import Certificates.Certificate8020
public import Certificates.Certificate8021
public import Certificates.Certificate8022
public import Certificates.Certificate8024
public import Certificates.Certificate8025
public import Certificates.Certificate8026
public import Certificates.Certificate8027
public import Certificates.Certificate8028
public import Certificates.Certificate8029
public import Certificates.Certificate8030
public import Certificates.Certificate8031
public import Certificates.Certificate8032
public import Certificates.Certificate8033
public import Certificates.Certificate4103
import CFSG.Adapters.LieModelSmallOrders
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.Quasithin.Background.A3Structure318Defs
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.Quasithin.Background.E2Hyp
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem6
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem7Stmts
public import CFSG.Quasithin.Vol2.Ch1Unique
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M22
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CPrime
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralAut

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

namespace Lem7

theorem exists_maximalLocal_ge {T X : Subgroup G} (hX : quasithinIsLocal T X) :
    ∃ Y : Subgroup G, X ≤ Y ∧ quasithinIsMaximalLocal T Y := by
  classical
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  obtain ⟨Y, ⟨hY, hXY⟩, hmax⟩ := Set.exists_max_image
    {Y : Subgroup G | quasithinIsLocal T Y ∧ X ≤ Y} (fun Y : Subgroup G => Nat.card Y)
    (Set.toFinite _) ⟨X, hX, le_rfl⟩
  exact ⟨Y, hXY, hY, fun K hK hYK =>
    (Subgroup.eq_of_le_of_card_ge hYK (hmax K ⟨hK, hXY.trans hYK⟩)).symm⟩

omit [Finite G] in
theorem isLocal_of_mem_cComp {T X H : Subgroup G} (hT : quasithinIsSylowTwo T) (hHT : InH T H)
    (hX : X ∈ cComp H) (hHX : H = X ⊔ T) : quasithinIsLocal T X := by
  have hsyl := (isSylowTwoOf_of_isSylowTwo hT hHT.1).2.2
  subst hHX
  exact ⟨hT.1, hX, hsyl, hHT.2⟩

theorem oTwoUpper_eq {T X H : Subgroup G} (hT : IsPGroup 2 T) (hX : X ∈ cComp H)
    (hHX : H = X ⊔ T) (hTX : T ≤ Subgroup.normalizer (X : Set G)) : oTwoUpper H = X := by
  have hXH : X ≤ H := hHX ▸ le_sup_left
  exact (eq_oTwoUpper_of_pow_mem hXH
    (fun h hh => exists_pow_two_pow_mem_of_le_normalizer hTX hT (hHX ▸ hh))
    (eq_oTwoUpper_of_perfect (perfect_of_mem_cComp hX))).symm

theorem card_of_lieModel_psu_three_three {Q : Type} [Group Q] (h : LieModel Q .PSU 3 3 1) :
    Nat.card Q = 6048 :=
  CFSG.Blueprint.LieModel.card_psu_three_three h

theorem card_sl_three_four_five {n : ℕ} (hn : n = 3 ∨ n = 4 ∨ n = 5) :
    Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) = 168 ∨
      Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) = 20160 ∨
      Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) = 9999360 := by
  rcases hn with rfl | rfl | rfl
  · left
    rw [card_sl_zmod_two]
    decide
  · right; left
    rw [card_sl_zmod_two]
    decide
  · right; right
    exact Lem8.card_sl_five_zmod_two

theorem card_of_altSeven (hA7 : AltNaturalCoverSeven) (h1222 : Stmt12_2_2)
    {T Y VY : Subgroup G} (hHy : Hyp1223 G T Y VY)
    (e7 : (↥Y ⧸ CFSG.pCore 2 ↥Y) ⧸ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) ≃*
      alternatingGroup (Fin 7)) :
    Nat.card VY = 2 ^ 4 ∨ Nat.card VY = 2 ^ 6 := by
  obtain ⟨-, -, hall⟩ := ((h1222 G T hHy.simple hHy.nonabelian hHy.qtke hHy.sylow).resolve_left
    hHy.notAlt) Y hHy.maximal hHy.faithful hHy.quasisimple
  obtain ⟨⟨hVT, -, hred, -⟩, -, -, hcomm, hmod⟩ := hall VY hHy.irrPlus
  have hq := hHy.quasisimple
  obtain ⟨-, -, ⟨z, hz⟩⟩ := SteinbergBM.five_core_quotient_center_odd hq
  have h7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [Lem8.card_alternatingGroup_fin (by norm_num)]
    decide
  have hQ : Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) = 2520 * (2 * z + 1) := by
    rw [(Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)).card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr e7.toEquiv, h7, hz]
  have hKV : Y ≤ Subgroup.normalizer (VY : Set G) := hHy.irrPlus.2.2.1
  have hc : ⁅VY, Y⁆ = VY := hHy.irrPlus.2.2.2.1
  have hVLT : VY ≤ Y ⊔ T := hVT.trans le_sup_right
  have hsq : ∀ v : ↥VY, v ^ 2 = 1 := by
    intro v
    have := hred.isElementaryAbelian
    have h2 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := VY.subgroupOf (Y ⊔ T))
      (⟨v, hVLT v.2⟩ : ↥(Y ⊔ T)) (Subgroup.mem_subgroupOf.mpr v.2)
    exact Subtype.ext (by simpa using congrArg Subtype.val h2)
  have hcomm' := commV_autOn_eq_top hKV hc
  have hfix := fixV_autOn_eq hKV
  rcases hmod with ⟨n, hn, ⟨e⟩, -⟩ | ⟨⟨e⟩, -, -⟩ | ⟨⟨e⟩, -, -⟩ |
      ⟨n, hn5, hn8, ⟨φ, hφ, -⟩, halt⟩ | ⟨hcard, -⟩ | ⟨hU, -⟩ | ⟨-, -, ⟨e6⟩, -⟩
  · exfalso
    rw [Nat.card_congr e.toEquiv] at hQ
    rcases card_sl_three_four_five hn with h | h | h <;> rw [h] at hQ <;> omega
  · exfalso
    rw [Nat.card_congr e.toEquiv] at hQ
    rcases card_sl_three_four_five (Or.inl rfl) with h | h | h <;> rw [h] at hQ <;> omega
  · exfalso
    rw [Nat.card_congr e.toEquiv, Lem8.card_sl_five_zmod_two] at hQ
    omega
  · have hle := pCore_le_ker_of_surjective_alternating hn5 φ hφ
    have : IsSimpleGroup (alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; exact hn5)
    obtain ⟨-, en, -⟩ := SteinbergBM.five_quasisimple_centerless_image hq
      (alternatingGroup_nonabelian (by omega)) (QuotientGroup.lift (CFSG.pCore 2 ↥Y) φ hle)
      (QuotientGroup.lift_surjective_of_surjective _ φ hφ hle)
    have hn7 : n = 7 := by
      have h1 := Nat.card_congr (en.symm.trans e7).toEquiv
      rw [h7, Lem8.card_alternatingGroup_fin (by omega)] at h1
      interval_cases n <;> first | rfl | exact absurd h1 (by decide)
    subst hn7
    have hZ := hA7 ↥VY hsq (autOn Y VY) _ hfix.symm.le hcomm' halt
    rw [hZ] at halt
    obtain ⟨π, hπ⟩ := halt
    have hcard := G64.RealizesVia.card_eq hπ
    have hsec := Explicit.card_dn_sec (n := 7) (by norm_num) .alternating
    right
    rw [Subgroup.card_top, Subgroup.card_bot, mul_one] at hcard
    split_ifs at hsec with he
    · exact absurd he (by decide)
    · exact hcard.trans hsec
  · exact Or.inl hcard
  · exfalso
    rw [card_of_lieModel_psu_three_three hU] at hQ
    omega
  · exfalso
    have h1 := Nat.card_congr (e6.symm.trans e7).toEquiv
    rw [h7, Lem8.card_alternatingGroup_fin (by norm_num)] at h1
    exact absurd h1 (by decide)

end Lem7

open Lem7

theorem stmt12_2_7_nonsolvable (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (h6220 : Stmt6_2_20) (hE22 : E2.E22StatementNoN) (h36 : A36ForSQTK) (h37 : A37ForSQTK)
    (h128 : Lemma128One)
    (hA7 : AltNaturalCoverSeven) (hEq : Lem1227ListEqNoN) (hLt : Lem1227ListLtNoN)
    (hNQ : Lem1227NotQuasisimple) {T L V H : Subgroup G} (hH : Hyp1223 G T L V)
    (hCZ : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤
      Subgroup.normalizer (L : Set G))
    (hHs : IsHStar T (Subgroup.normalizer (L : Set G)) H) (hns : ¬ Group.IsSolvable ↥H) :
    LieModel (↥(oTwoUpper H) ⧸ CFSG.pCore 2 ↥(oTwoUpper H)) .PSL 2 2 2 ∧
      ∃ Y : Subgroup G, oTwoUpper H ≤ Y ∧ quasithinIsMaximalLocal T Y ∧
        quasithinIsFaithfulLocal T Y ∧
        ((Y = oTwoUpper H ∧ IsA5ModuleSum (oTwoUpper H) ⁅VZ T H, oTwoUpper H⁆) ∨
          (Nonempty ((↥Y ⧸ CFSG.pCore 2 ↥Y) ⧸ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) ≃*
              alternatingGroup (Fin 7)) ∧
            CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) ∧
            T ≤ Subgroup.normalizer (Y : Set G) ∧
            ∀ VY : Subgroup G, IsIrrPlusIn Y (reducedAggregate (Y ⊔ T)) T VY →
              T ≤ Subgroup.normalizer (VY : Set G) ∧
                (Nat.card VY = 2 ^ 4 ∨ Nat.card VY = 2 ^ 6))) := by
  obtain ⟨S, rfl⟩ := exists_sylow_coe_eq hH.sylow
  set M := Subgroup.normalizer (L : Set G) with hMdef
  have hmin := minParabolic h331 hH hHs
  have hU := isTwoReducedIn_VZ hH hHs
  have hsqtk : SQTKGroup ↥H :=
    sqtkGroup_of_pCoreOf_ne_bot hH.qtke hH.simple hH.nonabelian hHs.1.2
  obtain ⟨⟨X, hXc, hHX, hXq0, hE⟩, -⟩ := hE22 G H (S : Subgroup G) (H ⊓ M) hmin hsqtk hns
  have hXq : CFSG.IsQuasisimple (↥X ⧸ CFSG.pCore 2 ↥X) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥X 2).symm)
      (A3.isQuasisimple_iff_open.mpr hXq0)
  have hXV : ⁅VZ (S : Subgroup G) H, X⁆ ≠ ⊥ := by
    intro h
    have hXC : X ≤ Subgroup.centralizer (VZ (S : Subgroup G) H : Set G) :=
      Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h)
    apply hHs.2.1
    rw [hHX]
    exact sup_le (hXC.trans ((centralizer_VZ_le _ H).trans hCZ)) hH.normalizes
  have hXf : quasithinIsFaithfulLocal (S : Subgroup G) X :=
    have h2 : ∃ W : Subgroup G, IsTwoReducedIn H W ∧ ⁅W, X⁆ ≠ ⊥ := ⟨_, hU, hXV⟩
    ((lemma_1_2_10_of_a36 hH.qtke hH.simple hH.nonabelian h36 S hHs.1
      hXc).out 1 2).mpr h2
  obtain ⟨Y, hXY, hYmax⟩ := exists_maximalLocal_ge hXf.1
  have hYf := (lemma_1_2_9_one hH.qtke hH.simple hH.nonabelian h37 h128 hH.sylow hXf hYmax.1
    hXY).2
  have hYq := hNQ G S L V H X Y hH hCZ hHs hns hXc hHX hXq hXY hYmax hYf
  obtain ⟨hTY, ⟨VY, hVY⟩, hallY⟩ := ((h1222 G S hH.simple hH.nonabelian hH.qtke
    hH.sylow).resolve_left hH.notAlt) Y hYmax hYf hYq
  have hHy : Hyp1223 G S Y VY :=
    ⟨hH.simple, hH.nonabelian, hH.qtke, hH.sylow, hH.notAlt, hYmax, hYf, hYq, hTY, hVY⟩
  obtain ⟨⟨-, hTVY, -, -⟩, -, -, hcommY, hmodY⟩ := hallY VY hVY
  have hTX : (S : Subgroup G) ≤ Subgroup.normalizer (X : Set G) := by
    have heq := lemma_1_2_8_one hH.qtke hH.simple hH.nonabelian h37 h128 hXf.1 hYmax.1 hXY
    intro t ht
    have ht' : t ∈ (S : Subgroup G) ⊓ Subgroup.normalizer (Y : Set G) := ⟨ht, hTY ht⟩
    rw [← heq] at ht'
    exact ht'.2
  have hK : oTwoUpper H = X := oTwoUpper_eq hH.sylow.1 hXc hHX hTX
  rw [hK]
  rcases eq_or_lt_of_le hXY with hXYe | hXYl
  ·
    subst hXYe
    have hLie := hEq G S X VY H (H ⊓ M) hHy hTVY ⟨hcommY, hmodY⟩ hHX hmin hE
    refine ⟨hLie, X, le_rfl, hYmax, hYf, Or.inl ⟨rfl, ?_⟩⟩
    have hNX : quasithinIsMaxTwoLocal (Subgroup.normalizer (X : Set G)) := by
      obtain ⟨⟨hmax2, -, -⟩, -⟩ :=
        (h331 G S hH.simple hH.nonabelian hH.qtke hH.sylow).2 X hYmax hYq
      rwa [conjClosure_eq_self_of_normalizes hTY] at hmax2
    have hVH : VZ (S : Subgroup G) H ≤ X ⊔ S := hHX ▸ hU.1
    have hred : IsPrimeReduced 2 ((VZ (S : Subgroup G) H).subgroupOf (X ⊔ S)) :=
      hHX ▸ (isTwoReducedIn_iff_isPrimeReduced_subgroupOf.mp hU).2
    rcases h6220 G S (Subgroup.normalizer (X : Set G)) X (VZ (S : Subgroup G) H) 2 hH.simple
        hH.nonabelian hH.qtke hH.sylow hNX hTY hYmax hYf Subgroup.le_normalizer le_rfl le_rfl
        hLie hVH hred hXV with ⟨-, hA5, -⟩ | hLie' | hM22 | hM23
    · exact hA5
    · exfalso
      rcases hLie' with h | h
      · exact hH.notAlt (Or.inl h)
      · exact hH.notAlt (Or.inr (Or.inl h))
    · exact absurd (Or.inr (Or.inr (Or.inl hM22))) hH.notAlt
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inl hM23)))) hH.notAlt
  ·
    obtain ⟨hLie, ⟨e7⟩⟩ :=
      hLt G S X Y VY H (H ⊓ M) hHy hTVY ⟨hcommY, hmodY⟩ hXf.1 hXYl hTX hXq hHX hmin hE
    refine ⟨hLie, Y, hXY, hYmax, hYf, Or.inr ⟨⟨e7⟩, hYq, hTY, fun VY' hVY' => ?_⟩⟩
    obtain ⟨⟨-, hTVY', -, -⟩, -⟩ := hallY VY' hVY'
    have hHy' : Hyp1223 G S Y VY' :=
      ⟨hH.simple, hH.nonabelian, hH.qtke, hH.sylow, hH.notAlt, hYmax, hYf, hYq, hTY, hVY'⟩
    exact ⟨hTVY', card_of_altSeven hA7 h1222 hHy' e7⟩

theorem stmt12_2_7_of_inputs (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h6220 : Stmt6_2_20) (hE22 : E2.E22StatementNoN) (h36 : A36ForSQTK) (h37 : A37ForSQTK)
    (h128 : Lemma128One)
    (hA7 : AltNaturalCoverSeven) (hEq : Lem1227ListEqNoN) (hLt : Lem1227ListLtNoN)
    (hNQ : Lem1227NotQuasisimple) : Stmt12_2_7 := by
  intro G _ _ T L V H hH hCZ hHs
  have h1226 := stmt12_2_6_of h1222 h323
  exact ⟨stmt12_2_7_one h331 h1222 h1226 hH hCZ hHs, fun hns =>
    stmt12_2_7_nonsolvable h331 h1222 h6220 hE22 h36 h37 h128 hA7 hEq hLt hNQ hH hCZ hHs hns⟩

theorem stmt12_2_7_of
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h6220 : Stmt6_2_20) (hE22 : E2.E22StatementNoN) (h37 : A37ForSQTK) (h128 : Lemma128One)
    (hEq : Lem1227ListEqNoN) (hLt : Lem1227ListLtNoN) (hNQ : Lem1227NotQuasisimple) :
    Stmt12_2_7 :=
  stmt12_2_7_of_inputs h331 h1222 h323 h6220 hE22 VolI.a36ForSQTK_holds h37 h128
    VolI.altNaturalCoverSeven_holds hEq hLt hNQ

end CFSG.Quasithin.H13
