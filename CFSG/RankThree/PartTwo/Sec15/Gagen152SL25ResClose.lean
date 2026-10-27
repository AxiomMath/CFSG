module

public import CFSG.RankThree.PartTwo.Sec15.Gagen152SL25ResMain
public import CFSG.RankThree.PartTwo.J2Residue.KFacts
public import CFSG.RankThree.PartTwo.J2Residue.Config
import CFSG.RankThree.PartTwo.J2Residue.Alpha
import CFSG.RankThree.PartTwo.J2Residue.Beta
import CFSG.RankThree.PartTwo.Sec16.Item166CtrLB
import CFSG.RankThree.PartTwo.Sec15.Liebeck156Theta
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Gagen152SL25Res

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L M X B : Subgroup G}
  {b d : G} {Lb : Subgroup G} {p : ℕ} {P : Subgroup G} {e : G}

private theorem theta_facts (C : Subgroup G) :
    Group.IsSolvable (inSubgroup (aschbacherSolvableCore 3) C) ∧
      ¬ 3 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) C) ∧
      inSubgroup (aschbacherSolvableCore 3) C ≤ C ∧
      Subgroup.normalizer (C : Set G) ≤
        Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) C : Set G) ∧
      CFSG.Open.pCoreOf 2 (inSubgroup (aschbacherSolvableCore 3) C) ≤
        CFSG.Open.pCoreOf 2 C := by
  obtain ⟨hsol, hchar, h3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥C) Nat.prime_three
  have hN : Subgroup.normalizer (C : Set G) ≤
      Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) C : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _
  have hle : inSubgroup (aschbacherSolvableCore 3) C ≤ C := Subgroup.map_subtype_le _
  refine ⟨Group.isSolvable_of_surjective
      (f := ((aschbacherSolvableCore 3 ↥C).equivMapOfInjective C.subtype C.subtype_injective
        : _ ≃* _).toMonoidHom) (MulEquiv.surjective _), ?_, hle, hN, ?_⟩
  · rw [inSubgroup, Subgroup.card_map_of_injective C.subtype_injective]
    exact h3
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hle)
      ((Subgroup.le_normalizer.trans hN).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)

private theorem ResCtx.pCoreOf_lB_le
    (h : ResCtx A c L M X B b d Lb p P e)
    (hθeq : inSubgroup (aschbacherSolvableCore 3) Lb = CFSG.Open.pCoreOf 2 Lb) :
    CFSG.Open.pCoreOf 2 (lB A B) ≤ CFSG.Open.pCoreOf 2 Lb := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hq, hZ, -, -, -⟩ := Item148HJ.resProj_facts h.sec15R.toSec14Std h.hyp h.config
  rw [Item148HJ.lB_eq_residual h.sec15R.toSec14Std h.hyp h.config]
  set J := inSubgroup perfectResidual (Lb ⊓ Subgroup.centralizer ({d} : Set G)) with hJ
  have hnot3 : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥J) := by
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥J)).exists_card_eq
    rw [hn]
    intro h3
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)
  rintro _ ⟨j, hj, rfl⟩
  have hjk : j ∈ (Item148HJ.resProj Lb d).ker :=
    Item148HJ.le_ker_of_normal _ hq hZ (CFSG.pCore_normal (p := 2) (G := ↥J)) hnot3 hj
  rw [← hθeq]
  exact (Item148HJ.mem_ker_resProj j).mp hjk

theorem ResCtx.j2Config
    (h : ResCtx A c L M X B b d Lb p P e)
    (hθeq : inSubgroup (aschbacherSolvableCore 3) Lb = CFSG.Open.pCoreOf 2 Lb) :
    J2Residue.J2Config Lb d (lB A B) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hLb, -, -, -, -, hdA, hd1, -, -⟩ :=
    Ronan152SL25.lbConfig_facts h.sec15R.isE27 h.hyp h.config
  obtain ⟨-, -, -, hJ, hdL, S, hdS, hSd⟩ := h.config
  have hlB := Item148HJ.lB_eq_residual h.sec15R.toSec14Std h.hyp h.config
  refine ⟨Sec6.isPerfect_of_mem_thetaComponentsAt (mem_lA_iff.mp hLb).1, hJ, hdL,
    orderOf_eq_prime (h.sec15R.toSec13Data.isElemAbelian.2 d hdA) hd1, ⟨S, hdS, hSd⟩, hlB,
    Sec16.Ctr166.isTripleCover_lB h.sec15R.toSec14Std h.hyp h.config, ?_,
    h.pCoreOf_lB_le hθeq⟩
  rw [hlB]
  exact Item148HJ.inf_le_residual h.sec15R.toSec14Std h.hyp h.config ⟨hdA, hdL⟩

theorem ResCtx.false_of_eq_bot
    (hG1 : J2Residue.KG1) (hfix : J2Residue.KJFix) (hsplit : J2Residue.KJSplit)
    (hcover : J2Residue.KJCover) (h142 : Item142AllS14) (h134 : Item134) (h48 : Sec4.Item4_8)
    (hcomp : Step143HJCompOne) (h : ResCtx A c L M X B b d Lb p P e)
    (hO2 : CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({e} : Set G)) = ⊥) : False := by
  obtain ⟨U, z, rfl, -, -, -, -, hU1, -, hθeq⟩ := h.exists_pCoreOf_data h142
  obtain ⟨K, hK, hBK, hKeq, -, -, -, -⟩ := h.exists_K_pCoreOf_data h142 h48 h134 hcomp
  have hJ := h.j2Config hθeq
  have hrk := h.sec15R.localRank_lt
  obtain ⟨hΘs, hΘ3, hΘe, hNΘ, hΘ2⟩ := theta_facts (Subgroup.centralizer ({e} : Set G))
  have hΘ1 := le_bot_iff.mp (hΘ2.trans hO2.le)
  have hθK : inSubgroup (aschbacherSolvableCore 3) K ≤
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({e} : Set G)) := by
    have := Liebeck156.theta_sSup_le (Set.singleton_subset_iff.mpr hK)
    rwa [sSup_singleton] at this
  have hUΘ := (pCoreOf_le_theta_of_eq_sup hBK hKeq).trans hθK
  by_cases hed : e ∈ Subgroup.zpowers d
  ·
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hzp : Subgroup.zpowers e = Subgroup.zpowers d := by
      have hoe : orderOf e = 3 :=
        orderOf_eq_prime (h.sec15R.toSec13Data.isElemAbelian.2 e h.mem_A) h.ne_one
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hed) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hoe, hJ.orderOf_d]
    have hCed : Subgroup.centralizer ({e} : Set G) = Subgroup.centralizer ({d} : Set G) := by
      rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure, hzp,
        Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    refine J2Residue.false_of_beta hG1 hfix hsplit hcover hrk hJ hU1 hΘs hΘ3 hΘ1 hUΘ
      (hΘe.trans hCed.le) (inf_le_right.trans ?_)
    rw [← hzp]
    refine (CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup _).trans ?_
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hNΘ
  ·
    obtain ⟨hbΩ, hLb, -, -, hbA, -, hdA, -, -, -⟩ :=
      Ronan152SL25.lbConfig_facts h.sec15R.isE27 h.hyp h.config
    have hb : orderOf b = 3 := by
      rw [← Nat.card_zpowers]
      exact (zpowers_mem_omegaA_iff.mp hbΩ).2.1
    have hbd : Commute b d :=
      congrArg Subtype.val (h.sec15R.isE27.1.1.is_comm.comm ⟨b, hbA⟩ ⟨d, hdA⟩)
    exact J2Residue.false_of_alpha hfix hsplit hcover hrk hJ hU1 (mem_lA_iff.mp hLb).1 hb hbd
      (h.config.1 ▸ h.mem_e) hed hΘs hΘ3 hΘ1 hUΘ hΘe (Subgroup.le_normalizer.trans hNΘ)

end Gagen152SL25Res

theorem step152SL25OneOmegaResR_of
    (hG1 : J2Residue.KG1) (hfix : J2Residue.KJFix) (hsplit : J2Residue.KJSplit)
    (hcover : J2Residue.KJCover) (h142 : Item142AllS14) (h134 : Item134) (h48 : Sec4.Item4_8)
    (hcomp : Step143HJCompOne) : Step152SL25OneOmegaResR := by
  intro G _ _ A c L hR hHJ M X hctx B b d Lb hB hc hcent hΩ p P hP hp3 hfr e heB heb hPe hO2
  exact Gagen152SL25Res.ResCtx.false_of_eq_bot hG1 hfix hsplit hcover h142 h134 h48 hcomp
    ⟨hR, hHJ, hctx, hB, hc, hcent, hΩ, hP, hp3, hfr, heB, heb, hPe⟩ hO2

end CFSG.RankThree.PartTwo.Sec15
