module

public import CFSG.RankThree.PartTwo.Sec15.Gagen152SL25ResD
public import CFSG.RankThree.PartTwo.Sec15.Gagen152SL25ResK
public import CFSG.RankThree.PartTwo.Sec15.Gagen152SL25ResP
public import CFSG.RankThree.PartTwo.Sec15.Gagen152SL25ResY
public import CFSG.RankThree.PartTwo.Sec15.Gagen152SL25ResEnd
public import CFSG.RankThree.PartTwo.Sec15.Gagen152SL25Cases
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec15.Item15Res7ProofQN
import CFSG.RankThree.PartTwo.Sec16.Item162Proof
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Gagen152SL25Res

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L M X B : Subgroup G}
  {b d : G} {Lb : Subgroup G} {p : ℕ} {P : Subgroup G} {e : G}

private theorem ResCtx.isZCentral_of_config
    (h : ResCtx A c L M X B b d Lb p P e) : IsZCentral Lb d := by
  obtain ⟨-, -, hJ, -, -, -, -, hd1, hdc, -⟩ :=
    Ronan152SL25.lbConfig_facts h.sec15R.isE27 h.hyp h.config
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  obtain ⟨hdL, S, hS1, hS2⟩ := hdc
  obtain ⟨-, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥Lb) Nat.prime_three
  obtain ⟨hSy, hZ⟩ := center_sylow_eq_zpowers_of_quot_j2 h415 hθ3 hJ hdL hd1 S hS1 hS2
  exact ⟨_, hSy, hZ⟩

theorem ResCtx.exists_pCoreOf_data
    (h142 : Item142AllS14) (h : ResCtx A c L M X B b d Lb p P e) :
    ∃ (U : Subgroup G) (z : G),
      U = CFSG.Open.pCoreOf 2 (lB A B) ∧ z ∈ U ∧
      z ∈ inSubgroup (aschbacherSolvableCore 3) Lb ∧ z ∉ oTwoOddIn X ∧ z ∈ X ∧ U ≠ ⊥ ∧
      CFSG.Open.pCoreOf 2 Lb ≠ ⊥ ∧
      inSubgroup (aschbacherSolvableCore 3) Lb = CFSG.Open.pCoreOf 2 Lb := by
  have hθeq : inSubgroup (aschbacherSolvableCore 3) Lb = CFSG.Open.pCoreOf 2 Lb := by
    obtain ⟨eJ⟩ := h.config.2.2.2.1
    simpa only [inSubgroup, CFSG.Open.pCoreOf] using
      congrArg (fun S : Subgroup ↥Lb => S.map Lb.subtype)
        (Ronan152SL25.theta_eq_pCore_two_of_j2 eJ)
  obtain ⟨D, hD, hDp, -, z, hzD, hzθ, hzO2Odd⟩ := h.exists_cover h142
  have hDX : D ≤ X := fun x hx => (hD hx).1.1
  have hDlB : D ≤ lB A B := by
    refine h.le_lB ?_ hDp
    intro x hx
    exact ⟨(hD hx).1.2, (hD hx).2⟩
  have hzLB : z ∈ lB A B := hDlB hzD
  have hnormLb : lB A B ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Lb : Set G) :=
    (h.lB_le.trans inf_le_left).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Lb)
  have hzN : z ∈ CFSG.Open.pCoreOf 2 Lb ⊓ lB A B := ⟨hθeq ▸ hzθ, hzLB⟩
  have hleU : CFSG.Open.pCoreOf 2 Lb ⊓ lB A B ≤ CFSG.Open.pCoreOf 2 (lB A B) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
      (Late.le_normalizer_inf hnormLb Subgroup.le_normalizer)
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Lb).to_le inf_le_left)
  have hzU : z ∈ CFSG.Open.pCoreOf 2 (lB A B) := hleU hzN
  have hz1 : z ≠ 1 := fun h1 => hzO2Odd (h1.symm ▸ (oTwoOddIn X).one_mem)
  refine ⟨CFSG.Open.pCoreOf 2 (lB A B), z, rfl, hzU, hzθ, hzO2Odd, hDX hzD, ?_, ?_, hθeq⟩
  · exact fun hbot => hz1 (Subgroup.mem_bot.mp (hbot ▸ hzU))
  · exact fun hbot => hz1 (Subgroup.mem_bot.mp (hbot ▸ (hθeq ▸ hzθ)))

theorem ResCtx.exists_K_pCoreOf_data
    (h142 : Item142AllS14) (h48 : Sec4.Item4_8) (h134 : Item134) (hcomp : Step143HJCompOne)
    (h : ResCtx A c L M X B b d Lb p P e) :
    ∃ K : Subgroup G, K ∈ thetaComponentsAt 3 e ∧ lB A B ≤ K ∧
      K = lB A B ⊔ inSubgroup (aschbacherSolvableCore 3) K ∧
      P ≤ inSubgroup (aschbacherSolvableCore 3) K ∧ P ∈ scriptQ A (lB A) ∧
      CFSG.Open.pCoreOf 2 (lB A B) ∈ scriptQ A (lB A) ∧
      A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (lB A B) : Set G) := by
  obtain ⟨D, hD, hDp, hDcov, -⟩ := h.exists_cover h142
  have hDX : D ≤ X := fun x hx => (hD hx).1.1
  have hDlB : D ≤ lB A B := by
    refine h.le_lB ?_ hDp
    intro x hx
    exact ⟨(hD hx).1.2, (hD hx).2⟩
  obtain ⟨K, hK, hBK, hKeq⟩ := h.exists_K h48 h134 hcomp
  have hDK : D ≤ K := hDlB.trans hBK
  have hXK : X ⊓ Subgroup.centralizer ({e} : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    h.le_normalizer_of_cover hK hDX hDK hDcov
  have hPK : P ≤ K := h.le_K hXK hDX hDK hDcov
  have hBKA : B ≤ Subgroup.normalizer (K : Set G) :=
    h.hyp.1.trans (h.A_le_normalizer hK hBK)
  have hPθK : P ≤ inSubgroup (aschbacherSolvableCore 3) K := h.le_theta hBKA hKeq hPK
  have hUθK : CFSG.Open.pCoreOf 2 (lB A B) ≤ inSubgroup (aschbacherSolvableCore 3) K :=
    pCoreOf_le_theta_of_eq_sup hBK hKeq
  have hAU : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (lB A B) : Set G) :=
    h.A_le_normalizer_lB.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (lB A B))
  have hUQ : CFSG.Open.pCoreOf 2 (lB A B) ∈ scriptQ A (lB A) :=
    Proof15Res7.mem_scriptQ_of_le_pPrimeCoreOf h.sec15R.toSec14Std h.mem_A
      (hUθK.trans (theta_le_pPrimeCoreOf hK)) hAU
  have hPQ : P ∈ scriptQ A (lB A) :=
    Proof15Res7.mem_scriptQ_of_le_pPrimeCoreOf h.sec15R.toSec14Std h.mem_A
      (hPθK.trans (theta_le_pPrimeCoreOf hK)) h.pdata.norm_p
  exact ⟨K, hK, hBK, hKeq, hPθK, hPQ, hUQ, hAU⟩

private theorem ResCtx.le_n155_and_mem_pCoreOf
    (h : ResCtx A c L M X B b d Lb p P e)
    (hne : CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({e} : Set G)) ≠ ⊥)
    {Y : Subgroup G} (hY : ConfY A b Lb Y) {U : Subgroup G} {z : G}
    (hU : U = CFSG.Open.pCoreOf 2 (lB A B)) (hU1 : U ≠ ⊥)
    (hUQ : U ∈ scriptQ A (lB A)) (hAU : A ≤ Subgroup.normalizer (U : Set G))
    (hzθ : z ∈ inSubgroup (aschbacherSolvableCore 3) Lb)
    (hθeq : inSubgroup (aschbacherSolvableCore 3) Lb = CFSG.Open.pCoreOf 2 Lb)
    (hPQ : P ∈ scriptQ A (lB A)) (h155 : Item155wJ2R)
    (hRb : Sec15R G A b Lb) (hdA : d ∈ A) (hd1 : d ≠ 1) (hdZ : IsZCentral Lb d) :
    P ≤ n155 A Y ∧
      z ∈ CFSG.Open.pCoreOf 2
        (oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G)))) := by
  have hUle : U ≤ lB A B := by
    rw [hU]
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 (lB A B)
  have hUN : lB A B ≤ Subgroup.normalizer (U : Set G) := by
    rw [hU]
    exact Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (lB A B))
  have hU2 : IsPGroup 2 U := by
    rw [hU]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (lB A B)
  set C : Subgroup G := Subgroup.centralizer ({e} : Set G) with hC
  have hloc : IsPLocal 2 (Subgroup.normalizer (CFSG.Open.pCoreOf 2 C : Set G)) :=
    CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 C) hne
  obtain ⟨M', hMle, hMmax⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge hloc
  have hCM' : C ≤ M' :=
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 C).trans hMle
  have hAM' : A ≤ M' := h.le_centralizer_A.trans hCM'
  have hRes_le : inSubgroup perfectResidual ((Lb ⊓ Y) ⊓ Subgroup.centralizer ({d} : Set G)) ≤
      Lb ⊓ Subgroup.centralizer ({d} : Set G) := by
    intro x hx
    have hx' : x ∈ (Lb ⊓ Y) ⊓ Subgroup.centralizer ({d} : Set G) :=
      Subgroup.map_subtype_le (perfectResidual ↥((Lb ⊓ Y) ⊓
        Subgroup.centralizer ({d} : Set G))) hx
    exact ⟨hx'.1.1, hx'.2⟩
  have hzHJLB : zHJ Lb Y d ≤ lB A B :=
    (Proof15Res7.zHJ_le_residual Lb Y d).trans
      (h.le_lB hRes_le (Proof15Res7.residual_inf_isPerfect Lb Y d))
  have hUY : U ≤ Y := (hUle.trans (h.lB_le.trans inf_le_left)).trans hY.le
  have hUC : U ≤ C := hUle.trans h.lB_le_centralizer
  have hZHC : zHJ Lb Y d ≤ C := hzHJLB.trans h.lB_le_centralizer
  have hsupM : (A ⊔ (zHJ Lb Y d ⊔ U) : Subgroup G) ≤ M' :=
    sup_le hAM' (sup_le (hZHC.trans hCM') (hUC.trans hCM'))
  have hMmem : M' ∈ CFSG.maximalTwoLocalsContaining
      ((A ⊔ (zHJ Lb Y d ⊔ U) : Subgroup G) : Set G) :=
    ⟨hMmax, fun x hx => hsupM hx⟩
  have hdelta : delta A (lB A) M' ≤ n155 A Y :=
    hY.delta_le_n155 (h155 G A b Lb hRb) hdA hd1 hdZ hU2 hU1 hUQ hAU
      (hzHJLB.trans hUN) (hUY.trans Subgroup.le_normalizer)
      (hUle.trans (h.lB_le.trans inf_le_right)) hMmem
  have hPdelta : P ≤ delta A (lB A) M' := le_delta hPQ (h.le_centralizer_e.trans hCM')
  have hPn155 : P ≤ n155 A Y := hPdelta.trans hdelta
  have hY0 : CFSG.Open.pCoreOf 2 Y ≤ CFSG.Open.pCoreOf 2
      (oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G)))) :=
    pCoreOf_le_pCoreOf_n155 hY.mem_scriptY0Star
  have hYle : Y ≤ Lb ⊔ CFSG.Open.pCoreOf 2 Y := by
    calc Y = (Y ⊓ Lb) ⊔ CFSG.Open.pCoreOf 2 Y := hY.eq_Y
      _ ≤ Lb ⊔ CFSG.Open.pCoreOf 2 Y := sup_le_sup inf_le_right le_rfl
  have hO2LY : CFSG.Open.pCoreOf 2 Lb ≤ CFSG.Open.pCoreOf 2 Y :=
    pCoreOf_le_of_le_sup hY.le hYle
  exact ⟨hPn155, hY0 (hO2LY (hθeq ▸ hzθ))⟩

theorem ResCtx.false_of_ne_bot
    (h142 : Item142AllS14) (h134 : Item134) (h48 : Sec4.Item4_8) (hcomp : Step143HJCompOne)
    (hlist : Step1515HJListLe) (h155 : Item155wJ2R) (h : ResCtx A c L M X B b d Lb p P e)
    (hne : CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({e} : Set G)) ≠ ⊥) : False := by
  obtain ⟨U, z, hU, -, hzθ, hzO2Odd, hzX, hU1, hO2, hθeq⟩ := h.exists_pCoreOf_data h142
  obtain ⟨-, -, -, -, -, hPQ, hUQ, hAU⟩ := h.exists_K_pCoreOf_data h142 h48 h134 hcomp
  obtain ⟨hbΩ, hLb, hJ, -, -, -, hdA, hd1, -, -⟩ :=
    Ronan152SL25.lbConfig_facts h.sec15R.isE27 h.hyp h.config
  have hRb : Sec15R G A b Lb := Sec16.sec15R_of_point h.sec15R hbΩ hLb
  have hdZ : IsZCentral Lb d := h.isZCentral_of_config
  obtain ⟨Y, hY⟩ := exists_confY hlist hRb hJ hO2
  obtain ⟨hPn155, hzK0⟩ :=
    h.le_n155_and_mem_pCoreOf hne hY hU hU1 (hU.symm ▸ hUQ) (hU.symm ▸ hAU)
      hzθ hθeq hPQ h155 hRb hdA hd1 hdZ
  haveI : Fact p.Prime := ⟨h.pdata.prime⟩
  have hPp : IsPGroup p P := by
    obtain ⟨R, hR, hPR, -⟩ := h.pdata.char_p
    exact IsPGroup.to_le hR.isPGroup hPR
  have hPnK0 : P ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2
      (oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G)))) : Set G) :=
    hPn155.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  exact hzO2Odd (mem_oTwoOddIn_of_mem_pCore (p := p) h.pdata.odd h.pdata.le_px hPp
    h.pdata.cent_p (Proof152FX.le_normalizer_sup_pCoreOf h.pdata.char_p)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hPnK0 hzX hzK0)

end Gagen152SL25Res

theorem step152SL25OneOmegaR_of_res
    (h142 : Item142AllS14) (h134 : Item134) (h48 : Sec4.Item4_8) (hcomp : Step143HJCompOne)
    (hlist : Step1515HJListLe) (h155 : Item155wJ2R) (hres : Step152SL25OneOmegaResR) :
    Step152SL25OneOmegaR := by
  intro G _ _ A c L hR hHJ M X hctx B b d Lb hB hc hcent hΩ
  obtain ⟨p, P, e, h⟩ := Gagen152SL25Res.exists_resCtx h142 hR hHJ hctx hB hc hcent hΩ
  by_cases hne : CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({e} : Set G)) = ⊥
  · exact hres G A c L h.sec15R h.allHJ M X h.ctx B b d Lb h.hyp h.config h.cent h.omega
      p P h.pdata h.three_lt h.fr e h.mem_e h.not_mem_e h.le_centralizer_e hne
  · exact h.false_of_ne_bot h142 h134 h48 hcomp hlist h155 hne

end CFSG.RankThree.PartTwo.Sec15
