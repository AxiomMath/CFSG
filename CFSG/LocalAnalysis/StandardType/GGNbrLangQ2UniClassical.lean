module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2UniSpBlock
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2UniOmegaBlock
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2UniDispatch
import CFSG.RankThree.GF2n.Stroth80.Sec1110CMLmConsumer
import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenIso
import CFSG.LocalAnalysis.StandardType.GGLayerCycModelOmegaSec
import CFSG.Timmesfeld.Orders.Classical
import CFSG.GroupTheory.ConjKerCenter
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1CentUniLift
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TorUniLift
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TorUniDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsUniBlock
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatTypeDet
import CFSG.Timmesfeld.Orders.Distinct
import CFSG.LieType.SemisimpleCentralizers.OrderThree.CenterQuot
import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.SemisimpleCentralizers
open CFSG.LieType.SemisimpleCentralizers.OrderThree

theorem GGInnerDiagOnLab.relabel {G : Type} [Group G] {S T : ℕ → LargeEvenLabel → Prop} {p : ℕ}
    {Bs L : Subgroup G}
    (hST : ∀ lab, LargeEvenInLambda2 lab → LargeEvenSplit p lab → S p lab →
      ∃ lab', GGLabelIso lab lab' ∧ LargeEvenInLambda2 lab' ∧ LargeEvenSplit p lab' ∧ T p lab')
    (h : GGInnerDiagOnLab S p Bs L) : GGInnerDiagOnLab T p Bs L := by
  obtain ⟨hperf, lab, hΛ, hraw⟩ := h
  obtain ⟨R, _, I, F, -, -, θ, hS, hSp, -⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨lab', hiso, hΛ', hSp', hT'⟩ := hST lab hΛ hSp hS
  refine ⟨hperf, lab', hΛ', largeEvenRawDatum_of_ggLabelIso hiso ?_⟩
  exact largeEvenRawDatum_mono
    (fun _ _ _ _ ⟨hs, hna, θ', _, _, hN, hI⟩ => ⟨hs, hna, θ', hT', hSp', hN, hI⟩) hraw

theorem GGBstarAbelianPreimageJUniS1On.relabel {S T : ℕ → LargeEvenLabel → Prop}
    (hST : ∀ p lab, LargeEvenInLambda2 lab → LargeEvenSplit p lab → S p lab →
      ∃ lab', GGLabelIso lab lab' ∧ LargeEvenInLambda2 lab' ∧ LargeEvenSplit p lab' ∧ T p lab')
    (h : GGBstarAbelianPreimageJUniS1On T) : GGBstarAbelianPreimageJUniS1On S := by
  intro G _ _ p B Bs x L D J hcfg hID hN d m hshape hpm hdm E _ hE θ hlab
  exact h G p B Bs x L D J hcfg hID hN d m hshape hpm hdm E hE θ
    (GGInnerDiagOnLab.relabel (hST p) hlab)

private theorem inLambda2_D3_iff_A3' (n : ℕ) :
    LargeEvenInLambda2 (⟨.D, 3, n⟩ : LargeEvenLabel) ↔
      LargeEvenInLambda2 (⟨.A, 3, n⟩ : LargeEvenLabel) := by
  simp [LargeEvenInLambda2]

private theorem inLambda2_twD3_iff_twA3' (n : ℕ) :
    LargeEvenInLambda2 (⟨.twD, 3, n⟩ : LargeEvenLabel) ↔
      LargeEvenInLambda2 (⟨.twA, 3, n⟩ : LargeEvenLabel) := by
  simp [LargeEvenInLambda2]

private theorem inLambda2_twD2_iff_A1' (n : ℕ) :
    LargeEvenInLambda2 (⟨.twD, 2, n⟩ : LargeEvenLabel) ↔
      LargeEvenInLambda2 (⟨.A, 1, 2 * n⟩ : LargeEvenLabel) := by
  simp only [LargeEvenInLambda2]
  omega

private theorem split_D3_A3 {p n : ℕ} (h : LargeEvenSplit p (⟨.D, 3, n⟩ : LargeEvenLabel)) :
    LargeEvenSplit p (⟨.A, 3, n⟩ : LargeEvenLabel) := by
  simpa [LargeEvenSplit, LargeEvenUntwisted] using h

private theorem two_pow_two_mul_sub_one (n : ℕ) :
    2 ^ (2 * n) - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ n = k + 1 := ⟨2 ^ n - 1, by omega⟩
  rw [pow_mul', hk]
  have h2 : k + 1 - 1 = k := by omega
  have h3 : (k + 1) ^ 2 = k * (k + 1 + 1) + 1 := by ring
  rw [h2, h3]
  omega

private theorem split_twD2_A1 {p n : ℕ} (h : LargeEvenSplit p (⟨.twD, 2, n⟩ : LargeEvenLabel)) :
    LargeEvenSplit p (⟨.A, 1, 2 * n⟩ : LargeEvenLabel) := by
  simp [LargeEvenSplit, LargeEvenUntwisted] at h ⊢
  rw [two_pow_two_mul_sub_one]
  rcases h with h | h | ⟨rfl, rfl⟩
  · exact Dvd.dvd.mul_left h _
  · exact Dvd.dvd.mul_right h _
  · decide

private theorem twD3_minus_of_not_split_twA {p n : ℕ}
    (h : LargeEvenSplit p (⟨.twD, 3, n⟩ : LargeEvenLabel))
    (hn : ¬ LargeEvenSplit p (⟨.twA, 3, n⟩ : LargeEvenLabel)) : p ∣ 2 ^ n - 1 := by
  simp [LargeEvenSplit, LargeEvenUntwisted] at h hn
  tauto

theorem q2URLevel_bc : Q2URLevel (fun _ lab => lab.tag = .B ∨ lab.tag = .C) := by
  intro p d m lab hlab hS _ hshape _ hdm Q hQ
  obtain ⟨t, l, n⟩ := lab
  have hodd : Odd p := by
    rcases hshape with ⟨h, _⟩ | ⟨h, _⟩ <;> subst h <;> decide
  have hd3 : 3 ≤ d := by omega
  rcases hS with h | h <;> dsimp only at h <;> subst h
  all_goals
    dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeSymplectic] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hq⟩ := hQ
    have hchar : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
    have hl2 : 2 ≤ l := hlab.2.1
    have hne : NeZero l := ⟨by omega⟩
    refine ⟨K, i1, i2, hK, hq, ?_⟩
    intro A hA hAI _ u hu huord J hJ hAJ E _ hE hJE M hM
    exact q2UniSpProj_lift (K := K) (l := l) hA.1
      (fun a ha => TableBSymp.sp_I_subset_inn (K := K) (m := l) (hAI a ha)) hu
      (by rw [huord]; exact hodd) (CFSG.Assembly.isComponentOf_iff_open.mpr hJ) hAJ hE hd3 hdm hJE M hM

theorem q2URLevel_D_high : Q2URLevel (fun _ lab => lab.tag = .D ∧ 4 ≤ lab.rank) := by
  intro p d m lab hlab hS _ hshape _ hdm Q hQ
  obtain ⟨htag, hrank⟩ := hS
  obtain ⟨tag, rank, n⟩ := lab
  dsimp only at htag hrank
  subst htag
  have hodd : Odd p := by
    rcases hshape with ⟨h, _⟩ | ⟨h, _⟩ <;> subst h <;> decide
  have hd3 : 3 ≤ d := by omega
  have hd4 : d ≠ 4 := by omega
  dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
  rw [if_neg (by omega : rank ≠ 3)] at hQ ⊢
  obtain ⟨K, fieldK, finiteK, hK, hQK⟩ := hQ
  let : Field K := fieldK
  let : Finite K := finiteK
  have hK2 : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  let : CharP K 2 := hK2
  let Φ : QuadraticForm K (Fin rank ⊕ Fin rank → K) := TableBOrth.qPlusForm K rank
  have hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate := TableBOrth.nondegenerate_qPlusForm rank
  have h8 : 8 ≤ Fintype.card (Fin rank ⊕ Fin rank) := by
    simp
    omega
  have hscal : (LargeEvenScalars (Fin rank ⊕ Fin rank) K).subgroupOf
      (LargeEvenOmega (LargeEvenQPlus K rank)) = ⊥ :=
    TableBOrth.scalars_subgroupOf_omegaPlus_eq_bot (K := K) (m := rank) (by omega)
  have hZraw : Subgroup.center ↥(LargeEvenOmega (LargeEvenQPlus K rank)) = ⊥ :=
    CFSG.RankThree.GF2n.Stroth80.center_statedOmega_quadPlus_eq_bot (m := rank) (by omega)
  have hconj : Function.Injective
      (MulAut.conj : ↥(LargeEvenOmega (LargeEvenQPlus K rank)) →*
        MulAut ↥(LargeEvenOmega (LargeEvenQPlus K rank))) :=
    (MonoidHom.ker_eq_bot_iff _).mp (CFSG.GroupTheory.ker_conj_eq_center.trans hZraw)
  refine ⟨K, fieldK, finiteK, hK, ?_⟩
  refine ⟨hQK, ?_⟩
  intro A hA hAI _ u hu huord J hJ hAJ E _ hE hJE M hM
  exact q2UniOmegaQuotient_lift (LargeEvenQPlus K rank) Φ (TableBOrth.coe_qPlusForm rank) hΦ h8
    hscal hconj hA.1 hAI hu (by rw [huord]; exact hodd) (CFSG.Assembly.isComponentOf_iff_open.mpr hJ)
    hAJ hE hd3 hd4 hdm hJE M hM

theorem q2URLevel_twD_high : Q2URLevel (fun _ lab => lab.tag = .twD ∧ 4 ≤ lab.rank) := by
  intro p d m lab hlab hS _ hshape _ hdm Q hQ
  obtain ⟨htag, hrank⟩ := hS
  obtain ⟨tag, rank, n⟩ := lab
  dsimp only at htag hrank
  subst htag
  have hodd : Odd p := by
    rcases hshape with ⟨h, _⟩ | ⟨h, _⟩ <;> subst h <;> decide
  have hd3 : 3 ≤ d := by omega
  have hd4 : d ≠ 4 := by omega
  dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
  rw [if_neg (by omega : rank ≠ 2), if_neg (by omega : rank ≠ 3)] at hQ ⊢
  obtain ⟨K, fieldK, finiteK, hK, b, c, hbc, hQK⟩ := hQ
  let : Field K := fieldK
  let : Finite K := finiteK
  have hK2 : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  let : CharP K 2 := hK2
  let Φ : QuadraticForm K (LargeEvenMinusIdx (rank - 1) → K) :=
    TableBOrth.qMinusForm K (rank - 1) b c
  have hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate :=
    TableBOrth.nondegenerate_qMinusForm (rank - 1) hbc
  have h8 : 8 ≤ Fintype.card (LargeEvenMinusIdx (rank - 1)) := by
    simp [LargeEvenMinusIdx]
    omega
  have hscal : (LargeEvenScalars (LargeEvenMinusIdx (rank - 1)) K).subgroupOf
      (LargeEvenOmega (LargeEvenQMinus (rank - 1) b c)) = ⊥ :=
    TableBOrth.scalars_subgroupOf_omegaMinus_eq_bot (K := K) (m := rank - 1) b c
  have hZstd : Subgroup.center (StatedOmega (StatedQuadMinus rank K b c)) = ⊥ :=
    CFSG.StandardType.center_statedOmega_quadMinus_eq_bot (n := rank) (by omega) hbc
  have hZraw : Subgroup.center (LargeEvenOmega (LargeEvenQMinus (rank - 1) b c)) = ⊥ := by
    have hsub : rank - 1 + 1 = rank := Nat.sub_add_cancel (by omega)
    have eM : LargeEvenOmega (LargeEvenQMinus (rank - 1) b c) ≃*
        StatedOmega (StatedQuadMinus rank K b c) :=
      hsub ▸ CFSG.StandardType.LayerCyc.largeEvenOmegaMinusEquiv (rank - 1) K b c
    rw [← Subgroup.map_center_eq eM.symm, hZstd, Subgroup.map_bot]
  have hconj : Function.Injective
      (MulAut.conj : ↥(LargeEvenOmega (LargeEvenQMinus (rank - 1) b c)) →*
        MulAut ↥(LargeEvenOmega (LargeEvenQMinus (rank - 1) b c))) :=
    (MonoidHom.ker_eq_bot_iff _).mp (CFSG.GroupTheory.ker_conj_eq_center.trans hZraw)
  refine ⟨K, fieldK, finiteK, hK, b, c, hbc, hQK, ?_⟩
  intro A hA hAI _ u hu huord J hJ hAJ E _ hE hJE M hM
  exact q2UniOmegaQuotient_lift (LargeEvenQMinus (rank - 1) b c) Φ
    (TableBOrth.coe_qMinusForm (rank - 1) b c) hΦ h8 hscal hconj hA.1 hAI hu
    (by rw [huord]; exact hodd) (CFSG.Assembly.isComponentOf_iff_open.mpr hJ) hAJ hE hd3 hd4 hdm
    hJE M hM

private theorem cuq2d3b_centerQuot_equiv {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] (SU : Subgroup (GL ι K)) {C : Subgroup (GL ι K)}
    (hperf : commutator ↥C = ⊤) (hCSU : C ≤ SU)
    {J : Subgroup (LargeEvenProj SU)}
    (hJeq : J = (C.subgroupOf SU).map (LargeEvenProjMk SU)) :
    Nonempty (↥C ⧸ Subgroup.center ↥C ≃* ↥J ⧸ Subgroup.center ↥J) := by
  have hmem : ∀ c : ↥C,
      LargeEvenProjMk SU ⟨(c : GL ι K), hCSU c.2⟩ ∈ J := by
    intro c
    rw [hJeq]
    exact Subgroup.mem_map.mpr ⟨⟨(c : GL ι K), hCSU c.2⟩, c.2, rfl⟩
  let f : ↥C →* ↥J :=
    { toFun := fun c => ⟨LargeEvenProjMk SU ⟨(c : GL ι K), hCSU c.2⟩, hmem c⟩
      map_one' := by
        apply Subtype.ext
        change LargeEvenProjMk SU (1 : ↥SU) = (1 : LargeEvenProj SU)
        rw [map_one]
      map_mul' := by
        intro x y
        apply Subtype.ext
        change LargeEvenProjMk SU
            (⟨(x : GL ι K), hCSU x.2⟩ * ⟨(y : GL ι K), hCSU y.2⟩ : ↥SU) =
          LargeEvenProjMk SU ⟨(x : GL ι K), hCSU x.2⟩ *
            LargeEvenProjMk SU ⟨(y : GL ι K), hCSU y.2⟩
        rw [map_mul] }
  have hf : Function.Surjective f := by
    intro j
    have hj : (j : LargeEvenProj SU) ∈ (C.subgroupOf SU).map (LargeEvenProjMk SU) := by
      rw [← hJeq]
      exact j.2
    obtain ⟨x, hx, hxj⟩ := Subgroup.mem_map.mp hj
    refine ⟨⟨(x : GL ι K), hx⟩, ?_⟩
    apply Subtype.ext
    show LargeEvenProjMk SU ⟨(x : GL ι K), hCSU hx⟩ = (j : LargeEvenProj SU)
    rw [show (⟨(x : GL ι K), hCSU hx⟩ : ↥SU) = x from Subtype.ext rfl]
    exact hxj
  have hker : f.ker ≤ Subgroup.center ↥C := by
    intro c hc
    have hc1 : LargeEvenProjMk SU ⟨(c : GL ι K), hCSU c.2⟩ = 1 := by
      have h := congrArg (fun z : ↥J => (z : LargeEvenProj SU)) hc
      simpa [f] using h
    have hmemker : (⟨(c : GL ι K), hCSU c.2⟩ : ↥SU) ∈ (LargeEvenProjMk SU).ker :=
      MonoidHom.mem_ker.mpr hc1
    rw [QuotientGroup.ker_mk', Subgroup.mem_subgroupOf] at hmemker
    have hcZ : (c : GL ι K) ∈ Subgroup.center (GL ι K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      rwa [largeEvenScalars_def] at hmemker
    rw [Subgroup.mem_center_iff]
    intro d
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hcZ (d : GL ι K)
  exact
    nonempty_quotientCenter_mulEquiv_of_surjective
      ⟨hperf⟩ f hf hker

private theorem cuq2d3b_ordA_one_two_pow (k : ℕ) (hk : 1 ≤ k) :
    CFSG.Open.ordA 1 (2 ^ k) = 2 ^ k * ((2 ^ k) ^ 2 - 1) := by
  rw [CFSG.Open.ordA]
  have hg : Nat.gcd 2 ((2 ^ k) - 1) = 1 :=
    Nat.coprime_two_left.mpr (CFSG.Timmesfeld.Orders.odd_two_pow_sub_one hk)
  rw [hg, Nat.div_one]
  norm_num

private theorem cuq2d3b_two_pow_dvd_of_dvd {p n m dd : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : p ∣ 2 ^ n - 1) (hpm : p ∣ 2 ^ m + 1) (hkm : m = n * dd) : False := by
  have hbase : (2 : ℕ) ^ n ≡ 1 [MOD p] :=
    ((Nat.modEq_iff_dvd' Nat.one_le_two_pow).mpr hpn).symm
  have hpow' : (2 : ℕ) ^ (n * dd) ≡ 1 [MOD p] := by
    have h := hbase.pow dd
    simpa [pow_mul] using h
  have hpow : (2 : ℕ) ^ m ≡ 1 [MOD p] := by
    rw [hkm]
    exact hpow'
  have hdvd1 : p ∣ 2 ^ m - 1 :=
    (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp hpow.symm
  have h2 : p ∣ 2 := by
    have h : 2 ^ m + 1 - (2 ^ m - 1) = 2 := by
      have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      omega
    rw [← h]
    exact Nat.dvd_sub hpm hdvd1
  exact hp2 (le_antisymm (Nat.le_of_dvd (by norm_num) h2) hp.two_le)


theorem q2UniTwD3_minus_false {n : ℕ} (hn : 1 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : p ∣ 2 ^ n - 1) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    {u : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n)))}
    (hu : u ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) K (2 ^ n)))
      (LargeEvenGUSet (Fin 4) K (2 ^ n)))
    (huord : orderOf u = p) {J : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n)))}
    (hJ : CFSG.Open.IsComponentOf J (ggAutFixedSubgroup u)) {d m : ℕ} {E : Type} [Field E]
    (hE : UnitaryFieldData 2 m E) (hd : 3 ≤ d) (hdm : ¬ (d = 3 ∧ m = 1)) (hpm : p ∣ 2 ^ m + 1)
    (θ : ↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) E (2 ^ m))) :
    False := by
  classical
  have hF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K :=
    unitaryFieldData_of_card hn hK
  haveI : CharP K 2 := hF.charP
  obtain ⟨τ, hτ, hτQ⟩ := exists_unitaryInvolution hn hK
  let H : Subgroup (GL (Fin 4) K) := LargeEvenSUGroup (Fin 4) K (2 ^ n)
  obtain ⟨s, hsN, hs_held, hs_proj⟩ :=
    q1CentUni_exists_lift (d := 4) (m := n) hK hn τ hτ hτQ hu
  have hsp : TableB.projConj H ⟨s, hsN⟩ ^ p = 1 := by
    rw [← hs_proj, ← huord, pow_orderOf_eq_one]
  have hdq : (4, 2 ^ n) ≠ (3, 2) := by
    intro h
    exact absurd (congrArg Prod.fst h) (by norm_num)
  have hsp_scal : s ^ p ∈ LargeEvenScalars (Fin 4) K :=
    q1CentUni_pow_mem_scalars (d := 4) (m := n) hK hn (by norm_num) hdq hsN hsp
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hso : Odd (orderOf s) :=
    q1CentUni_odd_orderOf (d := 4) (m := n) hK hn hpodd hsp_scal
  have hJc : CFSG.Open.IsComponentOf J (ggAutFixedSubgroup (TableB.projConj H ⟨s, hsN⟩)) := by
    rw [← hs_proj]
    exact hJ
  obtain ⟨C, hC, hCSU, hJeq⟩ :=
    q1TorUni_component_lift (d := 4) (m := n) (K := K) τ hτ hτQ s hs_held hsN J hJc
  have hCopen : CFSG.Open.IsComponentOf C
      (Subgroup.centralizer ({s} : Set (GL (Fin 4) K)) ⊓
        CFSG.LieType.SemisimpleCentralizers.Held.heldGU 4 K τ hτ) :=
    (CFSG.Assembly.isComponentOf_iff_open).1 hC
  have hord : ((orderOf s : ℕ) : K) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff K 2] at h0
    exact (Nat.not_even_iff_odd.mpr hso) (even_iff_two_dvd.mpr h0)
  obtain ⟨eCJ⟩ := cuq2d3b_centerQuot_equiv H hC.2.2.1 hCSU hJeq
  have hcardCZ : Nat.card (↥C ⧸ Subgroup.center ↥C) = Open.ordTwistedA (d - 1) (2 ^ m) := by
    rw [Nat.card_congr (eCJ.trans θ).toEquiv]
    change Nat.card (StatedProj (StatedSU d (2 ^ m) E)) = _
    rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two hE.one_le
      (unitaryFieldData_card_sq hE) (by omega : 2 ≤ d), CFSG.Open.ordTwistedA,
      Nat.sub_add_cancel (by omega : 1 ≤ d), Nat.mul_comm d (d - 1)]
  obtain ⟨_, _, _, _, _, hbr⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.K1419.k1419ClsUniBlockPair (n := 4) (Q := 2 ^ n)
      hτ hτQ hK s hs_held hord C hCopen
  rcases hbr with
    ⟨a, dd, E', hEfld, hEfin, τ', hτ', _, ha2, hτ'Q, hEcard, ⟨eM⟩, hirrP, hPdeg, _⟩ |
    ⟨b, e, E', hEfld, hEfin, _, _, _, _, hb2, hEcard, ⟨eM⟩, _, _, _, _, _,
      hirrP, hPdeg, _, _, _, _, _, _, _, _⟩
  ·
    letI : Field E' := hEfld
    letI : Finite E' := hEfin
    have hdd1 : 1 ≤ dd := by
      have h := hirrP.natDegree_pos
      omega
    have hn2 : 2 ≤ n := by
      by_contra h
      have hn1 : n = 1 := by omega
      subst hn1
      exact hp.ne_one (Nat.dvd_one.mp (by simpa using hpn))
    set kk : ℕ := n * dd with hkk
    have hQdd : (2 ^ n) ^ dd = 2 ^ kk := by rw [hkk, pow_mul]
    have hK2 : Nat.card E' = (2 ^ kk) ^ 2 := by rw [hEcard, hQdd]
    have hk2 : 2 ≤ kk := by
      rw [hkk]
      calc 2 = 2 * 1 := by norm_num
        _ ≤ n * dd := Nat.mul_le_mul hn2 hdd1
    have hτ'Q' : ∀ x : E', τ' x = x ^ (2 ^ kk) := by
      intro x
      rw [← hQdd]
      exact hτ'Q x
    have hHeldSU : Held.heldSU a E' τ' hτ' = StatedSU a (2 ^ kk) E' :=
      Held.hct_heldSU_eq_statedSU (a := a) (Q := 2 ^ kk) hτ'Q'
    let eM' : ↥C ≃* StatedSU a (2 ^ kk) E' :=
      eM.trans (MulEquiv.subgroupCongr hHeldSU)
    by_cases ha : a = 2
    ·
      subst ha
      have hcard2 : Nat.card (↥C ⧸ Subgroup.center ↥C) = Open.ordA 1 (2 ^ kk) := by
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        haveI : CharP E' 2 :=
          (unitaryFieldData_of_card (n := kk) (by omega : 1 ≤ kk) hK2).charP
        have hcenter : Subgroup.center (StatedSU 2 (2 ^ kk) E') = ⊥ :=
          CFSG.ComponentClassification.RankTwoClassical.center_statedSU_two_eq_bot
            (K := E') (f := kk) hK2
        have h1 : Nat.card (↥C ⧸ Subgroup.center ↥C) =
            Nat.card (↥(StatedSU 2 (2 ^ kk) E') ⧸
              Subgroup.center ↥(StatedSU 2 (2 ^ kk) E')) :=
          Nat.card_congr (QuotientGroup.congr _ _ eM' (Subgroup.map_center_eq eM')).toEquiv
        rw [h1]
        have e2 : ↥(StatedSU 2 (2 ^ kk) E') ⧸
              Subgroup.center ↥(StatedSU 2 (2 ^ kk) E') ≃* ↥(StatedSU 2 (2 ^ kk) E') :=
          (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
        rw [Nat.card_congr e2.toEquiv,
          CFSG.RankThree.SubgroupLists.card_statedSU_two (K := E') (r := 2) (f := kk) hK2]
        exact (cuq2d3b_ordA_one_two_pow kk (by omega)).symm
      have heq : Open.ordA 1 (2 ^ kk) = Open.ordTwistedA (d - 1) (2 ^ m) :=
        hcard2.symm.trans hcardCZ
      exact (CFSG.Timmesfeld.Orders.ordA_ne_ordTwistedA (n := 1) (f := kk) (u := d - 1) (g := m)
        le_rfl (by omega) (by omega) hE.one_le) heq
    ·
      have ha3 : 3 ≤ a := by omega
      have hcardU : Nat.card (↥C ⧸ Subgroup.center ↥C) =
          Open.ordTwistedA (a - 1) (2 ^ kk) := by
        obtain ⟨eCZ⟩ :=
          nonempty_quotientCenter_equiv_statedProj_statedSU
            (K := E') (f := kk) hK2 hk2 (by omega : 2 ≤ a) eM'
        rw [Nat.card_congr eCZ.toEquiv]
        change Nat.card (StatedProj (StatedSU a (2 ^ kk) E')) = _
        rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two
          (by omega : 1 ≤ kk) hK2 (by omega : 2 ≤ a), CFSG.Open.ordTwistedA,
          Nat.sub_add_cancel (by omega : 1 ≤ a), Nat.mul_comm a (a - 1)]
      have heq : Open.ordTwistedA (a - 1) (2 ^ kk) = Open.ordTwistedA (d - 1) (2 ^ m) :=
        hcardU.symm.trans hcardCZ
      have hnf : ((a - 1, kk) : ℕ × ℕ) ≠ (2, 1) := by
        rintro h
        have hkk1 : kk = 1 := (Prod.mk.inj h).2
        omega
      have hug : ((d - 1, m) : ℕ × ℕ) ≠ (2, 1) := by
        rintro h
        have hd1 : d - 1 = 2 := (Prod.mk.inj h).1
        exact hdm ⟨by omega, (Prod.mk.inj h).2⟩
      have hna : 2 ≤ a - 1 := by omega
      have hnd : 2 ≤ d - 1 := by omega
      have hnk : 1 ≤ kk := by omega
      obtain ⟨-, hkm⟩ :=
        CFSG.SeitzReduction.UnitaryPilot.ordTwistedA_inj_two_pow
          (n := a - 1) (u := d - 1) (f := kk) (g := m)
          hna hnd hnk hE.one_le hnf hug heq
      exact cuq2d3b_two_pow_dvd_of_dvd hp hp2 hpn hpm (hkm.symm.trans hkk)
  ·
    letI : Field E' := hEfld
    letI : Finite E' := hEfin
    have he1 : 1 ≤ e := by
      have h := hirrP.natDegree_pos
      omega
    have hexp : n * (2 * e) = 2 * n * e := by ring
    have hEcard' : Nat.card E' = 2 ^ (2 * n * e) := by
      rw [hEcard, ← pow_mul 2 n (2 * e), hexp]
    have hcardL : Nat.card (↥C ⧸ Subgroup.center ↥C) = Open.ordA (b - 1) (2 ^ (2 * n * e)) := by
      obtain ⟨eCZ⟩ :=
        CFSG.LieType.SemisimpleCentralizers.Held.nonempty_quotientCenter_equiv_statedProj eM
      rw [Nat.card_congr eCZ.toEquiv]
      rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (n := b) (by omega : 1 ≤ b),
        hEcard', CFSG.Open.ordA, Nat.sub_add_cancel (by omega : 1 ≤ b), Nat.mul_comm (b - 1) b]
    have heq : Open.ordA (b - 1) (2 ^ (2 * n * e)) = Open.ordTwistedA (d - 1) (2 ^ m) :=
      hcardL.symm.trans hcardCZ
    have hf : 1 ≤ 2 * n * e := by
      have hne : 1 ≤ n * e := by
        have h := Nat.mul_le_mul hn he1
        simpa using h
      calc 1 ≤ 2 * (n * e) := by omega
        _ = 2 * n * e := by ring
    exact (CFSG.Timmesfeld.Orders.ordA_ne_ordTwistedA (n := b - 1) (f := 2 * n * e)
      (u := d - 1) (g := m) (by omega) hf (by omega) hE.one_le) heq

theorem q2URLevel_twD_three_minus :
    Q2URLevel (fun p lab => lab.tag = .twD ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n - 1) := by
  intro p d m lab hlab hS _ hshape hpm hdm Q hQ
  obtain ⟨htag, hrank, hdvd⟩ := hS
  obtain ⟨tag, rank, n⟩ := lab
  dsimp only at htag hrank hdvd
  subst htag
  have hn : 1 ≤ n := hlab.1
  have hr2 : rank ≠ 2 := by omega
  dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
  rw [if_neg hr2, if_pos hrank] at hQ ⊢
  obtain ⟨K, fieldK, finiteK, hK, hQK⟩ := hQ
  let : Field K := fieldK
  let : Finite K := finiteK
  have hp : p.Prime := by
    rcases hshape with ⟨h, _⟩ | ⟨h, _⟩ <;> subst h <;> norm_num
  have hp2 : p ≠ 2 := by omega
  have hd3 : 3 ≤ d := by omega
  refine ⟨K, fieldK, finiteK, hK, hQK, ?_⟩
  intro A _ hAI _ u hu huord J hJ _ E _ hE hJE _ _
  obtain ⟨θ⟩ := hJE
  exact (q2UniTwD3_minus_false hn hp hp2 hdvd hK (hAI u hu) huord hJ hE hd3 hdm hpm θ).elim

theorem ggBstarAbelianPreimageJUniS1On_classical :
    GGBstarAbelianPreimageJUniS1On
      (fun _ lab => lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D ∨ lab.tag = .twD) := by
  refine GGBstarAbelianPreimageJUniS1On.relabel
    (T := fun p lab => (((lab.tag = .B ∨ lab.tag = .C) ∨ (lab.tag = .D ∧ 4 ≤ lab.rank)) ∨
        (lab.tag = .twD ∧ 4 ≤ lab.rank)) ∨
      (lab.tag = .A ∨ (lab.tag = .twA ∨
        (lab.tag = .twD ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n - 1)))) ?_
    ((((ggBstarAbelianPreimageJUniS1On_of_rLevel q2URLevel_bc).or
        (ggBstarAbelianPreimageJUniS1On_of_rLevel q2URLevel_D_high)).or
        (ggBstarAbelianPreimageJUniS1On_of_rLevel q2URLevel_twD_high)).or
      (ggBstarAbelianPreimageJUniS1On_tagA.or
        (ggBstarAbelianPreimageJUniS1On_twA.or
          (ggBstarAbelianPreimageJUniS1On_of_rLevel q2URLevel_twD_three_minus))))
  rintro p ⟨tag, rank, n⟩ hΛ hSp hS
  dsimp only at hS
  rcases hS with rfl | rfl | rfl | rfl
  · exact ⟨⟨.B, rank, n⟩, Or.inl rfl, hΛ, hSp, Or.inl (Or.inl (Or.inl (Or.inl rfl)))⟩
  · exact ⟨⟨.C, rank, n⟩, Or.inl rfl, hΛ, hSp, Or.inl (Or.inl (Or.inl (Or.inr rfl)))⟩
  · by_cases h4 : 4 ≤ rank
    · exact ⟨⟨.D, rank, n⟩, Or.inl rfl, hΛ, hSp, Or.inl (Or.inl (Or.inr ⟨rfl, h4⟩))⟩
    · have hr3 : rank = 3 := by
        dsimp only [LargeEvenInLambda2] at hΛ
        omega
      subst hr3
      exact ⟨⟨.A, 3, n⟩, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)), (inLambda2_D3_iff_A3' n).mp hΛ,
        split_D3_A3 hSp, Or.inr (Or.inl rfl)⟩
  · by_cases h4 : 4 ≤ rank
    · exact ⟨⟨.twD, rank, n⟩, Or.inl rfl, hΛ, hSp, Or.inl (Or.inr ⟨rfl, h4⟩)⟩
    · by_cases h3 : rank = 3
      · subst h3
        by_cases hsA : LargeEvenSplit p (⟨.twA, 3, n⟩ : LargeEvenLabel)
        · exact ⟨⟨.twA, 3, n⟩, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))),
            (inLambda2_twD3_iff_twA3' n).mp hΛ, hsA, Or.inr (Or.inr (Or.inl rfl))⟩
        · exact ⟨⟨.twD, 3, n⟩, Or.inl rfl, hΛ, hSp,
            Or.inr (Or.inr (Or.inr ⟨rfl, rfl, twD3_minus_of_not_split_twA hSp hsA⟩))⟩
      · have h2 : rank = 2 := by
          dsimp only [LargeEvenInLambda2] at hΛ
          omega
        subst h2
        exact ⟨⟨.A, 1, 2 * n⟩,
          Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))),
          (inLambda2_twD2_iff_A1' n).mp hΛ, split_twD2_A1 hSp, Or.inr (Or.inl rfl)⟩

end CFSG.StandardType
