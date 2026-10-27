module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec64Recog
public import CFSG.RankThree.GF2n.Stroth80.HeringSec64DirectMain
public import CFSG.RankThree.GF2n.Stroth80.CorBListNormal
public import CFSG.RankThree.GF2n.Stroth80.Sec64RecogCent
public import CFSG.RankThree.GF2n.Stroth80.Sec7OutSolvable
public import CFSG.RankThree.GF2n.Stroth80.Sec93CentAssembly
public import CFSG.RankThree.GF2n.Stroth80.Sec93FinalBoundPure
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailOddCoreBar
public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.O2Hbar

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem corB_centralizes_normalClosure {Y : Type} [Group Y] [Finite Y] {T H X : Subgroup Y}
    [H.Normal] [IsSimpleGroup ↥X] (hB : CorollaryBStmt) (hCorB : CorBHyp T) (hTH : T ≤ H)
    (h4 : 4 ≤ Nat.card T)
    (hO2 : ∀ P : Subgroup Y, P ≤ H → (∀ h ∈ H, h ∈ Subgroup.normalizer (P : Set Y)) →
      IsPGroup 2 P → P = ⊥)
    (hO : ∀ P : Subgroup Y, P ≤ H → (∀ h ∈ H, h ∈ Subgroup.normalizer (P : Set Y)) →
      Odd (Nat.card P) → P = ⊥)
    (hOut : OutSolvableListStatement) (hCent : ListCentralizerInvolutionsStatement)
    (hsimple : ∀ (D : Type) [Group D] [Finite D], ListGroup D → IsSimpleGroup D)
    (hnc : ∀ (D : Type) [Group D] [Finite D], ListGroup D → ∃ a b : D, a * b ≠ b * a)
    (hX4 : 4 ∣ Nat.card X) (hXT : ∀ x ∈ X, ∀ t ∈ T, x * t = t * x) :
    ∀ x ∈ X, ∀ s ∈ Subgroup.normalClosure (T : Set Y), x * s = s * x := by
  have hTne : T ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at h4
    omega
  have hTp : IsPGroup 2 T := corB_isPGroup_of_isElemAbelian T hCorB.1
  have hThm : ThmAConclusion T := hB Y T hCorB
  have hList : ListGroup ↥(Subgroup.normalClosure (T : Set Y)) :=
    corB_listGroup_of_normal_sub hTH hTne hTp hThm hO2 hO
  have hSn : (Subgroup.normalClosure (T : Set Y)).Normal := inferInstance
  have hTS : T ≤ Subgroup.normalClosure (T : Set Y) := Subgroup.le_normalClosure
  generalize Subgroup.normalClosure (T : Set Y) = S at hList hSn hTS ⊢
  haveI : IsSimpleGroup ↥S := hsimple _ hList
  have hZS : Subgroup.center ↥S = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center ↥S) with h0 | h0
    · exact h0
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc _ hList
      have ha : a ∈ Subgroup.center ↥S := by
        rw [h0]
        exact Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.mp ha b).symm
  have hTab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hCorB.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hCentS : ∀ s ∈ S, (∀ t ∈ T, s * t = t * s) → s * s = 1 → s ∈ T := by
    intro s hs hcomm hs2
    have hcorb : CorBHyp (T.subgroupOf S) := sec93f_corBHyp_subgroupOf hTS hCorB
    have h4' : 4 ≤ Nat.card (T.subgroupOf S) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTS).toEquiv]
      exact h4
    have hmem := hCent ↥S hList (T.subgroupOf S) h4' hcorb ⟨s, hs⟩ (by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subtype.ext (hcomm (y : Y) (Subgroup.mem_subgroupOf.mp hy)).symm)
      (Subtype.ext (by simpa using hs2))
    exact Subgroup.mem_subgroupOf.mp hmem
  exact centralizes_of_perfect_action hTS hTab hZS (hOut ↥S hList) hCentS hX4 hXT

namespace HS6

section Cent

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {hc : Ctx M Q Z B} {n : ℕ} {t : G} {m : ℕ} {X : Subgroup G}

theorem Env.bar_X_simple (e : Env hc n t m X)
    (hsat : (OmegaPlusNat hc t m ∧ QuotSat X Q (IsOmegaPlus m (Nat.card Z))) ∨
      (OmegaMinusNat hc t m ∧ QuotSat X Q (IsOmegaMinus m (Nat.card Z)))) :
    IsSimpleGroup ↥(bar M Q X) ∧ 16 ∣ Nat.card ↥(bar M Q X) := by
  obtain ⟨hnX, ⟨eXB⟩⟩ := quotMulEquivBar (M := M) (Q := Q) e.hQX e.X_le_M
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  obtain ⟨e', -, he, -⟩ := hc.hyp.cp
  rcases hsat with ⟨-, hnQ, K, fK, finK, hK, ⟨eΩ⟩⟩ | ⟨-, hnQ, K, fK, finK, hK, b, c, hirr, ⟨eΩ⟩⟩
  · haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hK.trans he)
    obtain ⟨hs, h16, -⟩ := endg_omegaPlus_facts (K := K) (by rw [hK]; exact hq4) e.hm
    let f : ↥(bar M Q X) ≃* ↥(StatedOmega (StatedQuadPlus m K)) := eXB.symm.trans eΩ
    exact ⟨f.isSimpleGroup, by rw [Nat.card_congr f.toEquiv]; exact h16⟩
  · haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hK.trans he)
    obtain ⟨hs, h16, -⟩ := endg_omegaMinus_facts (K := K) (m := m) (by rw [hK]; exact hq4)
      (by have := e.hm; omega) hirr
    let f : ↥(bar M Q X) ≃* ↥(StatedOmega (StatedQuadMinus m K b c)) := eXB.symm.trans eΩ
    exact ⟨f.isSimpleGroup, by rw [Nat.card_congr f.toEquiv]; exact h16⟩

theorem Env.cent_of_corB (I : Inputs) (e : Env hc n t m X) (h44 : Stroth44Statement)
    (hB : CorollaryBStmt) (hCorB : CorBHyp (bar M Q (hc.CN t)))
    (hsat : (OmegaPlusNat hc t m ∧ QuotSat X Q (IsOmegaPlus m (Nat.card Z))) ∨
      (OmegaMinusNat hc t m ∧ QuotSat X Q (IsOmegaMinus m (Nat.card Z))))
    (hOut : OutSolvableListStatement) (hCent : ListCentralizerInvolutionsStatement)
    (hsimple : ∀ (D : Type) [Group D] [Finite D], ListGroup D → IsSimpleGroup D)
    (hnc : ∀ (D : Type) [Group D] [Finite D], ListGroup D → ∃ a b : D, a * b ≠ b * a) :
    ∀ g ∈ M, ∀ a ∈ hc.CN t, ∀ x ∈ X, ⁅x, g * a * g⁻¹⁆ ∈ Q := by
  classical
  have hNM : hc.CN t ≤ M := e.CN_le_M
  have hQN : Q ≤ hc.CN t := hc.Q_le_CN e.hs.toSec5.mem
  have hXM : X ≤ M := e.X_le_M
  haveI hHn : (bar M Q (H0 M Z)).Normal := hc.normal_bar_H0
  haveI hZV : (Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer sec39_Z_le_Vt).mpr fun v hv =>
      hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hc.Vt_le_Q t hv))
  have hNbH : bar M Q (hc.CN t) ≤ bar M Q (H0 M Z) := bar_mono (e.CN_le_H0 I)
  have hcardNb : Nat.card (bar M Q (hc.CN t)) = Nat.card Z := by
    have h1 : Nat.card (bar M Q (hc.CN t)) * Nat.card Q = Nat.card (hc.CN t) :=
      card_bar_mul hQN hNM
    rw [e.hs.cardN] at h1
    have hQpos : 0 < Nat.card Q := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hQpos (by rw [h1, mul_comm])
  have hNb4 : 4 ≤ Nat.card (bar M Q (hc.CN t)) := by
    rw [hcardNb]
    exact hc.hyp.q4
  have hLB : bar M Q (LB M Q B) ≤ bar M Q (H0 M Z) :=
    hc.bar_LB_le_bar_Lgen.trans hc.bar_Lgen_le_bar_H0
  obtain ⟨hXs, h16⟩ := e.bar_X_simple hsat
  haveI := hXs
  have hXT : ∀ x ∈ bar M Q X, ∀ y ∈ bar M Q (hc.CN t), x * y = y * x := by
    intro x hx y hy
    obtain ⟨x', hx'X, hx'M, rfl⟩ := (mem_bar x).mp hx
    obtain ⟨a, ha, haM, rfl⟩ := (mem_bar y).mp hy
    refine piM_comm_of_comm_mem hx'M haM ?_
    have := Q.inv_mem (e.hcen a ha x' hx'X)
    rwa [commutatorElement_inv] at this
  have hcentral := corB_centralizes_normalClosure (T := bar M Q (hc.CN t))
    (H := bar M Q (H0 M Z)) (X := bar M Q X) hB hCorB hNbH hNb4
    (fun P hPH hPn hP2 =>
      eq_bot_of_normal_pgroup_of_pCore (pCore_two_bar_H0_eq_bot hc) hPH hPn hP2)
    (fun P hPH hPn hPodd =>
      h44 G M Q Z B hc n e.hs.toSec5.width e.hs.toSec5.n_gt e.hs.toSec5.noA2 e.hs.toSec5.gen P hPH
        (fun x hx => hPn x (hLB hx)) hPodd)
    hOut hCent hsimple hnc (dvd_trans (by norm_num : 4 ∣ 16) h16) hXT
  intro g hg a ha x hx
  have hgaM : g * a * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hg (hNM ha)) (M.inv_mem hg)
  have hxM : x ∈ M := hXM hx
  have hmemS : piM M Q (g * a * g⁻¹) ∈
      Subgroup.normalClosure ((bar M Q (hc.CN t) : Subgroup (Mbar M Q)) : Set (Mbar M Q)) := by
    rw [piM_conj hg (hNM ha)]
    exact (Subgroup.normalClosure_normal).conj_mem _
      (Subgroup.le_normalClosure (piM_mem_bar ha (hNM ha))) _
  exact comm_mem_Q_of_piM_comm hxM hgaM (hcentral _ (piM_mem_bar hx hxM) _ hmemS)

end Cent

end HS6

section Certs

theorem stroth64Recog_holds : HS6.Stroth64RecogStatement := by
  intro G _ _ M Q Z B hc n t hs m hm hΩ _ hCorB hB
  have I : HS6.Inputs := ⟨stroth34Statement_unconditional,
    stroth310Root_of_34 stroth34Statement_unconditional, stroth51Statement_unconditional,
    strothNtStatement_unconditional⟩
  have hn := stroth_6_3a stroth34Statement_unconditional stroth6LBStatement_holds G M Q Z B hc n t
    hs m hm hΩ
  obtain ⟨X, hQX, hXR, hNX, hNXQ, hcen, hsat⟩ :=
    stroth65XSplit_holds G M Q Z B hc n t hs m hm hn hΩ
  have e : HS6.Env hc n t m X := ⟨hs, hm, hn, hΩ, hQX, hXR, hNX, hNXQ, hcen⟩
  exact e.sl2_of_cent I (stroth63b_holds G M Q Z B hc n t hs m hm hΩ)
    (e.cent_of_corB I stroth44Statement_unconditional hB hCorB hsat outSolvableList_holds
      listCentralizerInvolutions_holds
      (fun D _ _ h => CFSG.RankThree.GF2n.Smith81.Smith23E1.listGroup_isSimpleGroup h)
      (fun D _ _ h => CFSG.RankThree.GF2n.Smith81.Smith23E1.kf7_listGroup_exists_noncomm h))

theorem stroth64_of_corB (hB : CorollaryBStmt) : Stroth64Statement :=
  stroth64_of_recog hB stroth64Recog_holds

end Certs

end CFSG.RankThree.GF2n.Stroth80
