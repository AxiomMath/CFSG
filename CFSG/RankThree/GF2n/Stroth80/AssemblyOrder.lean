module

public import CFSG.RankThree.GF2n.Stroth80.Assembly
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailStmtUn
public import CFSG.RankThree.GF2n.Stroth80.Sec12Omega6Order
public import CFSG.RankThree.GF2n.Stroth80.Sec12CaseVISpread

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

structure StrothSectionsOT : Prop where
  h34 : Stroth34Statement
  h37 : Stroth37Statement
  h44 : Stroth44Statement
  h310 : Stroth310Statement
  h65 : Stroth65Statement
  h78 : Stroth78Statement
  h79 : Stroth79Statement
  h716 : Stroth716TypeStatement
  h717 : Stroth717Statement
  h83 : Stroth83Statement
  h86 : Stroth86Statement
  h98 : Stroth98Statement
  h108 : Stroth108Statement
  h1111 : Stroth1111Statement
  h123 : Stroth123Statement
  noSp : Stroth121SpOrderStatement
  noOmega : Stroth121OmegaOrderStatement
  fstarLB : Stroth12FStarLBStatement
  omega6 : Stroth12Omega6OrderStatement
  genByB : StrothGenByBStatement
  nt : StrothNtStatement
  nbarGe : Stroth6NbarGeStatement
  notTI : Stroth1111NotTIStatement

theorem stroth_centTrivialOT (S : StrothSectionsOT) (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n)
    (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B) :
    CentTrivial M Q Z (Lgen M (LB M Q B)) := by
  haveI : (Q.subgroupOf M).Normal := hc.normal_Q_in_M
  set T := Lgen M (LB M Q B) with hT
  have hLT : bar M Q (LB M Q B) ≤ bar M Q T :=
    Subgroup.map_mono (fun x hx => le_Lgen (LB M Q B) (show (x : G) ∈ LB M Q B from hx))
  have hnorm : bar M Q (LB M Q B) ≤ Subgroup.normalizer
      ((Subgroup.centralizer (bar M Q T : Set (Mbar M Q)) ⊓ bar M Q (H0 M Z) :
        Subgroup (Mbar M Q)) : Set (Mbar M Q)) := by
    intro g hg
    have hgT : g ∈ bar M Q T := hLT hg
    have hgc : g ∈ Subgroup.centralizer ((Subgroup.centralizer (bar M Q T : Set (Mbar M Q)) ⊓
        bar M Q (H0 M Z) : Subgroup (Mbar M Q)) : Set (Mbar M Q)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (Subgroup.mem_centralizer_iff.mp ha.1 g hgT).symm
    exact Subgroup.centralizer_le_normalizer _ hgc
  have hbot := S.h44 G M Q Z B hc n hw hn hno hgen
    (Subgroup.centralizer (bar M Q T : Set (Mbar M Q)) ⊓ bar M Q (H0 M Z)) inf_le_right hnorm
    (stroth_odd S.h34 G M Q Z B hc n hw hn hno hgen)
  intro h hh hcomm
  have hhM : h ∈ M := hh.1
  have hmem : QuotientGroup.mk' (Q.subgroupOf M) ⟨h, hhM⟩ ∈
      Subgroup.centralizer (bar M Q T : Set (Mbar M Q)) ⊓ bar M Q (H0 M Z) := by
    refine ⟨Subgroup.mem_centralizer_iff.mpr ?_, ⟨⟨h, hhM⟩, show h ∈ H0 M Z from hh, rfl⟩⟩
    rintro _ ⟨s, hs, rfl⟩
    have hs' : (s : G) ∈ T := hs
    have hinv : (s : G)⁻¹ ∈ T := T.inv_mem hs'
    have hq : ⁅h, (s : G)⁻¹⁆ ∈ Q := hcomm _ hinv
    have e : QuotientGroup.mk' (Q.subgroupOf M) ⟨h, hhM⟩ * QuotientGroup.mk' (Q.subgroupOf M) s *
        (QuotientGroup.mk' (Q.subgroupOf M) ⟨h, hhM⟩)⁻¹ = QuotientGroup.mk' (Q.subgroupOf M) s := by
      rw [← map_inv, ← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq]
      show ((⟨h, hhM⟩ * s * ⟨h, hhM⟩⁻¹)⁻¹ * s : ↥M) ∈ Q.subgroupOf M
      rw [Subgroup.mem_subgroupOf]
      convert hq using 1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def, mul_inv_rev, inv_inv,
        mul_assoc]
    exact (mul_inv_eq_iff_eq_mul.mp e).symm
  rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at hmem
  exact hmem

theorem stroth_case_TIOT (S : StrothSectionsOT) (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n)
    (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B)
    (hTI : IsTIMod M Q (LB M Q B)) : StrothC3 M Q Z (Lgen M (LB M Q B)) := by
  haveI : (Q.subgroupOf M).Normal := hc.normal_Q_in_M
  obtain ⟨hn4, hbar, hSL⟩ := S.h37 G M Q Z B hc n hw hn hno hgen hTI
  subst hn4
  refine ⟨by simpa [Width] using hw, ?_, stroth_centTrivialOT S hc hw hn hno hgen⟩
  have hSL' : IsSLModel 2 (Nat.card Z ^ 3) ↥(bar M Q (Lgen M (LB M Q B))) := by
    rw [hbar]
    exact hSL
  exact quotSat_of_bar (fun X Y _ _ e h => IsSLModel.congr e h)
    (sec39_Q_le_LB.trans (le_Lgen (LB M Q B))) (Lgen_le (hc.LB_le_M)) hSL'

theorem stroth_case_a2OT (S : StrothSectionsOT) (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n)
    (hn : 2 < n) (ha : ∃ a ∈ LB M Q B, IsA2 Q Z a) :
    ¬ IsTIMod M Q (LB M Q B) ∧ CaseVI M Q Z (Lgen M (LB M Q B)) :=
  ⟨S.notTI G M Q Z B hc n hw hn ha, S.h1111 G M Q Z B hc n hw hn ha⟩

theorem stroth_case_6_5OT (S : StrothSectionsOT) (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n)
    (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B) {t : G}
    (ht : t ∈ LB M Q B) (htQ : t ∉ Q) (hN : Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z) :
    StrothCi M Q Z B t ∨ StrothCii M Q Z B t := by
  have hNt := S.nt G M Q Z B hc n hw hn hno hgen t ht htQ
  have hs6 : Stroth6Hyp hc n t := ⟨⟨hw, hn, hno, hgen, ht, htQ⟩, hN⟩
  rcases S.h65 G M Q Z B hc n t hs6 with ⟨hn4, hΩ⟩ |
      ⟨m, hm3, hnm, X, C, hQX, hXR, hNX, hNXQ, hcomm, hXnorm, hsign, hC, hLC, hCX, hCSL⟩
  · left
    subst hn4
    refine ⟨by simpa [Width] using hw, ?_, ?_⟩
    · rw [hNt, hN]
    · rw [hNt]
      exact hΩ
  · right
    subst hnm
    haveI : (Q.subgroupOf M).Normal := hc.normal_Q_in_M
    have hRle : Rt M (LB M Q B) t ≤ Lgen M (LB M Q B) := Rt_le_Lgen M (LB M Q B) t
    have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
    have hXM : X ≤ M := hXR.trans hRM
    have hMnormS : M ≤ Subgroup.normalizer (Lgen M (LB M Q B) : Set G) :=
      Lgen_normalizes M (LB M Q B)
    have hMnormX : M ≤ Subgroup.normalizer (X : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hXM).mp hXnorm
    have hMnormC : M ≤ Subgroup.normalizer (C : Set G) := by
      rw [← hLC]
      exact Lgen_normalizes M (hc.CN t)
    have hNR : hc.CN t ≤ Rt M (LB M Q B) t := fun x hx => (Ctx.mem_CN.mp hx).1
    have hNC : hc.CN t ≤ C := by
      rw [← hLC]
      exact le_Lgen (hc.CN t)
    have hCS : C ≤ Lgen M (LB M Q B) := by
      rw [← hLC]
      exact Lgen_le_of_normalized (hNR.trans hRle) hMnormS
    have hXS : X ≤ Lgen M (LB M Q B) := hXR.trans hRle
    have hCXS : C ⊔ X = Lgen M (LB M Q B) := by
      refine le_antisymm (sup_le hCS hXS) (Lgen_le_of_normalized ?_ ?_)
      · calc LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
          _ = hc.CN t ⊔ X := hNX.symm
          _ ≤ C ⊔ X := sup_le_sup_right hNC X
      · intro m' hm'
        have h1 : conjSubgroup m' C = C := conjSubgroup_eq_self_iff.mpr (hMnormC hm')
        have h2 : conjSubgroup m' X = X := conjSubgroup_eq_self_iff.mpr (hMnormX hm')
        have h3 : conjSubgroup m' (C ⊔ X) = C ⊔ X := by
          rw [conjSubgroup_sup', h1, h2]
        exact conjSubgroup_eq_self_iff.mp h3
    have hSnorm : (Q.subgroupOf (Lgen M (LB M Q B))).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer
        ((Lgen_le hc.LB_le_M).trans hc.hyp.Q_normal.2)
    have hQC : Q ≤ C := (hc.Q_le_CN ht).trans hNC
    have hcC : ∀ a ∈ C, ∀ b ∈ X, ⁅a, b⁆ ∈ Q := fun a ha b hb => ((hC a).mp ha).2 b hb
    have hcard : Nat.card Q = Nat.card Z ^ (4 * m + 1) := by
      unfold Width at hw
      rw [hw]
      congr 1
      ring
    refine ⟨m, by omega, hcard, by rw [hNt, hN], ?_⟩
    rcases hsign with ⟨hΩp, hXp⟩ | ⟨hΩm, hXm⟩
    · left
      refine ⟨by rw [hNt]; exact hΩp.quotSat, ?_⟩
      exact quotSat_isProdOf hQC hQX hCX hCXS hcC hSnorm hCSL hXp
    · right
      refine ⟨by rw [hNt]; exact hΩm.quotSat, ?_⟩
      exact quotSat_isProdOf hQC hQX hCX hCXS hcC hSnorm hCSL hXm

theorem classify310OT (S : StrothSectionsOT) (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n)
    (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B) {t : G}
    (ht : t ∈ LB M Q B) (htQ : t ∉ Q) :
    Rt M (LB M Q B) t = LB M Q B ∨ SLlike hc t ∨ BigNat hc t := by
  rcases S.h310 G M Q Z B hc n hw hn hno hgen t ht htQ with h | ⟨K, fK, finK, hK, h⟩
  · exact Or.inl h
  · right
    rcases h with ⟨m, hm, hrep⟩ | ⟨m, hm, hrep⟩ | ⟨m, hm, hrep⟩ | ⟨m, b, c, hm, hbc, hrep⟩
    · exact Or.inl ⟨m, hm, Or.inl ⟨K, fK, finK, hK, hrep⟩⟩
    · by_cases hm1 : m = 1
      · subst hm1
        exact Or.inl ⟨2, le_rfl, Or.inr ⟨rfl, K, fK, finK, hK, hrep⟩⟩
      · exact Or.inr (Or.inl ⟨m, by omega, K, fK, finK, hK, hrep⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨m, hm, K, fK, finK, hK, hrep⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨m, hm, K, fK, finK, hK, b, c, hbc, hrep⟩))

theorem stroth_exists_bigOT (S : StrothSectionsOT) (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n)
    (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B)
    (hTI : ¬ IsTIMod M Q (LB M Q B)) : ∃ t ∈ LB M Q B, t ∉ Q ∧ BigNat hc t := by
  by_contra hcon
  have hnobig : ∀ t ∈ LB M Q B, t ∉ Q → ¬ BigNat hc t := fun t ht htQ hb => hcon ⟨t, ht, htQ, hb⟩
  have hhyp : ∀ t ∈ LB M Q B, t ∉ Q → Rt M (LB M Q B) t = LB M Q B ∨ SLlike hc t := by
    intro t ht htQ
    rcases classify310OT S hc hw hn hno hgen ht htQ with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h (hnobig t ht htQ)
  obtain ⟨t₀, ht₀, ht₀Q, hR₀⟩ := hc.exists_Rt_ne_of_not_TI hTI
  exact S.h108 G M Q Z B hc n hw hn hno hgen hhyp
    ⟨t₀, ht₀, ht₀Q, (hhyp t₀ ht₀ ht₀Q).resolve_left hR₀⟩

theorem stroth_case_finalOT (S : StrothSectionsOT) (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n)
    (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B)
    (hTI : ¬ IsTIMod M Q (LB M Q B))
    (hlarge : ∀ τ ∈ LB M Q B, τ ∉ Q → Nat.card Q * Nat.card Z < Nat.card ↥(hc.CN τ))
    (IHS : Stroth1980Below (Nat.card G))
    (IHM : CFSG.RankThree.GF2n.Smith81.Smith1981TheoremBelow (Nat.card G)) :
    ∃ t ∈ LB M Q B, t ∉ Q ∧ CentTrivial M Q Z (Lgen M (LB M Q B)) ∧
      (StrothCi M Q Z B t ∨ StrothCii M Q Z B t ∨ StrothCiii M Q Z (Lgen M (LB M Q B)) ∨
        StrothCiv M Q Z B t ∨ StrothCv M Q Z B t) := by
  haveI : (Q.subgroupOf M).Normal := hc.normal_Q_in_M
  have s12 : Stroth12Hyp hc n := ⟨hw, hn, hno, hgen, hTI, hlarge⟩
  obtain ⟨t, ht, htQ, hbig⟩ := stroth_exists_bigOT S hc hw hn hno hgen hTI
  have s5 : Sec5Hyp hc n t := s12.toSec5 ht htQ
  have hgt : Nat.card Q * Nat.card Z < Nat.card ↥(hc.CN t) := hlarge t ht htQ
  refine ⟨t, ht, htQ, stroth_centTrivialOT S hc hw hn hno hgen, ?_⟩
  have hnoSp : ¬ ∃ m : ℕ, 2 ≤ m ∧ SpMNat hc t m := fun hsp =>
    S.noSp G M Q Z B hc n IHS s12 t ht htQ (S.h83 G M Q Z B hc n t s5 hsp)
      (S.h86 G M Q Z B hc n t s5 hsp)
  have hnot2 : ¬ OmegaPlusNat hc t 2 := fun h =>
    S.h98 G M Q Z B hc n hw hn hno hgen hlarge t ht htQ h
  obtain ⟨m, hm, hsign⟩ : ∃ m : ℕ, 2 ≤ m ∧ (OmegaPlusNat hc t m ∨ OmegaMinusNat hc t m) := by
    rcases hbig with h | ⟨m, hm, h⟩ | ⟨m, hm, h⟩
    · exact absurd h hnoSp
    · exact ⟨m, hm, Or.inl h⟩
    · exact ⟨m, hm, Or.inr h⟩
  have hconc := S.h78 G M Q Z B hc n t s5 hgt hnot2 m hm hsign
  have hc79 := S.h79 G M Q Z B hc n t s5 hgt hnot2 ⟨m, hm, hsign⟩
  have hNt := S.nt G M Q Z B hc n hw hn hno hgen t ht htQ
  have subcfg : n ≠ 10 →
      ((∃ m : ℕ, 4 ≤ m ∧ OmegaPlusNat hc t m) ∨ (∃ m : ℕ, 2 ≤ m ∧ OmegaMinusNat hc t m)) →
      SubConfig M Q Z (hc.CN t) := by
    intro hn10 hh
    rcases S.h716 G M Q Z B hc n t s5 hgt hh with hsub | ⟨hm3, -⟩
    · exact hsub
    · exfalso
      rcases S.h78 G M Q Z B hc n t s5 hgt hnot2 3 (by norm_num) (Or.inr hm3) with
        ⟨-, h10, -⟩ | ⟨h4, -⟩ | ⟨h4, -⟩ | ⟨h5', -⟩ | ⟨h6, -⟩
      · exact hn10 h10
      all_goals omega
  rcases hconc with ⟨rfl, hn10, hN⟩ | ⟨rfl, hn16, hN⟩ | ⟨rfl, hP4, hn12, hN⟩ |
      ⟨rfl, hP5, hn18, hN⟩ | ⟨rfl, hP6, hn28, hN⟩
  ·
    have hIii : Sec12Iii M Q Z (Lgen M (LB M Q B)) := by
      rcases hsign with hp | hm'
      · rcases S.h717 G M Q Z B hc n t s5 hgt hp with hsub | hF
        · exact S.omega6 G M Q Z B hc n IHM IHS s12 t ht htQ (Or.inl hp) hsub
        · exact stroth12FStarIii_of_lb S.fstarLB G M Q Z B hc n s12 t ht htQ (Or.inr ⟨hp, hF⟩)
      · rcases S.h716 G M Q Z B hc n t s5 hgt (Or.inr ⟨3, by norm_num, hm'⟩) with
          hsub | ⟨hm3, hF⟩
        · exact S.omega6 G M Q Z B hc n IHM IHS s12 t ht htQ (Or.inr hm') hsub
        · exact stroth12FStarIii_of_lb S.fstarLB G M Q Z B hc n s12 t ht htQ (Or.inl ⟨hm3, hF⟩)
    refine Or.inr (Or.inr (Or.inl ⟨?_, hIii⟩))
    subst hn10
    simpa [Width] using hw
  ·
    rcases hsign with hp | hm'
    · have hS := subcfg (by omega) (Or.inl ⟨4, le_rfl, hp⟩)
      refine Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_, ?_⟩)))
      · subst hn16
        simpa [Width] using hw
      · rw [hNt]
        exact hN
      · rw [hNt]
        exact hp.quotSat
      · rw [hNt]
        exact hS
    · exfalso
      exact S.noOmega G M Q Z B hc n IHS s12 t ht htQ (Or.inl ⟨Or.inl hm', hN⟩)
        (subcfg (by omega) (Or.inr ⟨4, by norm_num, hm'⟩)) hc79
  ·
    exfalso
    exact S.noOmega G M Q Z B hc n IHS s12 t ht htQ (Or.inr ⟨hP4, hn12, hN⟩)
      (subcfg (by omega) (Or.inl ⟨4, le_rfl, hP4⟩)) hc79
  ·
    exfalso
    exact S.noOmega G M Q Z B hc n IHS s12 t ht htQ (Or.inl ⟨Or.inr hP5, hN⟩)
      (subcfg (by omega) (Or.inl ⟨5, by norm_num, hP5⟩)) hc79
  ·
    have hS := subcfg (by omega) (Or.inl ⟨6, by norm_num, hP6⟩)
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_, ?_⟩)))
    · subst hn28
      simpa [Width] using hw
    · rw [hNt]
      exact hN
    · rw [hNt]
      exact hP6.quotSat
    · rw [hNt]
      exact hS

theorem stroth_order_step (S : StrothSectionsOT) {N : ℕ} (hS : Stroth1980Below N)
    (hM : CFSG.RankThree.GF2n.Smith81.Smith1981TheoremBelow N) : Stroth1980Below (N + 1) := by
  intro G _ _ hG M Q Z H B hB hBQ hBZ
  have hc : Ctx M Q Z B := ⟨H, hB, hBQ, hBZ⟩
  obtain ⟨n, hw⟩ := H.exists_width
  have hS' : Stroth1980Below (Nat.card G) := hS.mono (Nat.lt_succ_iff.mp hG)
  have hM' : CFSG.RankThree.GF2n.Smith81.Smith1981TheoremBelow (Nat.card G) :=
    hM.mono (Nat.lt_succ_iff.mp hG)
  refine strothConclusion_of (stroth_frobClause hc.hyp) ?_
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · interval_cases n
    · exact absurd hw hc.width_ne_zero
    · exact Or.inl (hc.hyp.isL3Type_of_width_one hw)
    · exact Or.inr (Or.inl ⟨by simpa [Width] using hw, S.h123 G M Q Z B hc hw⟩)
  · have hn : 2 < n := hn3
    by_cases ha : ∃ a ∈ LB M Q B, IsA2 Q Z a
    · exact Or.inr (Or.inr (Or.inr ⟨(stroth_case_a2OT S hc hw hn ha).1,
        Or.inr (stroth_case_a2OT S hc hw hn ha).2⟩))
    · have hno : NoA2 Q Z (LB M Q B) := fun a ha' hA2 => ha ⟨a, ha', hA2⟩
      have hgen : GenByB M Q B := S.genByB G M Q Z B hc n hw hn hno
      by_cases hTI : IsTIMod M Q (LB M Q B)
      · exact Or.inr (Or.inr (Or.inl (stroth_case_TIOT S hc hw hn hno hgen hTI)))
      · refine Or.inr (Or.inr (Or.inr ⟨hTI, Or.inl ⟨fun B' hB' hB'Q hB'Z =>
          strothNoA2Spread_of_h1111 S.h1111 G M Q Z B hc n hw hn hno hgen B'
            ⟨hc.hyp, hB', hB'Q, hB'Z⟩, ?_⟩⟩))
        by_cases h65 : ∃ t ∈ LB M Q B, t ∉ Q ∧
            Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z
        · obtain ⟨t, ht, htQ, hN⟩ := h65
          refine ⟨t, ht, htQ, stroth_centTrivialOT S hc hw hn hno hgen, ?_⟩
          rcases stroth_case_6_5OT S hc hw hn hno hgen ht htQ hN with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        · have hlarge : ∀ τ ∈ LB M Q B, τ ∉ Q →
              Nat.card Q * Nat.card Z < Nat.card ↥(hc.CN τ) := fun τ hτ hτQ =>
            lt_of_le_of_ne (S.nbarGe G M Q Z B hc n hw hn hno hgen τ hτ hτQ)
              (fun h => h65 ⟨τ, hτ, hτQ, h.symm⟩)
          exact stroth_case_finalOT S hc hw hn hno hgen hTI hlarge hS' hM'

end CFSG.RankThree.GF2n.Stroth80
