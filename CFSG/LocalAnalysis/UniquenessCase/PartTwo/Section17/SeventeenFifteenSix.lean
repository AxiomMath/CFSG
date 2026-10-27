module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFifteenProof
public import CFSG.GF2Type.Aschbacher1976Full.HSTransFinGroup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGammaInvolution
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34Thirteen
public import CFSG.Quasithin.EmptyFaithful.Insp9QS

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def Gap17_15_paraSixBranches (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q) : Prop :=
  IsL2Over17 (Bar2 L) 7 → V₀ = ⊥ → D.k = 2 →
    mBar D.M V₀ V hC.hyp125.isElemAbelian = 4 →
      Hyp154 D V₀ V L ∨ D.sig = {3}

theorem exists_involution_not_le_fixV_of_hyp125 {D : Data G} {V₀ V : Subgroup G}
    {L : Subgroup G} (h : Hyp125 D V₀ V) (hL : L ∈ calC D.M)
    (h151 : Hyp151 D V₀ V L)
    (hLb : barSub V₀ V h.isElemAbelian L ≠ ⊥) :
    ∃ t ∈ barSub V₀ V h.isElemAbelian L, orderOf t = 2 ∧
      ¬ wTil V₀ V h.isElemAbelian L ≤ fixV (Subgroup.zpowers t) := by
  classical
  have hV := h.isElemAbelian
  let Lb : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV L
  have hcomp := barSub_mem_compBar_of_ne_bot h hL hLb
  have hqC : CFSG.IsQuasisimple ↥Lb :=
    CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hcomp.2.2
  have hqGW : CFSG.GorensteinWalter.IsQuasisimple ↥Lb :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.2.mp hqC
  have heven : 2 ∣ Nat.card ↥Lb := CFSG.Walter.IsQuasisimple.two_dvd_card hqGW
  obtain ⟨t, ht2⟩ := exists_prime_orderOf_dvd_card' (G := ↥Lb) 2 heven
  by_contra hcon
  push Not at hcon
  let I : Set ↥Lb := {x | x ^ 2 = 1}
  let N : Subgroup ↥Lb := Subgroup.closure I
  have hIinv : ∀ g x : ↥Lb, x ∈ I → g * x * g⁻¹ ∈ I := by
    intro g x hx
    change (g * x * g⁻¹) ^ 2 = 1
    calc (g * x * g⁻¹) ^ 2 = g * x ^ 2 * g⁻¹ := by
          rw [pow_two, pow_two]
          group
      _ = 1 := by rw [show x ^ 2 = 1 from hx]; group
  have hNclosure : Subgroup.normalClosure I = N :=
    CFSG.GroupTheory.normalClosure_eq_closure_of_conj_invariant hIinv
  have hNnormal : N.Normal := by
    rw [← hNclosure]
    exact Subgroup.normalClosure_normal
  have htI : t ∈ I := by
    change t ^ 2 = 1
    have := pow_orderOf_eq_one t
    rwa [ht2] at this
  have hNne : N ≠ ⊥ := by
    intro hbot
    have htN : t ∈ N := Subgroup.subset_closure htI
    have ht1 : t = 1 := Subgroup.mem_bot.mp (hbot ▸ htN)
    have : orderOf t = 1 := by rw [ht1]; exact orderOf_one
    omega
  have hfixI : ∀ x : ↥Lb, x ∈ I →
      wTil V₀ V hV L ≤ fixV (Subgroup.zpowers (x : MulAut (Vtil V₀ V hV))) := by
    intro x hx
    by_cases hx1 : x = 1
    · subst hx1
      change wTil V₀ V hV L ≤ fixV (Subgroup.zpowers (1 : MulAut (Vtil V₀ V hV)))
      rw [Subgroup.zpowers_one_eq_bot]
      have hfixbot : fixV (⊥ : Subgroup (MulAut (Vtil V₀ V hV))) = ⊤ := by
        ext v
        simp [mem_fixV]
      rw [hfixbot]
      exact le_top
    · have hxord : orderOf x = 2 :=
        orderOf_eq_prime (show x ^ 2 = 1 from hx) hx1
      exact hcon (x : MulAut (Vtil V₀ V hV)) x.2 (by simpa using hxord)
  have hNmap_closure : N.map Lb.subtype =
      Subgroup.closure (Lb.subtype '' I) := by
    rw [show N = Subgroup.closure I from rfl, MonoidHom.map_closure]
  have hNfix : wTil V₀ V hV L ≤ fixV (N.map Lb.subtype) := by
    intro w hw
    rw [hNmap_closure, CFSG.QuasithinUnique.Setup.X1.mem_fixV_closure]
    intro s hs
    rcases hs with ⟨y, hy, rfl⟩
    exact mem_fixV.mp (hfixI y hy hw) (y : MulAut (Vtil V₀ V hV))
      ((Subgroup.mem_zpowers_iff.mpr ⟨1, pow_one _⟩))
  have hNcomm : commSub (wTil V₀ V hV L) (N.map Lb.subtype) = ⊥ :=
    commSub_eq_bot_iff.mpr hNfix
  have : N.Normal := hNnormal
  rcases CFSG.Quasithin.Insp9.qs_normal_le_center_or_top hqC N with hNcenter | hNtop
  ·
    have hN2 : IsPGroup 2 N := by
      have hsq : ∀ u ∈ I, u * u = 1 := by
        intro u hu
        simpa [pow_two] using (show u ^ 2 = 1 from hu)
      have hcommI : ∀ u ∈ I, ∀ v ∈ I, u * v = v * u := by
        intro u hu v hv
        have huZ : u ∈ Subgroup.center ↥Lb := hNcenter (Subgroup.subset_closure hu)
        exact (Subgroup.mem_center_iff.mp huZ v).symm
      exact CFSG.GF2Type.Aschbacher1976Full.HS.TransFin.isPGroup_closure_of_comm hsq hcommI
    have hNcore : N ≤ CFSG.pCore 2 ↥Lb :=
      CFSG.LieType.BorelTits.le_pCore 2 hNnormal hN2
    have hNmap : N.map Lb.subtype ≤ CFSG.Open.pCoreOf 2 Lb := by
      rw [CFSG.openPCoreOf_eq_map_pCore]
      exact Subgroup.map_mono hNcore
    have hNcoreM : N.map Lb.subtype ≤ CFSG.Open.pCoreOf 2 (Mbar D.M V₀ V hV) :=
      hNmap.trans (CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2 hcomp.2.1)
    have hO2M : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O2Trivial
        (Mbar D.M V₀ V hV) :=
      fun P hP hPn hP2 => s15_Kbar_eq_bot_of_normal_isPGroup D h hP hPn hP2
    have hCoreM : CFSG.Open.pCoreOf 2 (Mbar D.M V₀ V hV) = ⊥ := by
      refine hO2M _ (CFSG.LieType.BorelTits.pCoreOf_le 2 _) ?_
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
      rw [CFSG.openPCoreOf_subgroupOf]
      exact CFSG.LieType.BorelTits.pCore_normal (r := 2) (G := Mbar D.M V₀ V hV)
    have hNamb_bot : N.map Lb.subtype = ⊥ :=
      le_bot_iff.1 (hNcoreM.trans (le_of_eq hCoreM))
    apply hNne
    rw [eq_bot_iff]
    intro x hx
    have hxmap : (x : MulAut (Vtil V₀ V hV)) ∈ N.map Lb.subtype :=
      Subgroup.mem_map_of_mem _ hx
    rw [hNamb_bot] at hxmap
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hxmap))
  ·
    have hNambL : N.map Lb.subtype = Lb := by
      ext x
      constructor
      · intro hx
        rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
        exact y.2
      · intro hx
        exact Subgroup.mem_map_of_mem Lb.subtype (by
          show (⟨x, hx⟩ : ↥Lb) ∈ N
          rw [hNtop]
          trivial)
    have hcommL : commSub (wTil V₀ V hV L) Lb = ⊥ := by
      rw [← hNambL]
      exact hNcomm
    have hself := s15_Core_commSub_wTil_conj (D := D) (V₀ := V₀) (V := V) (L := L)
      h151 (m := 1) D.M.one_mem
    have hself' : commSub (wTil V₀ V hV L) Lb = wTil V₀ V hV L := by
      simpa [Lb, conjSubgroup_one] using hself
    have hwbot : wTil V₀ V hV L = ⊥ := by
      rw [← hself']
      exact hcommL
    apply hLb
    have htopbot : commSub (⊤ : Subgroup (Vtil V₀ V hV)) Lb = ⊥ := by
      simpa [wTil, Lb] using hwbot
    simpa [Lb] using s15_Lin_eq_bot_of_commSub_top_eq_bot htopbot

theorem gap17_15_paraSix_of (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q)
    (h1217 : R1217 D) (hR127 : R127 D)
    (h117 : C117 D V₀ V) (h1771 : R17_7_1At D V₀ V L r q hC)
    (hSg : UC6S846.SigmaStd D) (hR1513 : R15_13Small D)
    (hGap : Gap17_15_paraSixBranches D V₀ V L r q hC) :
    Gap17_15_paraSix D V₀ V L r q hC := by
  intro h7 hV0 hk2 hm4
  subst hV0
  rcases hGap h7 rfl hk2 hm4 with h154 | hsig
  ·
    have h151 : Hyp151 D ⊥ V L := h154.hyp151
    have hV : IsElemAbelian 2 V := h151.isElemAbelian
    have hUL : UniqueMax D.M L := h1771
    have hbar : barSub ⊥ V hV L ≠ ⊥ :=
      barSub_ne_bot_of_uniqueMax hR127 h151.hyp125 h117 hC.memL hUL
    have h15 := hR1513 ⊥ V L h154 (by rw [mSub, rk_bot]; omega) hbar
    have hγle : gamma15 D.M ⊥ V hV L ≤ 3 := h15.1
    obtain ⟨t, htL, hto, -⟩ :=
      exists_involution_not_le_fixV_of_hyp125 h151.hyp125 hC.memL h151 hbar
    have hmle := mBar_le_gamma15_of_R1217 D h1217 h151 hbar htL hto
    omega
  ·
    have hns : ¬ Group.IsSolvable ↥D.M := UC6S846.not_solvable_of_mem_calC hC.memL
    have h3 : 3 ∈ D.sig := by
      rw [hsig]
      exact Set.mem_singleton 3
    have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M :=
      UC6S846.sp_of_mem_sig hSg hns h3
    have hk1 : D.k = 1 := s16c1614_k_eq_one_of_sp D hsp
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

end
