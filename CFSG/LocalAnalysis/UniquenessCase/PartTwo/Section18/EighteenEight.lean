module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Statements
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSixFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Statements
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGammaBounds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGammaInvolution
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4136Mbar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FstarBridge
public import CFSG.GroupTheory.SupCommute
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Hyp154
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSeventeen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSixtyNine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.DeltaAPI
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtySixShape
public import CFSG.Quasithin.EmptyFaithful.S151S4D
public import CFSG.Quasithin.EmptyFaithful.Insp9QS
public import CFSG.Foundations.SteinbergCADefinitionNodes
public import CFSG.GroupTheory.OddOrderClosurePResidual
public import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.LieType.BorelTits.Basic
public import CFSG.GF2Type.Aschbacher1976Full.HSTransFinGroup
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Fix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34Thirteen
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S2Basic
public import CFSG.LargeExtraspecial.S5Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineMain
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenEleven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenNine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThirteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwelve
public import CFSG.Quasithin.EmptyFaithful.S151ZC
public import CFSG.Quasithin.Vol2.Ch11SecD552
public import CFSG.Quasithin.Vol2.Ch11SecD555
public import CFSG.Quasithin.Vol2.Ch11SecD556
public import CFSG.Quasithin.Vol2.Ch11SecD556I
public import CFSG.Quasithin.Vol2.Ch11SecD557A
public import CFSG.Quasithin.Vol2.Ch11SecFCase2
public import CFSG.Quasithin.Vol2.Ch11SecFKL1b
public import CFSG.Quasithin.Vol2.Ch11SecFQ3
public import CFSG.Quasithin.Vol2.Ch11StatementsF
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem hyp151_of_p18_6_5 {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (h5 : P18_6_5 D V₀ V p L h) : Hyp151 D V₀ V L := by
  classical
  have hV := h.hyp125.isElemAbelian
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hLstab : L ≤ stabTil V₀ V := h.L_le_M.trans hMs
  have hLbar : barSub V₀ V hV L ∈ compBar D.M V₀ V hV ∨
      barSub V₀ V hV L = ⊥ := by
    by_cases hb : barSub V₀ V hV L = ⊥
    · exact Or.inr hb
    · exact Or.inl (barSub_mem_compBar_of_ne_bot h.hyp125 h.hL.1 hb)
  refine ⟨h.hyp125, h.L_le_M, ?_, ?_, ?_⟩
  · exact CFSG.Quasithin.S151S4.twoResidual_eq_self_of_perfect h.hL.1.2.1
  · rcases hLbar with hc | hb
    · exact fstar_eq_self_of_isQuasisimple hc.2.2
    · rw [hb]
      exact le_bot_iff.1 (Subgroup.map_subtype_le _)
  · intro g hgM hgn
    have hLgne : barSub V₀ V hV (conjSubgroup L g) ≠ barSub V₀ V hV L := by
      intro heq
      exact hgn ((s15_Infra_mem_nBar_iff h.hyp125 hV hgM).2 heq)
    have hLgcal : conjSubgroup L g ∈ calC D.M :=
      uc22p22u_calC_conj (X := D.M) (M := D.M) (K := L) Subgroup.le_normalizer h.hL.1
        (m := g) hgM
    have hneL : conjSubgroup L g ≠ L := by
      intro heq
      exact hLgne (by rw [heq])
    have hLgM : conjSubgroup L g ≤ D.M := by
      intro x hx
      rw [mem_conjSubgroup_iff] at hx
      have hx' : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      rw [hx']
      exact D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hgM) (h.L_le_M hx)) hgM
    have hLgstab : conjSubgroup L g ≤ stabTil V₀ V := hLgM.trans hMs
    have hcommG : ⁅barSub V₀ V hV L, barSub V₀ V hV (conjSubgroup L g)⁆ = ⊥ := by
      have hle : ⁅L, conjSubgroup L g⁆ ≤ pCoreOf 2 L :=
        (calC_commutator_le_of_ne h.hL.1 hLgcal hneL.symm).trans inf_le_left
      have hbotL : barSub V₀ V hV (pCoreOf 2 L) = ⊥ :=
        TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal hV h.hL.1.1
          (barSub_pCoreOf_eq_bot_of_hyp125 h.hyp125)
      have hmap : barSub V₀ V hV ⁅L, conjSubgroup L g⁆ = ⊥ :=
        le_bot_iff.1 (hbotL ▸ barSub_mono V₀ V hV hle)
      have hlebar := commutator_barSub_le (V₀ := V₀) (V := V) hV hLstab hLgstab
      exact le_bot_iff.1 (hmap ▸ hlebar)
    refine ⟨hcommG, ?_⟩
    have hgN : g ∉ normalizer (L : Set G) := by
      intro hnorm
      apply hgn
      rw [s15_Infra_mem_nBar_iff h.hyp125 hV hgM,
        conjSubgroup_eq_iff_mem_normalizer.mpr hnorm]
    have hgroup := h5.2 g hgM hgN
    have hA : ⁅V, L⁆ ≤ V := commutator_le_of_le_stabTil_general hLstab
    have hEq := imgTil_commutator_eq_commSub_of_le (V₀ := V₀) (V := V) hV hA hLgstab
      (A := ⁅V, L⁆) (X := conjSubgroup L g)
    have hW : imgTil V₀ V hV ⁅V, L⁆ = wTil V₀ V hV L := by
      rw [imgTil_commutator_eq_commSub_of_le (V₀ := V₀) (V := V) hV le_rfl hLstab,
        s15_Infra_imgTil_top]
      rfl
    rw [hgroup, TwelveSeventeen.imgTil_bot, hW] at hEq
    exact hEq.symm


theorem two_le_s15_of_p18_6_5 {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (h5 : P18_6_5 D V₀ V p L h) (h151 : Hyp151 D V₀ V L)
    (hLb : barSub V₀ V h.hyp125.isElemAbelian L ≠ ⊥) :
    2 ≤ s15 D.M V₀ V h.hyp125.isElemAbelian L := by
  classical
  have hV := h.hyp125.isElemAbelian
  by_contra hlt
  have hpos : 0 < s15 D.M V₀ V hV L := by
    have h := s15_Core_s15_eq_ncard_range (D := D) h151
    rw [h]
    refine (Set.ncard_pos (Set.toFinite _)).2 ?_
    exact ⟨barSub V₀ V hV L, ⟨(1 : D.M), by
        change barSub V₀ V hV (conjSubgroup L (1 : G)) = barSub V₀ V hV L
        rw [conjSubgroup_one]⟩⟩
  have hs : s15 D.M V₀ V hV L = 1 := by omega
  have hcard :
      (Set.range (fun m : D.M => barSub V₀ V hV (conjSubgroup L (m : G)))).ncard = 1 := by
    rw [← s15_Core_s15_eq_ncard_range (D := D) h151]
    exact hs
  obtain ⟨A, hA⟩ := Set.ncard_eq_one.1 hcard
  obtain ⟨K, hKmem, hKne⟩ := exists_mem_conjSetOf_ne_of_conjClosure_ne h5.1
  obtain ⟨g, hgM, rfl⟩ := hKmem
  let x : G := g⁻¹
  have hxM : x ∈ D.M := D.M.inv_mem hgM
  have hKx : conjSubgroup L x ≠ L := by
    simpa [x, conjSubgroup] using hKne
  have hbar : barSub V₀ V hV (conjSubgroup L x) = barSub V₀ V hV L := by
    have h1 : barSub V₀ V hV (conjSubgroup L x) ∈
        (Set.range (fun m : D.M => barSub V₀ V hV (conjSubgroup L (m : G)))) :=
      ⟨⟨x, hxM⟩, rfl⟩
    have h2 : barSub V₀ V hV L ∈
        (Set.range (fun m : D.M => barSub V₀ V hV (conjSubgroup L (m : G)))) :=
      ⟨(1 : D.M), by
        change barSub V₀ V hV (conjSubgroup L (1 : G)) = barSub V₀ V hV L
        rw [conjSubgroup_one]⟩
    rw [hA, Set.mem_singleton_iff] at h1 h2
    exact h1.trans h2.symm
  have hLxcal : conjSubgroup L x ∈ calC D.M :=
    uc22p22u_calC_conj (X := D.M) (M := D.M) (K := L) Subgroup.le_normalizer h.hL.1
      (m := x) hxM
  have hcommG : ⁅barSub V₀ V hV L, barSub V₀ V hV (conjSubgroup L x)⁆ = ⊥ := by
    have hle : ⁅L, conjSubgroup L x⁆ ≤ pCoreOf 2 L :=
      (calC_commutator_le_of_ne h.hL.1 hLxcal hKx.symm).trans inf_le_left
    have hbot : barSub V₀ V hV (pCoreOf 2 L) = ⊥ :=
      TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal hV h.hL.1.1
        (barSub_pCoreOf_eq_bot_of_hyp125 h.hyp125)
    have hmap : barSub V₀ V hV ⁅L, conjSubgroup L x⁆ = ⊥ :=
      le_bot_iff.1 (hbot ▸ barSub_mono V₀ V hV hle)
    have hMs : D.M ≤ stabTil V₀ V :=
      le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
    have hLstab : L ≤ stabTil V₀ V := h.L_le_M.trans hMs
    have hLxM : conjSubgroup L x ≤ D.M := by
      intro y hy
      rw [mem_conjSubgroup_iff] at hy
      have hy' : y = x⁻¹ * (x * y * x⁻¹) * x := by group
      rw [hy']
      exact D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hxM) (h.L_le_M hy)) hxM
    have hlebar := commutator_barSub_le (V₀ := V₀) (V := V) hV hLstab (hLxM.trans hMs)
    exact le_bot_iff.1 (hmap ▸ hlebar)
  rw [hbar] at hcommG
  have hcent : barSub V₀ V hV L ≤
      Subgroup.centralizer (barSub V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcommG
  have hcomm : ∀ a b : ↥(barSub V₀ V hV L), a * b = b * a := by
    intro a b
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hcent a.2) b b.2).symm
  have hcomp := barSub_mem_compBar_of_ne_bot h.hyp125 h.hL.1 hLb
  have hqC : CFSG.IsQuasisimple ↥(barSub V₀ V hV L) :=
    CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hcomp.2.2
  exact CFSG.Quasithin.Insp9.qs_not_commutative hqC hcomm


private theorem wSub_le_commutator_sup_V0 {D : Data G} {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) :
    wSub V₀ V h.isElemAbelian L ≤ ⁅V, L⁆ ⊔ V₀ := by
  have hV := h.isElemAbelian
  have hLstab : L ≤ stabTil V₀ V :=
    h.le.trans (le_stabTil h.hyp125.pairFacts.le_normalizer
      h.hyp125.pairFacts.le_normalizer₀)
  have hcommV : ⁅V, L⁆ ≤ V := commutator_le_of_le_stabTil_general hLstab
  intro w hw
  have hWV : w ∈ V := preTil_le V₀ V hV _ hw
  have hwT : mkTil V₀ V hV (IntMod.mk hV ⟨w, hWV⟩) ∈ wTil V₀ V hV L :=
    (mem_preTil_iff_of_mem V₀ V hV _ hWV).1 hw
  have hWt : wTil V₀ V hV L = imgTil V₀ V hV ⁅V, L⁆ := by
    change CFSG.Quasithin.commSub ⊤ (barSub V₀ V hV L) = imgTil V₀ V hV ⁅V, L⁆
    have hEq : imgTil V₀ V hV ⁅V, L⁆ = commSub ⊤ (barSub V₀ V hV L) := by
      rw [imgTil_commutator_eq_commSub_of_le (V₀ := V₀) (V := V) hV le_rfl hLstab,
        s15_Infra_imgTil_top]
    exact hEq.symm
  rw [hWt] at hwT
  obtain ⟨x, hx, hxeq⟩ := (mem_imgTil V₀ V hV ⁅V, L⁆ _).1 hwT
  have hdiff : w * x.val⁻¹ ∈ V₀ := by
    have h := (mkTil_eq_iff V₀ V hV x (IntMod.mk hV ⟨w, hWV⟩)).1 hxeq
    have h2 : (x.val * (IntMod.mk hV ⟨w, hWV⟩).val⁻¹)⁻¹ ∈ V₀ := V₀.inv_mem h
    have h2' : (IntMod.mk hV ⟨w, hWV⟩).val * x.val⁻¹ ∈ V₀ := by
      simpa [mul_inv_rev, inv_inv] using h2
    have hval : (IntMod.mk hV ⟨w, hWV⟩).val = w := rfl
    rwa [hval] at h2'

  have hxmem : x.val ∈ ⁅V, L⁆ := hx
  have hxV : x.val ∈ V := hcommV hxmem
  have hxw : x.val * w = w * x.val := B2F.isElemAbelian_comm hV hxV hWV
  have hwx : x.val * (w * x.val⁻¹) = w := by
    calc x.val * (w * x.val⁻¹) = (x.val * w) * x.val⁻¹ := by group
      _ = (w * x.val) * x.val⁻¹ := by rw [hxw]
      _ = w := by group
  rw [← hwx]
  exact Subgroup.mul_mem_sup hxmem hdiff

private theorem p18_cent_wSub_conj {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (h5 : P18_6_5 D V₀ V p L h) (h151 : Hyp151 D V₀ V L)
    {x m : G} (hxM : x ∈ D.M) (hmM : m ∈ D.M)
    (hne : conjSubgroup L x ≠ conjSubgroup L m) :
    conjSubgroup (wSub V₀ V h.hyp125.isElemAbelian L) m ≤
      Subgroup.centralizer (conjSubgroup L x : Set G) := by
  have hV := h.hyp125.isElemAbelian
  let y : G := x * m⁻¹
  have hyM : y ∈ D.M := D.M.mul_mem hxM (D.M.inv_mem hmM)
  have hyN : y ∉ normalizer (L : Set G) := by
    intro hyN
    have hyL : conjSubgroup L y = L := conjSubgroup_eq_iff_mem_normalizer.mpr hyN
    apply hne
    have h1 : conjSubgroup (conjSubgroup L y) m = conjSubgroup L (y * m) :=
      conjSubgroup_conjSubgroup L y m
    rw [hyL] at h1
    have hyx : y * m = x := by simp [y, mul_assoc]
    rw [hyx] at h1
    exact h1.symm
  have hgroup := h5.2 y hyM hyN
  have hcard : Nat.card V₀ ≤ 2 :=
    (mSub_le_one_iff h.hyp125.pairFacts.elemAbelian₀).1 h.small
  have hLyM : conjSubgroup L y ≤ D.M := by
    intro z hz
    rw [mem_conjSubgroup_iff] at hz
    have hz' : z = y⁻¹ * (y * z * y⁻¹) * y := by group
    rw [hz']
    exact D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hyM) (h.L_le_M hz)) hyM
  have hV0comm : ⁅V₀, conjSubgroup L y⁆ = ⊥ :=
    CFSG.RankThree.PartOne.commutator_eq_bot_of_card_le_two hcard
      (hLyM.trans h.hyp125.pairFacts.le_normalizer₀)
  have hcent1 : ⁅V, L⁆ ≤ Subgroup.centralizer (conjSubgroup L y : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hgroup
  have hcent2 : V₀ ≤ Subgroup.centralizer (conjSubgroup L y : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hV0comm
  have hcommW : ⁅wSub V₀ V hV L, conjSubgroup L y⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have ha' : (a : G) ∈ (⁅V, L⁆ ⊔ V₀ : Subgroup G) :=
      wSub_le_commutator_sup_V0 (D := D) h151 ha
    have hMs : D.M ≤ stabTil V₀ V :=
      le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
    have hcommV : ⁅V, L⁆ ≤ V :=
      commutator_le_of_le_stabTil_general (h.L_le_M.trans hMs)
    have hcommAB : ∀ a ∈ ⁅V, L⁆, ∀ b ∈ V₀, Commute a b :=
      fun a ha b hb => B2F.isElemAbelian_comm hV (hcommV ha) (h.hyp125.pairFacts.le hb)
    rcases (CFSG.mem_sup_of_commute hcommAB).mp ha' with ⟨a₁, ha₁, a₂, ha₂, rfl⟩
    have h1 : a₁ * b = b * a₁ := (Subgroup.mem_centralizer_iff.mp (hcent1 ha₁) b hb).symm
    have h2 : a₂ * b = b * a₂ := (Subgroup.mem_centralizer_iff.mp (hcent2 ha₂) b hb).symm
    show b * (a₁ * a₂) = (a₁ * a₂) * b
    calc b * (a₁ * a₂) = (b * a₁) * a₂ := by group
      _ = (a₁ * b) * a₂ := by rw [← h1]
      _ = a₁ * (b * a₂) := by group
      _ = a₁ * (a₂ * b) := by rw [← h2]
      _ = (a₁ * a₂) * b := by group
  have hconj := E3.conjSubgroup_commutator (wSub V₀ V hV L) (conjSubgroup L y) m
  rw [hcommW, E3.conjSubgroup_bot, conjSubgroup_conjSubgroup] at hconj
  have hyx : y * m = x := by simp [y, mul_assoc]
  rw [hyx] at hconj
  have hcent : conjSubgroup (wSub V₀ V hV L) m ≤
      Subgroup.centralizer (conjSubgroup L x : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hconj.symm
  intro w hw
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  exact Subgroup.mem_centralizer_iff.mp (hcent hw) l hl

private theorem p18_cent_v1Sub {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (h5 : P18_6_5 D V₀ V p L h) (h151 : Hyp151 D V₀ V L)
    {x : G} (hxM : x ∈ D.M) :
    v1Sub D.M V₀ V h.hyp125.isElemAbelian L ≤
      Subgroup.centralizer (conjSubgroup L x : Set G) := by
  have hV := h.hyp125.isElemAbelian
  by_cases h0 : V₀ = ⊥
  · rw [v1Sub_of_eq_bot D.M V₀ V hV L h0]
    refine iSup_le fun m : D.M => ?_
    intro w hw
    rw [E3.conjSubgroup_inf] at hw
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    by_cases hxm : conjSubgroup L x = conjSubgroup L (m : G)
    · have hwC : w ∈ Subgroup.centralizer (conjSubgroup L (m : G) : Set G) := by
        have hc0 := (Subgroup.mem_inf.1 hw).2
        have hc : (m : G) * w * (m : G)⁻¹ ∈ Subgroup.centralizer (L : Set G) :=
          (mem_conjSubgroup_iff).1 hc0
        rw [Subgroup.mem_centralizer_iff] at hc ⊢
        intro l' hl'
        have hlL : (m : G) * l' * (m : G)⁻¹ ∈ L := (mem_conjSubgroup_iff).1 hl'
        have hcomm := hc ((m : G) * l' * (m : G)⁻¹) hlL
        have := congrArg (fun t => (m : G)⁻¹ * t * (m : G)) hcomm
        simpa [mul_assoc] using this
      rw [← hxm] at hwC
      exact Subgroup.mem_centralizer_iff.mp hwC l hl
    · have hle := p18_cent_wSub_conj h h5 h151 hxM m.2 hxm
      exact Subgroup.mem_centralizer_iff.mp (hle (Subgroup.mem_inf.1 hw).1) l hl
  · rw [v1Sub_of_ne_bot D.M V₀ V hV L h0]
    have hcard : Nat.card V₀ ≤ 2 :=
      (mSub_le_one_iff h.hyp125.pairFacts.elemAbelian₀).1 h.small
    have hV0c : V₀ ≤ Subgroup.centralizer (D.M : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (CFSG.RankThree.PartOne.commutator_eq_bot_of_card_le_two hcard
          h.hyp125.pairFacts.le_normalizer₀)
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hlM : l ∈ D.M := by
      have hLxM : conjSubgroup L x ≤ D.M := by
        intro z hz
        rw [mem_conjSubgroup_iff] at hz
        have hz' : z = x⁻¹ * (x * z * x⁻¹) * x := by group
        rw [hz']
        exact D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hxM) (h.L_le_M hz)) hxM
      exact hLxM hl
    exact Subgroup.mem_centralizer_iff.mp (hV0c hw) l hlM


@[expose] def Delta18_8At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  P18_6_5 D V₀ V p L h → Hyp151 D V₀ V L → UniqueMax D.M L →
    barSub V₀ V h.hyp125.isElemAbelian L ≠ ⊥ → V₀ = ⊥ →
    delta15 D.M V₀ V h.hyp125.isElemAbelian L <
      gamma15 D.M V₀ V h.hyp125.isElemAbelian L - 1

theorem hyp154_of_p18_6_5 (D : Data G)
    {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (hSg : UC6S846.SigmaStd D) (h1217 : R1217 D)
    (h : Hyp18 D V₀ V p L) (h5 : P18_6_5 D V₀ V p L h)
    (h151 : Hyp151 D V₀ V L) (hLb : barSub V₀ V h.hyp125.isElemAbelian L ≠ ⊥)
    (hUL : UniqueMax D.M L)
    (hδ : V₀ = ⊥ → delta15 D.M V₀ V h.hyp125.isElemAbelian L <
      gamma15 D.M V₀ V h.hyp125.isElemAbelian L - 1) : Hyp154 D V₀ V L := by
  classical
  have hV := h.hyp125.isElemAbelian
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  obtain ⟨K, hKmem, hKne⟩ := exists_mem_conjSetOf_ne_of_conjClosure_ne h5.1
  obtain ⟨g, hgM, rfl⟩ := hKmem
  let x : G := g⁻¹
  have hxM : x ∈ D.M := D.M.inv_mem hgM
  have hKx : conjSubgroup L x ≠ L := by
    simpa [x, conjSubgroup] using hKne
  have hxN : x ∉ normalizer (L : Set G) := fun hN =>
    hKx (conjSubgroup_eq_iff_mem_normalizer.mpr hN)
  have hULx : UniqueMax D.M (conjSubgroup L x) := by
    have h := uniqueMax_conjSubgroup hUL x
    rwa [s15_Tools_conjSubgroup_M D hxM] at h
  have hLxM : conjSubgroup L x ≤ D.M := by
    intro l hl
    rw [mem_conjSubgroup_iff] at hl
    have hl' : l = x⁻¹ * (x * l * x⁻¹) * x := by group
    rw [hl']
    exact D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hxM) (h.L_le_M hl)) hxM
  have hWC : wSub V₀ V hV L ≤ Subgroup.centralizer (conjSubgroup L x : Set G) := by
    have h := p18_cent_wSub_conj h h5 h151 hxM (D.M.one_mem) (by
      simpa [conjSubgroup_one] using hKx)
    simpa [conjSubgroup_one] using h
  have hV1C : v1Sub D.M V₀ V hV L ≤ Subgroup.centralizer (conjSubgroup L x : Set G) :=
    p18_cent_v1Sub h h5 h151 hxM
  have hWVC : wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L ≤
      Subgroup.centralizer (conjSubgroup L x : Set G) := sup_le hWC hV1C
  refine ⟨h151, ?_, ?_, ?_⟩
  ·
    intro w hw hw1
    refine uc22p22u_uniqueMax_mono D ?_ inf_le_left hULx
    refine le_inf hLxM ?_
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (hWVC hw) l hl
  ·
    intro x' hx'M y' hy'M _ w hw hw1
    have hV1C' : v1Sub D.M V₀ V hV L ≤ Subgroup.centralizer (conjSubgroup L x' : Set G) :=
      p18_cent_v1Sub h h5 h151 hx'M
    have hS : (⨆ X ∈ {X | X ∈ wConj D.M V₀ V hV L ∧
        X ≠ conjSubgroup (wSub V₀ V hV L) x' ∧
        X ≠ conjSubgroup (wSub V₀ V hV L) y'}, X) ≤
        Subgroup.centralizer (conjSubgroup L x' : Set G) := by
      refine iSup_le fun X => iSup_le fun hX => ?_
      obtain ⟨m, hmM, rfl⟩ := hX.1
      have hne : conjSubgroup L x' ≠ conjSubgroup L m := by
        intro heq
        apply hX.2.1
        rw [← s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs hmM),
          ← s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs hx'M), heq]
      exact p18_cent_wSub_conj h h5 h151 hx'M hmM hne
    have hsupC := sup_le hV1C' hS
    have hULx' : UniqueMax D.M (conjSubgroup L x') := by
      have h := uniqueMax_conjSubgroup hUL x'
      rwa [s15_Tools_conjSubgroup_M D hx'M] at h
    have hLx'M : conjSubgroup L x' ≤ D.M := by
      intro l hl
      rw [mem_conjSubgroup_iff] at hl
      have hl' : l = x'⁻¹ * (x' * l * x'⁻¹) * x' := by group
      rw [hl']
      exact D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hx'M) (h.L_le_M hl)) hx'M
    refine uc22p22u_uniqueMax_mono D ?_ inf_le_left hULx'
    refine le_inf hLx'M ?_
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (hsupC hw) l hl
  ·
    intro g hgM X hX Y hY hXY hne
    have hcomp := barSub_mem_compBar_of_ne_bot h.hyp125 h.hL.1 hLb
    have hqC : CFSG.IsQuasisimple ↥(barSub V₀ V hV L) :=
      CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hcomp.2.2
    have hsolv : ¬ Group.IsSolvable ↥(barSub V₀ V hV L) := by
      intro hs
      have : Nontrivial ↥(barSub V₀ V hV L) :=
        (Subgroup.nontrivial_iff_ne_bot _).mpr hLb
      have : Group.IsPerfect ↥(barSub V₀ V hV L) := hqC.1
      exact Group.IsPerfect.not_isSolvable _ hs
    have hγ3 := three_le_gamma15_of_not_solvable D h1217 h151 hsolv
    by_cases hs2 : s15 D.M V₀ V hV L = 2
    · refine ⟨hs2, ?_⟩
      by_cases hV0 : V₀ = ⊥
      · subst hV0
        exact hδ rfl
      · have hV0W : V₀ ≤ wSub V₀ V hV L := by
          intro v hv0
          rw [wSub, mem_preTil_iff_of_mem V₀ V hV _ (h.hyp125.pairFacts.le hv0)]
          have hvmod : IntMod.mk hV ⟨v, h.hyp125.pairFacts.le hv0⟩ ∈ modNull V₀ V hV := by
            rw [mem_modNull]; exact hv0
          rw [show mkTil V₀ V hV (IntMod.mk hV ⟨v, h.hyp125.pairFacts.le hv0⟩) = 1 from
            (QuotientGroup.eq_one_iff (N := modNull V₀ V hV) _).2 hvmod]
          exact (wTil V₀ V hV L).one_mem
        have hδle : delta15 D.M V₀ V hV L ≤ 1 := by
          rw [delta15, v1Sub_of_ne_bot D.M V₀ V hV L hV0,
            inf_eq_left.mpr hV0W]
          exact h.small
        omega
    · exfalso
      have hs3 : 3 ≤ s15 D.M V₀ V hV L := by
        have hs := two_le_s15_of_p18_6_5 h h5 h151 hLb
        omega
      obtain ⟨x', hx'M, rfl⟩ := hX
      obtain ⟨y', hy'M, rfl⟩ := hY
      have hnotall : ¬ ∀ m ∈ D.M, conjSubgroup (wSub V₀ V hV L) m =
          conjSubgroup (wSub V₀ V hV L) x' ∨
          conjSubgroup (wSub V₀ V hV L) m = conjSubgroup (wSub V₀ V hV L) y' := by
        intro hall
        have hsub : wConj D.M V₀ V hV L ⊆
            ({conjSubgroup (wSub V₀ V hV L) x',
              conjSubgroup (wSub V₀ V hV L) y'} : Set (Subgroup G)) := by
          intro Z hZ
          obtain ⟨m, hmM, rfl⟩ := hZ
          rcases hall m hmM with h | h <;> simp [h]
        have hcard := ncard_wConj (D := D) h151 hV
        have hle : (wConj D.M V₀ V hV L).ncard ≤ 2 := by
          calc (wConj D.M V₀ V hV L).ncard ≤
              ({conjSubgroup (wSub V₀ V hV L) x',
                conjSubgroup (wSub V₀ V hV L) y'} : Set (Subgroup G)).ncard :=
                Set.ncard_le_ncard hsub
            _ ≤ 2 := by
                rw [Set.ncard_pair hXY]
        omega
      push Not at hnotall
      obtain ⟨z, hzM, hzx, hzy⟩ := hnotall
      have hXle : conjSubgroup (wSub V₀ V hV L) x' ≤
          Subgroup.centralizer (conjSubgroup L z : Set G) :=
        p18_cent_wSub_conj h h5 h151 hzM hx'M (by
          intro heq
          apply hzx
          rw [← s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs hzM),
            ← s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs hx'M), heq])
      have hYle : conjSubgroup (wSub V₀ V hV L) y' ≤
          Subgroup.centralizer (conjSubgroup L z : Set G) :=
        p18_cent_wSub_conj h h5 h151 hzM hy'M (by
          intro heq
          apply hzy
          rw [← s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs hzM),
            ← s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs hy'M), heq])
      have hV1le : v1Sub D.M V₀ V hV L ≤
          Subgroup.centralizer (conjSubgroup L z : Set G) :=
        p18_cent_v1Sub h h5 h151 hzM
      have hXYZle : conjSubgroup (wSub V₀ V hV L) x' ⊔
          conjSubgroup (wSub V₀ V hV L) y' ⊔ v1Sub D.M V₀ V hV L ≤
          Subgroup.centralizer (conjSubgroup L z : Set G) :=
        sup_le (sup_le hXle hYle) hV1le
      obtain ⟨v, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
      have hvXYZ : (v : G) ∈ conjSubgroup (wSub V₀ V hV L) x' ⊔
          conjSubgroup (wSub V₀ V hV L) y' ⊔ v1Sub D.M V₀ V hV L :=
        (Subgroup.mem_inf.1 v.2).1
      have hvC : (v : G) ∈ Subgroup.centralizer (conjSubgroup L z : Set G) := hXYZle hvXYZ
      have hu : g * (v : G) * g⁻¹ ∈ wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L :=
        (mem_conjSubgroup_iff).1 (Subgroup.mem_inf.1 v.2).2
      have hu1 : g * (v : G) * g⁻¹ ≠ 1 := by
        intro h1
        apply hv1
        apply Subtype.ext
        have : (v : G) = g⁻¹ * (g * (v : G) * g⁻¹) * g := by group
        rw [this, h1]; simp
      have huV : g * v * g⁻¹ ∈ V :=
        (sup_le (preTil_le V₀ V hV _) (s15_Infra_v1Sub_le h.hyp125 hV)) hu
      have hu2 : ∃ n : ℕ, (g * v * g⁻¹) ^ (2 ^ n) = 1 :=
        ⟨1, by simpa using hV.2 (g * v * g⁻¹) huV⟩
      have huUM : UniqueMax D.M (D.M ⊓ Subgroup.centralizer ({g * (v : G) * g⁻¹} : Set G)) := by
        refine uc22p22u_uniqueMax_mono D ?_ inf_le_left hULx
        refine le_inf hLxM ?_
        intro l hl
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp (hWVC hu) l hl
      have hcentu : Subgroup.centralizer ({g * (v : G) * g⁻¹} : Set G) ≤ D.M :=
        (centralizer_le_of_uniqueMax D.maxLocal hu1 hu2 huUM).1
      have hLzM : conjSubgroup L z ≤ D.M := by
        intro l hl
        rw [mem_conjSubgroup_iff] at hl
        have hl' : l = z⁻¹ * (z * l * z⁻¹) * z := by group
        rw [hl']
        exact D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hzM) (h.L_le_M hl)) hzM
      have hLzCv : conjSubgroup L z ≤ Subgroup.centralizer ({(v : G)} : Set G) := by
        intro l hl
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp hvC l hl
      have hLzConj : conjSubgroup L z ≤ conjSubgroup D.M g := by
        intro l hl
        have hlv : l * (v : G) = (v : G) * l :=
          (Subgroup.mem_centralizer_iff.mp (hLzCv hl) (v : G) (by simp)).symm
        have hglCu : g * l * g⁻¹ ∈ Subgroup.centralizer ({g * (v : G) * g⁻¹} : Set G) := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          calc (g * l * g⁻¹) * (g * (v : G) * g⁻¹) = g * (l * (v : G)) * g⁻¹ := by group
            _ = g * ((v : G) * l) * g⁻¹ := by rw [hlv]
            _ = (g * (v : G) * g⁻¹) * (g * l * g⁻¹) := by group
        exact (mem_conjSubgroup_iff).2 (hcentu hglCu)
      have hLzInt : conjSubgroup L z ≤ D.M ⊓ conjSubgroup D.M g :=
        le_inf hLzM hLzConj
      have hpL : p ∣ Nat.card ↥(conjSubgroup L z) := by
        rw [E3.card_conjSubgroup]
        exact h.hL.2.2
      exact h.p_not_dvd_card_inf hSg hgM (hpL.trans (Subgroup.card_dvd_of_le hLzInt))


theorem exists_involution_not_le_fixV {D : Data G} {V₀ V : Subgroup G} {p : ℕ}
    {L : Subgroup G} (h : Hyp18 D V₀ V p L) (h151 : Hyp151 D V₀ V L)
    (hLb : barSub V₀ V h.hyp125.isElemAbelian L ≠ ⊥) :
    ∃ t ∈ barSub V₀ V h.hyp125.isElemAbelian L, orderOf t = 2 ∧
      ¬ wTil V₀ V h.hyp125.isElemAbelian L ≤ fixV (Subgroup.zpowers t) := by
  classical
  have hV := h.hyp125.isElemAbelian
  let Lb : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV L
  have hcomp := barSub_mem_compBar_of_ne_bot h.hyp125 h.hL.1 hLb
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
      fun P hP hPn hP2 => s15_Kbar_eq_bot_of_normal_isPGroup D h.hyp125 hP hPn hP2
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

theorem r18_8At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) (hδ : Delta18_8At D V₀ V p L h) (hSg : UC6S846.SigmaStd D)
    (h1217 : R1217 D) (h127 : R127 D)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (h17_66_1 : S17.R17_66_1At D V₀ V) (h18_4 : R18_4At D V₀ V p L)
    (h15_13 : R15_13Small D) :
    R18_8At D V₀ V p L h := by
  intro h5
  have hV := h.hyp125.isElemAbelian
  have hUL : UniqueMax D.M L := by
    rcases h17_66_1 p h.hp L h.hL (UC22.conjClosure D.M L) rfl h.hX with hh | hh
    · exact hh
    · exact absurd hh h18_4
  have hV0card : Nat.card V₀ ≤ 2 :=
    (mSub_le_one_iff h.hyp125.pairFacts.elemAbelian₀).1 h.small
  have hLb : barSub V₀ V hV L ≠ ⊥ :=
    barSub_ne_bot_of_card_le_two D h127 h.hyp125 h.hL.1 hUL hV0card
  have h151 : Hyp151 D V₀ V L := hyp151_of_p18_6_5 h h5
  have h154 : Hyp154 D V₀ V L :=
    hyp154_of_p18_6_5 D hSg h1217 h h5 h151 hLb hUL
      (fun hV0 => hδ h5 h151 hUL hLb hV0)
  have h15 := h15_13 V₀ V L h154 (by have := h.small; omega) hLb
  have hγle : gamma15 D.M V₀ V hV L ≤ 3 := h15.1
  obtain ⟨t, htL, hto, -⟩ := exists_involution_not_le_fixV h h151 hLb
  have hmle := mBar_le_gamma15_of_R1217 D h1217 h151 hLb htL hto
  have hmgt : MBarGT D.M V₀ V 3 :=
    h1669 (by omega)
  have hgt : (3 : ℕ) < mBar D.M V₀ V hV :=
    (h.hyp125.mBarGT_iff_lt_mBar 3).1 hmgt
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
