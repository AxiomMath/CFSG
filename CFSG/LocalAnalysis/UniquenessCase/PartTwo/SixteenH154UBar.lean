module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154TenG
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeY2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34UniqueP

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]


private theorem s16h_ubar_subgroupOf_commutator_self {X : Type*} [Group X] (H : Subgroup X) :
    (⁅H, H⁆).subgroupOf H = ⁅(⊤ : Subgroup ↥H), ⊤⁆ := by
  ext x
  rw [Subgroup.mem_subgroupOf, ← Subgroup.map_subtype_commutator H, ← _root_.commutator_def,
    Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hyx' : y = x := Subtype.ext hyx
    rwa [hyx'] at hy
  · intro hx
    exact ⟨x, hx, rfl⟩

private theorem s16h_ubar_openPRank_map_mulEquiv {X Y : Type*} [Group X] [Group Y]
    [Finite X] [Finite Y] (e : X ≃* Y) (p : ℕ) (H : Subgroup X) :
    CFSG.Open.pRank p (H.map e.toMonoidHom) = CFSG.Open.pRank p H := by
  have h1 := CFSG.pRank_congr_of_mulEquiv
    (Subgroup.equivMapOfInjective H e.toMonoidHom e.injective) p
  simp only [CFSG.SectionRank.pRank_coe_eq_openPRank] at h1
  exact h1.symm

private theorem s16h_ubar_openPRank_subgroupOf_eq {X : Type*} [Group X] [Finite X] {p : ℕ}
    {H K : Subgroup X} (h : H ≤ K) :
    CFSG.Open.pRank p (H.subgroupOf K) = CFSG.Open.pRank p H := by
  have h1 := CFSG.pRank_congr_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h) p
  simp only [CFSG.SectionRank.pRank_coe_eq_openPRank] at h1
  exact h1

theorem s16h_uniqueMax_cent_of_bar_pRank (D : Data G) (hSig : UC6S846.SigmaStd D)
    (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D) (h77 : F07.R77Eq D) (h869 : F08.R869 D)
    (h111 : F11.R111 D) (h112 : F11.R112 D) (hThin : ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) (h127 : R127 D)
    (hσ : D.sig = D.sig1) {V₀ V : Subgroup G} (h : Hyp16 D V₀ V) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {X : Subgroup (MulAut (Vtil V₀ V h.hyp125.isElemAbelian))}
    (hXM : X ≤ Mbar D.M V₀ V h.hyp125.isElemAbelian)
    (hXn : ∀ q ∈ Mbar D.M V₀ V h.hyp125.isElemAbelian, ∀ x ∈ X, q * x * q⁻¹ ∈ X)
    (hXe : IsElemAbelian p X)
    (hXd : X ≤ ⁅Mbar D.M V₀ V h.hyp125.isElemAbelian, Mbar D.M V₀ V h.hyp125.isElemAbelian⁆)
    {v : G} (hvV : v ∈ V) (hvV₀ : v ∉ V₀)
    (hrank : 1 < CFSG.Open.pRank p
      (X ⊓ barSub V₀ V h.hyp125.isElemAbelian (F11.CElt D.M V₀ v))) :
    UniqueMax D.M (D.M ⊓ centralizer ({v} : Set G)) := by
  let hV := h.hyp125.isElemAbelian
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  haveI hCTilde : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal :=
    s15_Three_cTilde_normal hV hMs
  obtain ⟨e, he⟩ := s15_Three_barImage_equiv hV hMs
  set Xbar : Subgroup (F11.MBar11 D.M V₀ V) :=
    (X.subgroupOf (Mbar D.M V₀ V hV)).map e.symm.toMonoidHom with hXbar
  have hNnorm : (X.subgroupOf (Mbar D.M V₀ V hV)).Normal := by
    refine ⟨fun x hx q => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
      hXn (q : MulAut (Vtil V₀ V hV)) q.2 (x : MulAut (Vtil V₀ V hV)) hx
  have hXnorm : Xbar.Normal := by
    rw [hXbar]
    exact hNnorm.map e.symm.toMonoidHom e.symm.surjective
  haveI : Xbar.Normal := hXnorm
  have hXab : IsElemAbelian p Xbar := by
    rw [hXbar]
    exact (hXe.subgroupOf (Mbar D.M V₀ V hV)).map e.symm.toMonoidHom
  have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom =
      MonoidHom.id (↥(Mbar D.M V₀ V hV)) := by
    ext x
    simp
  have hXmap : Xbar.map e.toMonoidHom = X.subgroupOf (Mbar D.M V₀ V hV) := by
    rw [hXbar, Subgroup.map_map, hcomp, Subgroup.map_id]
  have hcomm_le : X.subgroupOf (Mbar D.M V₀ V hV) ≤
      (⁅Mbar D.M V₀ V hV, Mbar D.M V₀ V hV⁆).subgroupOf (Mbar D.M V₀ V hV) :=
    fun x hx => hXd (Subgroup.mem_subgroupOf.1 hx)
  have hcommmap : ((⁅Mbar D.M V₀ V hV, Mbar D.M V₀ V hV⁆).subgroupOf
        (Mbar D.M V₀ V hV)).map e.symm.toMonoidHom =
      ⁅(⊤ : Subgroup (F11.MBar11 D.M V₀ V)), ⊤⁆ := by
    rw [s16h_ubar_subgroupOf_commutator_self, Subgroup.map_commutator, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr e.symm.surjective]
  have hXc : Xbar ≤ ⁅(⊤ : Subgroup (F11.MBar11 D.M V₀ V)), ⊤⁆ := by
    rw [hXbar]
    exact le_trans (Subgroup.map_mono hcomm_le) (le_of_eq hcommmap)
  have hleC : F11.CElt D.M V₀ v ≤ D.M := fun x hx => hx.1
  have hmapC : (F11.barImage11 D.M V₀ V (F11.CElt D.M V₀ v)).map e.toMonoidHom =
      (barSub V₀ V hV (F11.CElt D.M V₀ v)).subgroupOf (Mbar D.M V₀ V hV) :=
    he (F11.CElt D.M V₀ v) hleC
  have hAmap : (Xbar ⊓ F11.barImage11 D.M V₀ V (F11.CElt D.M V₀ v)).map e.toMonoidHom =
      (X.subgroupOf (Mbar D.M V₀ V hV)) ⊓
        (barSub V₀ V hV (F11.CElt D.M V₀ v)).subgroupOf (Mbar D.M V₀ V hV) := by
    rw [Subgroup.map_inf _ _ e.toMonoidHom e.injective, hXmap, hmapC]
  have hsub : (X.subgroupOf (Mbar D.M V₀ V hV)) ⊓
        (barSub V₀ V hV (F11.CElt D.M V₀ v)).subgroupOf (Mbar D.M V₀ V hV) =
      (X ⊓ barSub V₀ V hV (F11.CElt D.M V₀ v)).subgroupOf (Mbar D.M V₀ V hV) := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
  have hpA : CFSG.Open.pRank p (Xbar ⊓
        F11.barImage11 D.M V₀ V (F11.CElt D.M V₀ v)) =
      CFSG.Open.pRank p (X ⊓ barSub V₀ V hV (F11.CElt D.M V₀ v)) := by
    calc CFSG.Open.pRank p (Xbar ⊓ F11.barImage11 D.M V₀ V (F11.CElt D.M V₀ v))
        = CFSG.Open.pRank p ((Xbar ⊓
            F11.barImage11 D.M V₀ V (F11.CElt D.M V₀ v)).map e.toMonoidHom) :=
          (s16h_ubar_openPRank_map_mulEquiv e p _).symm
      _ = CFSG.Open.pRank p ((X.subgroupOf (Mbar D.M V₀ V hV)) ⊓
            (barSub V₀ V hV (F11.CElt D.M V₀ v)).subgroupOf (Mbar D.M V₀ V hV)) := by
            rw [hAmap]
      _ = CFSG.Open.pRank p ((X ⊓
            barSub V₀ V hV (F11.CElt D.M V₀ v)).subgroupOf (Mbar D.M V₀ V hV)) := by
            rw [hsub]
      _ = CFSG.Open.pRank p (X ⊓ barSub V₀ V hV (F11.CElt D.M V₀ v)) :=
          s16h_ubar_openPRank_subgroupOf_eq (p := p) (fun x hx => hXM hx.1)
  have hrank' : 1 < CFSG.Open.pRank p (Xbar ⊓
      F11.barImage11 D.M V₀ V (F11.CElt D.M V₀ v)) := hpA.symm ▸ hrank
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q⟩ : Nonempty (Sylow p ↥(F11.O2p p D.M)) := inferInstance
  have hP : CFSG.ABGLocalTools.IsSylowOf p
      ((Q : Subgroup ↥(F11.O2p p D.M)).map (F11.O2p p D.M).subtype) (F11.O2p p D.M) :=
    ⟨Q, rfl⟩
  exact s16h_uniqueMax_cent_of_pRank D hSig h61 h63 h77 h869 h111 h112 hThin hCyc
    (Hyp125.hyp11 h127 h.hyp125) (s16c34_card_v0_le_four D h) hσ hp hp2 hP hXab hXc hvV
    hvV₀ hrank'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
