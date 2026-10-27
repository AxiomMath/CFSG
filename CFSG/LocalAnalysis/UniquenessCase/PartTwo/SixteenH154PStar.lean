module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD3Five

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem s16h_pstar_subgroupOf_commutator_self {X : Type*} [Group X] (H : Subgroup X) :
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

theorem s16h_exists_xbar_of_bar {D : Data G} {V₀ V : Subgroup G} (h : Hyp16 D V₀ V) {p n : ℕ}
    {X : Subgroup (MulAut (Vtil V₀ V h.hyp125.isElemAbelian))}
    (hXn : ∀ q ∈ Mbar D.M V₀ V h.hyp125.isElemAbelian, ∀ x ∈ X, q * x * q⁻¹ ∈ X)
    (hXe : IsElemAbelian p X)
    (hXd : X ≤ ⁅Mbar D.M V₀ V h.hyp125.isElemAbelian, Mbar D.M V₀ V h.hyp125.isElemAbelian⁆)
    (hcard : Nat.card ↥X = p ^ n) [((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal] :
    ∃ Xbar : Subgroup (F11.MBar11 D.M V₀ V), Xbar.Normal ∧ IsElemAbelian p Xbar ∧
      Nat.card Xbar = p ^ n ∧ Xbar ≤ ⁅(⊤ : Subgroup (F11.MBar11 D.M V₀ V)), ⊤⁆ := by
  let hV := h.hyp125.isElemAbelian
  have hXM : X ≤ Mbar D.M V₀ V hV := hXd.trans (Subgroup.commutator_le_self _)
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  obtain ⟨e, -⟩ := s15_Three_barImage_equiv hV hMs
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
  have hXab : IsElemAbelian p Xbar := by
    rw [hXbar]
    exact (hXe.subgroupOf (Mbar D.M V₀ V hV)).map e.symm.toMonoidHom
  have hcardX : Nat.card ↥Xbar = p ^ n := by
    rw [hXbar, Subgroup.card_map_of_injective e.symm.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv, hcard]
  have hcomm_le : X.subgroupOf (Mbar D.M V₀ V hV) ≤
      (⁅Mbar D.M V₀ V hV, Mbar D.M V₀ V hV⁆).subgroupOf (Mbar D.M V₀ V hV) :=
    fun x hx => hXd (Subgroup.mem_subgroupOf.1 hx)
  have hcommmap : ((⁅Mbar D.M V₀ V hV, Mbar D.M V₀ V hV⁆).subgroupOf
        (Mbar D.M V₀ V hV)).map e.symm.toMonoidHom =
      ⁅(⊤ : Subgroup (F11.MBar11 D.M V₀ V)), ⊤⁆ := by
    rw [s16h_pstar_subgroupOf_commutator_self, Subgroup.map_commutator, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr e.symm.surjective]
  refine ⟨Xbar, hXnorm, hXab, hcardX, ?_⟩
  rw [hXbar]
  exact le_trans (Subgroup.map_mono hcomm_le) (le_of_eq hcommmap)

theorem s16h_not_mBarGT_of_bar (D : Data G) (hSig : UC6S846.SigmaStd D) (h61 : UC6.R6_1 D)
    (h63 : UC6.R6_3 D) (h77 : F07.R77Eq D) (h869 : F08.R869 D) (h111 : F11.R111 D)
    (h112 : F11.R112 D) (hThin : ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) (h127 : R127 D)
    (h126 : R126 D) (h1211 : R1211_1 D) (h111W : W3Thm111 G) (h6161ii : W3Lem616_1ii G)
    (hσ : D.sig = D.sig1) {V₀ V : Subgroup G} (h : Hyp16 D V₀ V) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {X : Subgroup (MulAut (Vtil V₀ V h.hyp125.isElemAbelian))}
    (hXn : ∀ q ∈ Mbar D.M V₀ V h.hyp125.isElemAbelian, ∀ x ∈ X, q * x * q⁻¹ ∈ X)
    (hXe : IsElemAbelian p X)
    (hXd : X ≤ ⁅Mbar D.M V₀ V h.hyp125.isElemAbelian, Mbar D.M V₀ V h.hyp125.isElemAbelian⁆)
    {n : ℕ} (hn : 1 < n) (hn2 : V₀ = ⊥ → 2 < n) (hcard : Nat.card ↥X = p ^ n) :
    ¬ MBarGT D.M V₀ V (D.k + 1) := by
  intro hm
  have hV := h.hyp125.isElemAbelian
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  haveI : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal := s15_Three_cTilde_normal hV hMs
  obtain ⟨Xbar, hXn', hXe', hXc', hXd'⟩ := s16h_exists_xbar_of_bar h hXn hXe hXd hcard
  have hH11 : F11.Hyp11 D V₀ V := Hyp125.hyp11 h127 h.hyp125
  have h1110 : R1110Core D := r1110Core_holds D hSig h61 h63 h77 h869 h111 h112 hThin hCyc
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf p (F11.O2p p D.M)
  refine twelve_twelve D h63 h126 h1211 h111W h6161ii h.hyp125 hm
    (F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar)) ?_
  by_cases hV0 : V₀ = ⊥
  · exact s16e_d3_inPStar D hSig hσ h1110 h77 hH11 hp hp2 (hn2 hV0) Xbar hXn' hXe' hXc' hXd' hP
  · exact (inPStar_iff_of_ne_bot hV0 _).2
      (s16e_d3_inP11 D hSig hσ h1110 h77 hH11 hp hp2 hn Xbar hXn' hXe' hXc' hXd' hP)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
