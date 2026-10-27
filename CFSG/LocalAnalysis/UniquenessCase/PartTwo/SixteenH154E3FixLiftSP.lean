module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case2LnLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165Bar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154UThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_uniqueMax_of_fixed_three (D : Data G) (S : s16h_Std D) {V₀ V L : Subgroup G}
    (h : Setting16 D V₀ V L) (hsp : IsStronglyPEmbedded 3 D.M)
    (h3 : 3 ≤ CFSG.Open.pRank 3 D.M)
    (hv1 : v1Sub D.M V₀ V h.hyp151.isElemAbelian L ≤ wSub V₀ V h.hyp151.isElemAbelian L)
    (hfix : ∀ w : Vtil V₀ V h.hyp151.isElemAbelian,
      w ∈ wTil V₀ V h.hyp151.isElemAbelian L → w ≠ 1 →
      ∃ E : Subgroup (MulAut (Vtil V₀ V h.hyp151.isElemAbelian)),
        E ≤ Mbar D.M V₀ V h.hyp151.isElemAbelian ∧ IsElemAbelian 3 E ∧ 3 ^ 2 ≤ Nat.card ↥E ∧
          ∀ e ∈ E, e w = w) :
    ∀ w ∈ wSub V₀ V h.hyp151.isElemAbelian L ⊔ v1Sub D.M V₀ V h.hyp151.isElemAbelian L,
      w ≠ 1 → UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  have hV := h.hyp151.isElemAbelian
  haveI : Finite (MulAut (Vtil V₀ V hV)) := MulEquiv.finite_left
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
      h.hyp151.hyp125.pairFacts.le_normalizer₀
  intro w hw hw1
  have hwW : w ∈ wSub V₀ V hV L := by
    rw [sup_eq_left.2 hv1] at hw
    exact hw
  by_cases hw0 : w ∈ V₀
  · obtain ⟨E, hEM, hEea, hEcard⟩ :=
      c23_exists_elemAbelian_card_pow (p := 3) (M := D.M) (k := 3) Nat.prime_three
        (by rw [UC6.groupPRank_eq_pRank]; exact h3)
    have hMn : D.M ≤ normalizer (V₀ : Set G) := h.hyp16.hyp125.pairFacts.le_normalizer₀
    have hS : ((V₀ : Set G) \ {1}).ncard ≤ 3 := by
      have h4 : Nat.card V₀ ≤ 4 := s16c34_card_v0_le_four D h.hyp16
      have h5 : (V₀ : Set G).ncard = Nat.card V₀ := (Nat.card_coe_set_eq (V₀ : Set G)).symm
      have h6 : ((V₀ : Set G) \ {1}).ncard = (V₀ : Set G).ncard - 1 :=
        Set.ncard_diff_singleton_of_mem V₀.one_mem
      omega
    have hSw : ∀ e ∈ E, e * w * e⁻¹ ∈ (V₀ : Set G) \ {1} := by
      intro e he
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hMn (hEM he)) w).mp hw0, ?_⟩
      intro h1
      apply hw1
      have h2 : e * w * e⁻¹ = 1 := h1
      simpa using h2
    have hnc := c23_not_isCyclic_inf_centralizer Nat.prime_three (by norm_num) hEea hEcard hS hSw
    exact s16h_uniqueMax_of_noncyclic_three D S.h61 S.h63 hsp
      (IsElemAbelian.isPGroup (IsElemAbelian.mono hEea inf_le_left)) hnc
      (inf_le_inf_right _ hEM) inf_le_left
  · have hwV : w ∈ V := preTil_le V₀ V hV (wTil V₀ V hV L) hwW
    let wtil : Vtil V₀ V hV := mkTil V₀ V hV (IntMod.mk hV ⟨w, hwV⟩)
    have hwtil : wtil ∈ wTil V₀ V hV L :=
      (mem_preTil_iff_of_mem V₀ V hV (wTil V₀ V hV L) hwV).1 hwW
    have hwtil1 : wtil ≠ 1 := by
      intro h1
      apply hw0
      have h2 : (IntMod.mk hV ⟨w, hwV⟩ : IntMod V hV) ∈ modNull V₀ V hV :=
        (QuotientGroup.eq_one_iff (N := modNull V₀ V hV) _).1 h1
      exact (mem_modNull V₀ V hV _).1 h2
    obtain ⟨E, hEMbar, hEab, hEcard, hEfix⟩ := hfix wtil hwtil hwtil1
    have hEp : IsPGroup 3 E := hEab.isPGroup
    have hEnc : ¬ IsCyclic ↥E := s16c7_not_isCyclic_of_elemAbelian Nat.prime_three hEab hEcard
    let φ : ↥D.M →* MulAut (Vtil V₀ V hV) := barHom V₀ V hV hMs
    have hErange : E ≤ φ.range := by
      rw [range_barHom V₀ V hV hMs]
      exact hEMbar
    obtain ⟨B, hBp, hBc, hB⟩ :=
      exists_noncyclic_pGroup_map_le φ Nat.prime_three hErange hEp hEnc
    let P : Subgroup G := B.map D.M.subtype
    have hPp : IsPGroup 3 P := hBp.map D.M.subtype
    have hPc : ¬ IsCyclic ↥P := fun hc =>
      hBc ((Subgroup.equivMapOfInjective B D.M.subtype D.M.subtype_injective).isCyclic.2 hc)
    have hPle : P ≤ F11.CElt D.M V₀ w := by
      rw [Subgroup.map_le_iff_le_comap]
      intro b hb
      rw [Subgroup.mem_comap]
      have hbfix : φ b wtil = wtil := hEfix (φ b) (hB b hb)
      have hcomm : (b : G) * w * (b : G)⁻¹ * w⁻¹ ∈ V₀ :=
        (barHom_fix_iff V₀ V hV hMs b (IntMod.mk hV ⟨w, hwV⟩)).1 hbfix
      exact ⟨b.2, (stabTil_le_normalizer₀ V₀ V) (hMs b.2), hcomm⟩
    exact s16h_uniqueMax_cent_of_cElt_three D S.h61 S.h63 S.h127 hsp h.hyp16 hPp hPc hwV hw0 hPle

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
