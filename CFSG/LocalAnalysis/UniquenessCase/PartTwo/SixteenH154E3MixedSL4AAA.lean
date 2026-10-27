module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4AAAA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_sl4_scalar_element
    (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    (hJP : K_JonesParshallH1) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M ⊥ V h.hyp151.isElemAbelian) t (lBar ⊥ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar ⊥ V h.hyp151.isElemAbelian L) ≤ 1)
    (hZ : commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L) ≠ ⊥)
    (hbad : ∀ q ∈ D.sig, ∀ E : Subgroup G, E ≤ D.M → IsElemAbelian q E →
      Nat.card ↥(E ⊓ preBarSub D.M ⊥ V h.hyp151.isElemAbelian
        (centSub (wTil ⊥ V h.hyp151.isElemAbelian L))) < q ^ 2)
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 2)
    (hZ4 : 2 < Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)))
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L) :
    ∃ d : G, d ∈ D.M ∧ orderOf d = 3 ∧
      (∀ w ∈ wSub ⊥ V h.hyp151.isElemAbelian L,
        d * w * d⁻¹ ∈ wSub ⊥ V h.hyp151.isElemAbelian L) ∧
      (∀ w ∈ conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L) x,
        d * w * d⁻¹ ∈ conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L) x) ∧
      (∀ z ∈ wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G),
        d * z * d⁻¹ ∈ wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G)) ∧
      (∃ z ∈ wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G),
        d * z * d⁻¹ ≠ z) := by
  obtain ⟨d, hdM, hd3, hWn, hWxn, hZn, hfpf⟩ :=
    s16h_sl4_scalar_data D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin hZ hbad hrow
      hZ4 hxM hxn
  refine ⟨d, hdM, hd3, hWn, hWxn, hZn, ?_⟩
  have hV := h.hyp151.isElemAbelian
  have hZeq : wSub ⊥ V hV L ⊓ Subgroup.centralizer (L : Set G) =
      preTil ⊥ V hV (commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (lBar ⊥ V hV L)) :=
    s16h_wSub_inf_centralizer_eq_preTil D h
  obtain ⟨q, hq1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hZ
  obtain ⟨x, hx⟩ := mkTil_surjective ⊥ V hV (q : Vtil ⊥ V hV)
  have hxmem : x.val ∈ wSub ⊥ V hV L ⊓ Subgroup.centralizer (L : Set G) := by
    rw [hZeq]
    exact (mem_preTil ⊥ V hV _).2 ⟨x, rfl, by rw [hx]; exact q.2⟩
  refine ⟨x.val, hxmem, fun hfix => hq1 ?_⟩
  have hx1 : x.val = 1 := hfpf x.val hxmem hfix
  have hx1' : x = 1 := IntMod.val_injective (by rw [IntMod.val_one]; exact hx1)
  refine Subtype.ext ?_
  rw [← hx, hx1', map_one]
  rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
