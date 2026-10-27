module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4CBA3AAA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenCore
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JP

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_sl4_cba3_three_fixes_v1
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
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    (hZ0 : wSub ⊥ V h.hyp151.isElemAbelian L ⊓
        conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L) x =
      wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G)) :
    ∃ E : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)),
      E ≤ Mbar D.M ⊥ V h.hyp151.isElemAbelian ∧ IsElemAbelian 3 E ∧
        9 ≤ Nat.card ↥E ∧
        ∀ e ∈ E, ∀ q ∈ imgTil ⊥ V h.hyp151.isElemAbelian
          (v1Sub D.M ⊥ V h.hyp151.isElemAbelian L), e q = q := by
  have hV := h.hyp151.isElemAbelian
  obtain ⟨E, hEsub, hEab, hEcard⟩ :=
    s16h_sl4_cba3_E9_le_two_components h hrow hxM hxn
  let H : Subgroup (MulAut (Vtil ⊥ V hV)) :=
    { carrier := {e | ∀ q ∈ imgTil ⊥ V hV (v1Sub D.M ⊥ V hV L), e q = q}
      one_mem' := fun _ _ => rfl
      mul_mem' := fun ha hb q hq => by rw [MulAut.mul_apply, hb q hq, ha q hq]
      inv_mem' := fun {a} ha q hq => by
        calc a⁻¹ q = a⁻¹ (a q) := by rw [ha q hq]
          _ = q := by simp }
  have hlbarH : lBar ⊥ V hV L ≤ H := by
    intro e he q hq
    have h1 := s15_Core_imgTil_v1Sub_le_fixV (D := D) (V₀ := ⊥) (V := V) (L := L) h.hyp151
      (m := (1 : G)) D.M.one_mem
    rw [conjSubgroup_one] at h1
    exact mem_fixV.1 (h1 hq) e he
  have hxH : barSub ⊥ V hV (conjSubgroup L x) ≤ H := by
    intro e he q hq
    have h1 := s15_Core_imgTil_v1Sub_le_fixV (D := D) (V₀ := ⊥) (V := V) (L := L) h.hyp151
      (m := x) hxM
    exact mem_fixV.1 (h1 hq) e he
  have hEH : E ≤ H := hEsub.trans (sup_le hlbarH hxH)
  refine ⟨E, ?_, hEab, hEcard, fun e he => hEH he⟩
  refine hEsub.trans (sup_le ?_ ?_)
  · exact barSub_mono ⊥ V hV h.hyp151.le
  · refine barSub_mono ⊥ V hV ?_
    intro y hy
    have hxy : x * y * x⁻¹ ∈ L := (mem_conjSubgroup_iff).1 hy
    have hmem : x⁻¹ * (x * y * x⁻¹) * x ∈ D.M :=
      D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hxM) (h.hyp151.le hxy)) hxM
    rwa [show x⁻¹ * (x * y * x⁻¹) * x = y by group] at hmem

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
