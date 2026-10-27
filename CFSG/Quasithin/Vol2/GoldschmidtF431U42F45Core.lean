module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42F45Act
public import Certificates.Data.U42F45Check

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin U42F431

@[expose] def repY (w : List ℕ) : Y := ⟨wordP w, wordP_mem w⟩

theorem repL_repY (w : List ℕ) : RepL (evalW w) ((repY w : Y) : P45) := repL_wordP w

theorem repL_repY_inv (w : List ℕ) : RepL (evalW (invW w)) (((repY w)⁻¹ : Y) : P45) := by
  have : (((repY w)⁻¹ : Y) : P45) = wordP (invW w) := by
    rw [wordP_invW]
    rfl
  rw [this]
  exact repL_wordP _

theorem core_iff {ws : List (List ℕ)} {i : ℕ} {q : Y} (hi : i < 64)
    (hq : RepL (Tl.getD i []) (q : P45)) :
    (∀ w ∈ ws, (repY w)⁻¹ * q * repY w ∈ T) ↔ i ∈ coreIdx ws := by
  rw [coreIdx, List.mem_filter, List.mem_range]
  simp only [List.all_eq_true, hi, true_and]
  refine forall_congr' fun w => forall_congr' fun _ => ?_
  have hr : RepL (comp (comp (evalW (invW w)) (Tl.getD i [])) (evalW w))
      ((((repY w)⁻¹ * q * repY w : Y)) : P45) :=
    repL_mul (repL_mul (repL_repY_inv w) hq) (repL_repY w)
  rw [List.contains_iff_mem, mem_T_iff]
  constructor
  · rintro ⟨j, hj, hjr⟩
    rw [← repL_unique hjr hr, List.mem_iff_getElem]
    exact ⟨j, by have := chkT_spec.1; omega, by rw [List.getElem_eq_getD ([] : PL)]⟩
  · intro hmem
    obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.1 hmem
    have hj64 : j < 64 := by have := chkT_spec.1; omega
    refine ⟨j, hj64, ?_⟩
    rw [List.getD_eq_getElem _ _ hj, hjeq]
    exact hr

theorem repY_image_lnS {w : List ℕ} {a b : ℕ} (ha : a < 27)
    (hs : sameSet (imgSet (evalW w) (lnTab.getD a [])) (lnTab.getD b []) = true) :
    ((repY w : Y) : P45) '' lnS a = lnS b := by
  show (wordP w) '' lnS a = lnS b
  rw [lnS, image_lineSet (repL_wordP w) (lnTab_lt ha), lineSet_eq_of_sameSet hs]
  rfl

theorem lnImg_repY {w : List ℕ} {a b : Fin 27}
    (hs : sameSet (imgSet (evalW w) (lnTab.getD a [])) (lnTab.getD b []) = true) :
    repY w • a = b :=
  lnImg_eq_iff.2 (repY_image_lnS a.2 hs)

theorem eq_one_of_repL_zero {q : Y}
    (hq : RepL (Tl.getD 0 []) (q : P45)) : q = 1 := by
  have h0 : Tl.getD 0 [] = idL := chkT_spec.2.2.2.1
  rw [h0] at hq
  exact Subtype.ext (eq_of_repL hq (repL_one 45))

end CFSG.Quasithin.H13.F431.U42
