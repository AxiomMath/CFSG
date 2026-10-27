module

public import CFSG.Quasithin.H13.GoldschmidtU43ModBase
public import CFSG.Quasithin.H13.GoldschmidtU43ModRel
public import CFSG.Quasithin.H13.GoldschmidtU43ModSimple

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.KGroups.U43 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.LieType.Multipliers.U43

theorem rels5_lt5 : ∀ r ∈ rels5Codes, ∀ l ∈ r, l.1 < 5 := by
  rw [rels5Codes_eq]
  decide

theorem evalG_mem {K : Type*} [Group K] (H : Subgroup K) (g : ℕ → K) {m : ℕ}
    (hg : ∀ i < m, g i ∈ H) : ∀ w : List (ℕ × Bool), (∀ l ∈ w, l.1 < m) → evalG g w ∈ H
  | [], _ => by simp [evalG]
  | l :: w, hw => by
    have h1 : letterVal g l ∈ H := by
      by_cases hb : l.2 = true
      · simpa [letterVal, hb] using hg l.1 (hw l List.mem_cons_self)
      · simpa [letterVal, hb] using H.inv_mem (hg l.1 (hw l List.mem_cons_self))
    have h2 := evalG_mem H g hg w (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
    simpa [evalG] using H.mul_mem h1 h2


theorem u43Model_of_checks (hm : modelCheck 820 tabA tabB rels5Codes = true) : U43Model := by
  unfold modelCheck at hm
  simp only [Bool.and_eq_true] at hm
  obtain ⟨⟨⟨⟨h1, hM⟩, hr⟩, hA⟩, hB⟩ := hm
  have hrep := rep_gensWith h1 (rep_phiArr h1)
  have hrepi := rep_invs psi hrep hM (by simp [gensWith])
  have hrid : Rep 820 (idA 820) (psi (1 : X₀)) := by rw [map_one]; exact rep_idA
  have hJ : JW20 mdA mdS mdU mdV mdPhi := JW20.of_eval_rels fun r hrm =>
    psi_inj ((eqA_iff (rep_evalArr psi hrep hrepi r (rels5_lt5 r hrm)) hrid).1
      (List.all_eq_true.1 hr r hrm))
  have ha : evalG (gen5 mdA mdS mdU mdV mdPhi) [(0, false), (0, false)] = xElt :=
    psi_inj ((eqA_iff (rep_evalArr psi hrep hrepi _ (by decide)) rep_tabA).1 hA)
  have hb : evalG (gen5 mdA mdS mdU mdV mdPhi) surjB = yElt :=
    psi_inj ((eqA_iff (rep_evalArr psi hrep hrepi _ (by decide)) rep_tabB).1 hB)
  refine ⟨mdA, mdS, mdU, mdV, mdPhi, hJ, ?_⟩
  have hgm : ∀ i < 5, gen5 mdA mdS mdU mdV mdPhi i ∈
      Subgroup.closure ({mdA, mdS, mdU, mdV, mdPhi} : Set X₀) := by
    intro i hi
    refine Subgroup.subset_closure ?_
    interval_cases i <;> simp [gen5]
  rw [eq_top_iff, ← closure_xy, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · rw [← ha]
    exact evalG_mem _ _ hgm _ (by decide)
  · rw [← hb]
    exact evalG_mem _ _ hgm _ (by decide)

end CFSG.Quasithin.H13.U43
