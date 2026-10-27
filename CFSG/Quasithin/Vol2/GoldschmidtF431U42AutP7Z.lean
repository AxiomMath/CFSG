module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7A

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

@[expose] def ZCl : List PL :=
  ((List.range 43).filter fun k => invTgt.getD k 0 == 0 || invTgt.getD k 0 == 3).map invL

@[expose] def Th2 : List PL := Al2.filter fun l => l != idL && !ZCl.contains l

theorem ZCl_check : ZCl.length = 17 ∧ ZCl.Nodup ∧
    ∀ l ∈ ZCl, comp l l = idL ∧ l ≠ idL ∧ l ∈ Thl := by
  decide +kernel

theorem invL_inj : ∀ k < 43, ∀ k' < 43, invL k = invL k' → k = k' := by decide +kernel

theorem mem_ZCl_iff {l : PL} :
    l ∈ ZCl ↔ ∃ k < 43, (invTgt.getD k 0 = 0 ∨ invTgt.getD k 0 = 3) ∧ invL k = l := by
  unfold ZCl
  simp only [List.mem_map, List.mem_filter, List.mem_range, Bool.or_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨k, ⟨hk, h⟩, rfl⟩
    exact ⟨k, hk, h, rfl⟩
  · rintro ⟨k, hk, h, rfl⟩
    exact ⟨k, ⟨hk, h⟩, rfl⟩

theorem cnt_check : (Al1.filter fun l => ZCl.contains l).length = 5 ∧
    (Al2.filter fun l => ZCl.contains l).length = 9 ∧
    (Vl.filter fun l => ZCl.contains l).length = 5 ∧ Th2.length = 6 := by
  decide +kernel

theorem span_check :
    (∀ a ∈ Al1, ∃ p ∈ idL :: Al1.filter (fun l => ZCl.contains l),
      ∃ q ∈ idL :: Al1.filter (fun l => ZCl.contains l), comp p q = a) ∧
    (∀ a ∈ Al2, ∃ p ∈ idL :: Al2.filter (fun l => ZCl.contains l),
      ∃ q ∈ idL :: Al2.filter (fun l => ZCl.contains l), comp p q = a) ∧
    (∀ a ∈ Al2, ∃ p ∈ idL :: Th2, ∃ q ∈ idL :: Th2, comp p q = a) := by
  decide +kernel

end CFSG.Quasithin.H13.F431.U42Aut
