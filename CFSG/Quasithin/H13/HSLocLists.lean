module

public import CFSG.Quasithin.H13.LocDblDcos
public import Certificates.Data.DcHS

public section

namespace CFSG.Quasithin.H13.LocDbl.HSLoc

open CFSG.QuasithinUnique.K1.SporadicPerm hiding img keyNat
open CFSG.Quasithin.H13.LocDbl.DcNative CFSG.Quasithin.H13.LocDbl.DcRank CFSG.Quasithin.H13.LocDbl.Dc

theorem pwDistinct_iff (l : List (Array ℕ)) : pwDistinct l = true ↔ l.Nodup := by
  induction l with
  | nil => simp [pwDistinct]
  | cons x l ih =>
    simp only [pwDistinct, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq, ih,
      List.nodup_cons]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun hx => h1 x hx rfl, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun y hy hxy => h1 (hxy ▸ hy), h2⟩

theorem mem_of_maskOf_eq {l l' : List ℕ} (h : maskOf l = maskOf l') {x : ℕ} (hx : x < 100) :
    x ∈ l ↔ x ∈ l' := by
  have := congrArg (fun m => m[x]?) h
  simp only [maskOf, List.getElem?_map, List.getElem?_range, hx, if_true, Option.map_some,
    Option.some.injEq] at this
  rw [← List.contains_iff_mem, ← List.contains_iff_mem, this]

theorem maskOf_eq_of_mem_iff {l l' : List ℕ} (h : ∀ x < 100, x ∈ l ↔ x ∈ l') :
    maskOf l = maskOf l' := by
  unfold maskOf
  apply List.map_congr_left
  intro x hx
  have := h x (List.mem_range.mp hx)
  exact Bool.eq_iff_iff.mpr (List.contains_iff_mem.trans (this.trans List.contains_iff_mem.symm))

end CFSG.Quasithin.H13.LocDbl.HSLoc
