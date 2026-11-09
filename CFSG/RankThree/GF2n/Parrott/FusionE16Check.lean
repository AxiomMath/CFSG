module

public import Mathlib.Data.Nat.Notation
public import CFSG.Permutation.FinPackWalk

public section

namespace CFSG.RankThree.GF2n.Parrott.FusionE16

@[expose] def vmul (v r0 r1 r2 r3 : ℕ) : ℕ :=
  (if v.testBit 0 then r0 else 0) ^^^ (if v.testBit 1 then r1 else 0) ^^^
  (if v.testBit 2 then r2 else 0) ^^^ (if v.testBit 3 then r3 else 0)

@[expose] def tab (r0 r1 r2 r3 : ℕ) : List ℕ := (List.range 16).map fun v => vmul v r0 r1 r2 r3

@[expose] def comp (t u : List ℕ) : List ℕ := (List.range 16).map fun v => t.getD (u.getD v 0) 0

@[expose] def idTab : List ℕ := List.range 16

@[expose] def A4tabs : List (List ℕ) :=
  [tab 1 4 6 8, tab 1 4 7 13, tab 1 2 4 8, tab 1 2 5 11, tab 1 6 2 8, tab 1 6 3 15, tab 1 5 6 15,
   tab 1 5 7 11, tab 1 3 4 13, tab 1 3 5 15, tab 1 7 2 11, tab 1 7 3 13]

@[expose] def pairs16 : List (List ℕ × List ℕ) :=
  [(tab 1 4 6 8, tab 1 5 6 15), (tab 1 2 4 8, tab 1 3 4 13), (tab 1 6 2 8, tab 1 7 2 11),
   (tab 1 4 7 13, tab 1 5 7 11), (tab 1 2 5 11, tab 1 3 5 15), (tab 1 6 3 15, tab 1 7 3 13),
   (tab 1 4 6 8, tab 1 5 7 11), (tab 1 4 7 13, tab 1 5 6 15), (tab 1 2 4 8, tab 1 3 5 15),
   (tab 1 2 5 11, tab 1 3 4 13), (tab 1 4 6 8, tab 1 2 4 8), (tab 1 4 6 8, tab 1 2 5 11),
   (tab 1 4 6 8, tab 1 6 2 8), (tab 1 4 6 8, tab 1 6 3 15), (tab 1 2 4 8, tab 1 6 2 8),
   (tab 1 2 4 8, tab 1 6 3 15)]

@[expose] def hasOrderFourProduct (M : List ℕ) : Bool :=
  pairs16.any fun bc =>
    let W := comp M (comp bc.1 (comp M bc.2))
    let W2 := comp W W
    W2 != idTab && comp W2 W2 == idTab

open CFSG.Permutation.FinPack

noncomputable def tcode (l : List ℕ) : ℕ := encF (fun i => l.getD i 0) 16

def Small (l : List ℕ) : Prop := ∀ i < 16, l.getD i 0 < 16

theorem getD_map_range16 (f : ℕ → ℕ) {i : ℕ} (hi : i < 16) :
    ((List.range 16).map f).getD i 0 = f i := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_range hi]

theorem rd_tcode {l : List ℕ} (hl : Small l) {j : ℕ} (hj : j < 16) : rd (tcode l) j = l.getD j 0 :=
  rd_encF hl hj

theorem comp_small {t u : List ℕ} (ht : Small t) (hu : Small u) : Small (comp t u) := fun i hi => by
  rw [comp, getD_map_range16 _ hi]
  exact ht _ (hu i hi)

theorem length_comp (t u : List ℕ) : (comp t u).length = 16 := by simp [comp]

theorem tcode_comp {t u : List ℕ} (ht : Small t) (hu : Small u) :
    tcode (comp t u) = mulK 16 (tcode t) (tcode u) := by
  rw [mulK]
  conv_lhs => rw [tcode]
  refine encF_congr fun i hi => ?_
  rw [comp, getD_map_range16 _ hi, rd_tcode hu hi, rd_tcode ht (hu i hi)]

theorem beq_tcode {t u : List ℕ} (hlt : t.length = 16) (hlu : u.length = 16) (ht : Small t)
    (hu : Small u) : (t == u) = Nat.beq (tcode t) (tcode u) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq]
  constructor
  · rintro rfl
    rfl
  · intro h
    refine List.ext_getElem (by rw [hlt, hlu]) fun i h1 h2 => ?_
    have hi : i < 16 := hlt ▸ h1
    have e := congrArg (fun c => rd c i) h
    simpa only [rd_tcode ht hi, rd_tcode hu hi, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2, Option.getD_some] using e

theorem vmul_lt {r0 r1 r2 r3 : ℕ} (h0 : r0 < 16) (h1 : r1 < 16) (h2 : r2 < 16) (h3 : r3 < 16)
    (v : ℕ) : vmul v r0 r1 r2 r3 < 16 := by
  have e : (16 : ℕ) = 2 ^ 4 := by norm_num
  have hz : (0 : ℕ) < 2 ^ 4 := by norm_num
  rw [e] at h0 h1 h2 h3 ⊢
  unfold vmul
  refine Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow ?_ ?_) ?_) ?_ <;>
    split <;> assumption

theorem tab_small {r0 r1 r2 r3 : ℕ} (h0 : r0 < 16) (h1 : r1 < 16) (h2 : r2 < 16) (h3 : r3 < 16) :
    Small (tab r0 r1 r2 r3) := fun i hi => by
  rw [tab, getD_map_range16 _ hi]
  exact vmul_lt h0 h1 h2 h3 i

theorem length_tab (r0 r1 r2 r3 : ℕ) : (tab r0 r1 r2 r3).length = 16 := by simp [tab]

theorem tcode_tab (r0 r1 r2 r3 : ℕ) :
    tcode (tab r0 r1 r2 r3) = encF (fun v => vmul v r0 r1 r2 r3) 16 :=
  encF_congr fun i hi => by rw [tab, getD_map_range16 _ hi]

theorem idTab_small : Small idTab := fun i hi => by
  rw [idTab, List.getD_eq_getElem?_getD, List.getElem?_range hi]
  exact hi

noncomputable def hasK (m : ℕ) : Bool :=
  (pairs16.map fun bc => (tcode bc.1, tcode bc.2)).any fun bc =>
    !Nat.beq (mulK 16 (mulK 16 m (mulK 16 bc.1 (mulK 16 m bc.2)))
        (mulK 16 m (mulK 16 bc.1 (mulK 16 m bc.2)))) (tcode idTab) &&
      Nat.beq (mulK 16 (mulK 16 (mulK 16 m (mulK 16 bc.1 (mulK 16 m bc.2)))
          (mulK 16 m (mulK 16 bc.1 (mulK 16 m bc.2))))
        (mulK 16 (mulK 16 m (mulK 16 bc.1 (mulK 16 m bc.2)))
          (mulK 16 m (mulK 16 bc.1 (mulK 16 m bc.2))))) (tcode idTab)

theorem any_congr_of_mem {α : Type*} {l : List α} {f g : α → Bool} (h : ∀ a ∈ l, f a = g a) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.any_cons, List.any_cons, h a List.mem_cons_self,
      ih fun b hb => h b (List.mem_cons_of_mem a hb)]

theorem pairs16_small : ∀ bc ∈ pairs16, Small bc.1 ∧ Small bc.2 := by
  intro bc hbc
  simp only [pairs16, List.mem_cons, List.not_mem_nil, or_false] at hbc
  rcases hbc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;>
    exact ⟨tab_small (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      tab_small (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩

theorem hasOrderFourProduct_eq_hasK {M : List ℕ} (hM : Small M) :
    hasOrderFourProduct M = hasK (tcode M) := by
  unfold hasOrderFourProduct hasK
  rw [List.any_map]
  refine any_congr_of_mem fun bc hbc => ?_
  obtain ⟨hb, hc⟩ := pairs16_small bc hbc
  have h1 := comp_small hM hc
  have h2 := comp_small hb h1
  have hW := comp_small hM h2
  have hW2 := comp_small hW hW
  simp only [Function.comp, bne, beq_tcode (length_comp _ _) (by simp [idTab]) hW2 idTab_small,
    beq_tcode (length_comp _ _) (by simp [idTab]) (comp_small hW2 hW2) idTab_small,
    tcode_comp hW hW, tcode_comp hW2 hW2, tcode_comp hM h2, tcode_comp hb h1, tcode_comp hM hc]

set_option maxRecDepth 100000 in
theorem hasOrderFourProduct_tab : ∀ a < 16, ∀ c < 16, ∀ d < 16,
    ((List.range 15).all fun k => vmul (k + 1) 2 a c d != 0) = true →
      hasOrderFourProduct (tab 2 a c d) = true := by
  have hw : allLtK (fun a => allLtK (fun c => allLtK (fun d =>
      !((List.range 15).all fun k => vmul (k + 1) 2 a c d != 0) ||
        hasK (encF (fun v => vmul v 2 a c d) 16)) 16) 16) 16 = true := by
    decide +kernel
  intro a ha c hc d hd hinv
  have h := allLtK_iff.1 (allLtK_iff.1 (allLtK_iff.1 hw a ha) c hc) d hd
  rw [hinv, Bool.not_true, Bool.false_or] at h
  rw [hasOrderFourProduct_eq_hasK (tab_small (by norm_num) ha hc hd), tcode_tab]
  exact h

end CFSG.RankThree.GF2n.Parrott.FusionE16
