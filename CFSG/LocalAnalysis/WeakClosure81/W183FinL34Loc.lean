module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinL34Pack
public import CFSG.Open.LocalVocabulary
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions

public section

namespace CFSG.LocalAnalysis.WeakClosure81.W183L34

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.Open

@[expose] def r1W : List ℕ := [0, 0, 1, 0]

@[expose] def z0W : List (List ℕ) := [[], [0, 0, 1, 0], [0, 0, 2, 0], [0, 0, 1, 2, 0]]

@[expose] def c1N : List Nat := c1W.map wN

@[expose] def r1N : Nat := wN r1W

@[expose] def z0N : List Nat := z0W.map wN

@[expose] def commN (p q : Nat) : Bool := eqN (compN p q) (compN q p)

@[expose] def normE4 (y : Nat) : Bool :=
  !eqN y idN && !eqN y r1N && eqN (compN y y) idN && commN y r1N &&
    c1N.all (fun u => [idN, r1N, y, compN r1N y].any (fun a => eqN (compN u y) (compN a u)))

theorem c1W_length : c1W.length = 64 := by decide +kernel

theorem c1_comm_r1 : c1W.all (fun w => commN (wN w) r1N) = true := by decide +kernel

theorem c1_distinct : c1N.Pairwise (fun a b => eqN a b = false) := by decide +kernel

theorem normE4_z0 : (c1N.filter normE4).all (fun y => z0N.any (eqN y)) = true := by decide +kernel

theorem z0_mul : z0N.all (fun a => z0N.all fun b => z0N.any (eqN (compN a b))) = true := by
  decide +kernel

theorem z0_inv : z0N.all (fun a => eqN (compN a a) idN) = true := by decide +kernel

theorem r1_sq_N : eqN (compN r1N r1N) idN = true := by decide +kernel

theorem r1_ne_N : eqN r1N idN = false := by decide +kernel

theorem r1_eq : r₁ = wordPerm r1W := by
  simp [wordPerm, r1W, r₁, genS, pow_two, mul_assoc]

private theorem w183finL34_repN_r1 : RepN r1N r₁ := by
  rw [r1_eq]
  exact repN_wN r1W

theorem r1_sq : r₁ * r₁ = 1 :=
  (RepN.eq_iff (w183finL34_repN_r1.comp w183finL34_repN_r1) RepN.one).1 r1_sq_N

theorem r1_ne_one : r₁ ≠ 1 := by
  intro h
  have h' : eqN r1N idN = true := (RepN.eq_iff w183finL34_repN_r1 RepN.one).2 h
  rw [r1_ne_N] at h'
  exact Bool.false_ne_true h'

theorem wordPerm_mem_c1 {w : List ℕ} (hw : w ∈ c1W) : wordPerm w ∈ C₁ := by
  refine Subgroup.mem_inf.2 ⟨?_, wordPerm_mem w⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := List.all_eq_true.1 c1_comm_r1 w hw
  have h' : eqN (compN (wN w) r1N) (compN r1N (wN w)) = true := h
  exact (RepN.eq_iff ((repN_wN w).comp w183finL34_repN_r1)
    (w183finL34_repN_r1.comp (repN_wN w))).1 h'

theorem mem_c1 {x : Equiv.Perm (Fin 42)} (hx : x ∈ C₁) :
    ∃ w ∈ c1W, wordPerm w = x := by
  have hlen : c1W.length = 64 := c1W_length
  have hmem : ∀ k : Fin 64, c1W[k.1]'(by rw [hlen]; exact k.2) ∈ c1W :=
    fun k => List.getElem_mem _
  let f : Fin 64 → C₁ := fun k =>
    ⟨wordPerm (c1W[k.1]'(by rw [hlen]; exact k.2)), wordPerm_mem_c1 (hmem k)⟩
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hij' : wordPerm (c1W[i.1]'(by rw [hlen]; exact i.2)) =
        wordPerm (c1W[j.1]'(by rw [hlen]; exact j.2)) := congrArg Subtype.val hij
    have heq : eqN (wN (c1W[i.1]'(by rw [hlen]; exact i.2)))
        (wN (c1W[j.1]'(by rw [hlen]; exact j.2))) = true :=
      (RepN.eq_iff (repN_wN _) (repN_wN _)).2 hij'
    have hp := List.pairwise_iff_getElem.1 c1_distinct
    have hlenN : c1N.length = 64 := by simp [c1N, hlen]
    rcases Nat.lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hlt | hlt
    · have := hp i.1 j.1 (by rw [hlenN]; exact i.2) (by rw [hlenN]; exact j.2) hlt
      simp only [c1N, List.getElem_map] at this
      rw [heq] at this
      exact absurd this (by simp)
    · have := hp j.1 i.1 (by rw [hlenN]; exact j.2) (by rw [hlenN]; exact i.2) hlt
      simp only [c1N, List.getElem_map] at this
      have heq' : eqN (wN (c1W[j.1]'(by rw [hlen]; exact j.2)))
          (wN (c1W[i.1]'(by rw [hlen]; exact i.2))) = true :=
        (RepN.eq_iff (repN_wN _) (repN_wN _)).2 hij'.symm
      rw [heq'] at this
      exact absurd this (by simp)
  have hbij : Function.Bijective f :=
    hinj.bijective_of_nat_card_le (by rw [card_C₁, Nat.card_eq_fintype_card, Fintype.card_fin])
  obtain ⟨k, hk⟩ := hbij.2 ⟨x, hx⟩
  exact ⟨c1W[k.1]'(by rw [hlen]; exact k.2), hmem k, congrArg Subtype.val hk⟩

@[expose] def Z0 : Subgroup (Equiv.Perm (Fin 42)) where
  carrier := {x | ∃ w ∈ z0W, wordPerm w = x}
  mul_mem' := by
    rintro a b ⟨wa, hwa, rfl⟩ ⟨wb, hwb, rfl⟩
    have h := List.all_eq_true.1 z0_mul (wN wa) (List.mem_map.2 ⟨wa, hwa, rfl⟩)
    have h2 := List.all_eq_true.1 h (wN wb) (List.mem_map.2 ⟨wb, hwb, rfl⟩)
    obtain ⟨zN, hzN, hzeq⟩ := List.any_eq_true.1 h2
    obtain ⟨wc, hwc, rfl⟩ := List.mem_map.1 hzN
    exact ⟨wc, hwc, ((RepN.eq_iff ((repN_wN wa).comp (repN_wN wb)) (repN_wN wc)).1 hzeq).symm⟩
  one_mem' := ⟨[], by decide, rfl⟩
  inv_mem' := by
    rintro a ⟨wa, hwa, rfl⟩
    have h := List.all_eq_true.1 z0_inv (wN wa) (List.mem_map.2 ⟨wa, hwa, rfl⟩)
    have hsq : wordPerm wa * wordPerm wa = 1 :=
      (RepN.eq_iff ((repN_wN wa).comp (repN_wN wa)) RepN.one).1 h
    exact ⟨wa, hwa, (inv_eq_of_mul_eq_one_right hsq).symm⟩

theorem mem_Z0_iff {x : Equiv.Perm (Fin 42)} : x ∈ Z0 ↔ ∃ w ∈ z0W, wordPerm w = x := Iff.rfl

private theorem w183finL34_z0W_eq_of_eqN {a b : List ℕ} (ha : a ∈ z0W) (hb : b ∈ z0W)
    (h : eqN (wN a) (wN b) = true) : a = b := by
  simp only [z0W, List.mem_cons, List.not_mem_nil, or_false] at ha hb
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
    first
      | rfl
      | (exfalso; revert h; decide +kernel)

private theorem w183finL34_wordPerm_injOn :
    Set.InjOn wordPerm {w : List ℕ | w ∈ z0W} := by
  intro a ha b hb hab
  exact w183finL34_z0W_eq_of_eqN ha hb ((RepN.eq_iff (repN_wN a) (repN_wN b)).2 hab)

theorem card_Z0 : Nat.card Z0 = 4 := by
  have hinj : Set.InjOn wordPerm {w : List ℕ | w ∈ z0W} := w183finL34_wordPerm_injOn
  have hset : (Z0 : Set (Equiv.Perm (Fin 42))) = wordPerm '' {w : List ℕ | w ∈ z0W} := by
    ext x
    change x ∈ Z0 ↔ x ∈ wordPerm '' {w : List ℕ | w ∈ z0W}
    rw [mem_Z0_iff]
    rfl
  have hs : {w : List ℕ | w ∈ z0W} = (z0W.toFinset : Set (List ℕ)) := by
    ext w
    simp
  change (Z0 : Set (Equiv.Perm (Fin 42))).ncard = 4
  rw [hset, hinj.ncard_image, hs, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup (by decide +kernel)]
  rfl

end CFSG.LocalAnalysis.WeakClosure81.W183L34

end
