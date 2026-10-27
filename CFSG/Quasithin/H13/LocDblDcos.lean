module

public import Certificates.Data.CFSGNative.H13.LocDblDc
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBase

public section

namespace CFSG.Quasithin.H13.LocDbl.Dc

open CFSG.QuasithinUnique.K1.SporadicPerm hiding img keyNat
open CFSG.Quasithin.H13.LocDbl.DcNative
open DoubleCoset

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)]

theorem eq_of_base {B : List ℕ} (hB : ∀ b ∈ B, b < n)
    (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1) {g h : Γ}
    (H : ∀ b ∈ B, act n g b = act n h b) : g = h := by
  have : g⁻¹ * h = 1 := by
    apply hbase
    intro b hb
    rw [act_mul _ _ (hB b hb), ← H b hb, ← act_mul _ _ (hB b hb), inv_mul_cancel,
      act_one (hB b hb)]
  exact inv_mul_eq_one.mp this

@[expose] def wprod (L : List Γ) (w : List ℕ) : Γ := (w.map fun l => L.getD l 1).prod

theorem wprod_cons (L : List Γ) (l : ℕ) (w : List ℕ) :
    wprod L (l :: w) = L.getD l 1 * wprod L w := by
  simp [wprod]

theorem evalW_eq (T : Array (Array ℕ)) (L : List Γ) (w : List ℕ)
    (hT : ∀ l ∈ w, ∀ q < n, img (T.getD l #[]) q = act n (L.getD l 1) q) {p : ℕ} (hp : p < n) :
    evalW T w p = act n (wprod L w) p := by
  induction w with
  | nil => simp [evalW, wprod, act_one hp]
  | cons l w ih =>
    have ih' := ih (fun l' hl' => hT l' (List.mem_cons_of_mem _ hl'))
    have e : evalW T (l :: w) p = img (T.getD l #[]) (evalW T w p) := rfl
    rw [e, ih', hT l List.mem_cons_self _ (act_lt _ hp), wprod_cons, act_mul _ _ hp]

theorem img_tabW (T : Array (Array ℕ)) (w : List ℕ) {p : ℕ} (hp : p < n) :
    img (tabW n T w) p = evalW T w p := by
  simp [img, tabW, Array.getD_eq_getD_getElem?, hp]

theorem wprod_invW (a b : Γ) (w : List ℕ) (hw : ∀ l ∈ w, l < 4) :
    wprod [a, b, a⁻¹, b⁻¹] (invW w) = (wprod [a, b, a⁻¹, b⁻¹] w)⁻¹ := by
  unfold wprod invW
  rw [List.prod_inv_reverse, List.map_reverse, List.map_map, List.map_map]
  congr 2
  apply List.map_congr_left
  intro l hl
  have := hw l hl
  simp only [Function.comp_apply, invL]
  interval_cases l <;> simp

@[expose] def ABOK (n : ℕ) [MulAction Γ (Fin n)] (AB : Array (Array ℕ)) (a b : Γ) : Prop :=
  ∀ l < 4, ∀ q < n, img (AB.getD l #[]) q = act n ([a, b, a⁻¹, b⁻¹].getD l 1) q

@[expose] def RTOK (n : ℕ) [MulAction Γ (Fin n)] (RT RTi : Array (Array ℕ)) (rg : List Γ) :
    Prop :=
  RT.size = rg.length ∧ RTi.size = rg.length ∧
    ∀ t < rg.length, ∀ q < n, img (RT.getD t #[]) q = act n (rg.getD t 1) q ∧
      img (RTi.getD t #[]) q = act n (rg.getD t 1)⁻¹ q

@[expose] def wAB (a b : Γ) (w : List ℕ) : Γ := wprod [a, b, a⁻¹, b⁻¹] w

theorem act_wAB {AB : Array (Array ℕ)} {a b : Γ} (hAB : ABOK n AB a b) {w : List ℕ}
    (hw : ∀ l ∈ w, l < 4) {p : ℕ} (hp : p < n) : evalW AB w p = act n (wAB a b w) p :=
  evalW_eq AB _ w (fun l hl => hAB l (hw l hl)) hp

theorem act_wAB_inv {AB : Array (Array ℕ)} {a b : Γ} (hAB : ABOK n AB a b) {w : List ℕ}
    (hw : ∀ l ∈ w, l < 4) {p : ℕ} (hp : p < n) :
    evalW AB (invW w) p = act n (wAB a b w)⁻¹ p := by
  rw [wAB, ← wprod_invW a b w hw]
  refine evalW_eq AB _ _ (fun l hl => hAB l ?_) hp
  simp only [invW, List.mem_reverse, List.mem_map] at hl
  obtain ⟨l', hl', rfl⟩ := hl
  have := hw l' hl'
  simp only [invL]; split_ifs <;> omega

@[expose] def edgeList (rg : List Γ) (x : Γ) : List Γ := rg ++ rg.map (·⁻¹) ++ [x, x⁻¹]

theorem edgeList_getD_lt (rg : List Γ) (x : Γ) {t : ℕ} (ht : t < rg.length) :
    (edgeList rg x).getD t 1 = rg.getD t 1 := by
  simp [edgeList, List.getD_eq_getElem?_getD, List.getElem?_append_left ht]

theorem edgeList_getD_inv (rg : List Γ) (x : Γ) {t : ℕ} (h1 : rg.length ≤ t)
    (h2 : t < 2 * rg.length) :
    (edgeList rg x).getD t 1 = (rg.getD (t - rg.length) 1)⁻¹ := by
  have hlt : t < (rg ++ List.map (fun x => x⁻¹) rg).length := by simp; omega
  simp only [edgeList, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt,
    List.getElem?_append_right h1, List.getElem?_map]
  rw [List.getElem?_eq_getElem (by omega)]
  simp

theorem edgeList_getD_x (rg : List Γ) (x : Γ) :
    (edgeList rg x).getD (2 * rg.length) 1 = x := by
  simp [edgeList, List.getD_eq_getElem?_getD, two_mul]

theorem edgeList_getD_xi (rg : List Γ) (x : Γ) :
    (edgeList rg x).getD (2 * rg.length + 1) 1 = x⁻¹ := by
  have : (rg ++ (List.map (fun x => x⁻¹) rg ++ [x, x⁻¹]))[rg.length + rg.length + 1]? =
      some x⁻¹ := by
    rw [List.getElem?_append_right (by omega)]
    rw [show rg.length + rg.length + 1 - rg.length = rg.length + 1 by omega]
    rw [List.getElem?_append_right (by simp)]
    simp
  simp [edgeList, List.getD_eq_getElem?_getD, two_mul, this]

theorem edgeLetter_eq (RT RTi AB : Array (Array ℕ)) (a b : Γ) (rg : List Γ)
    (hAB : ABOK n AB a b) (hRT : RTOK n RT RTi rg) (w : List ℕ)
    (hw : ∀ l ∈ w, l < 4) {l : ℕ} (hl : l < RT.size + RTi.size + 2) {q : ℕ} (hq : q < n) :
    edgeLetter RT RTi AB w l q = act n ((edgeList rg (wAB a b w)).getD l 1) q := by
  obtain ⟨h1, h2, h3⟩ := hRT
  unfold edgeLetter
  by_cases c1 : l < RT.size
  · simp only [c1, ↓reduceIte]
    rw [edgeList_getD_lt _ _ (by omega)]
    exact (h3 l (by omega) q hq).1
  simp only [c1, ↓reduceIte]
  by_cases c2 : l < RT.size + RTi.size
  · simp only [c2, ↓reduceIte]
    rw [edgeList_getD_inv _ _ (by omega) (by omega), h1]
    exact (h3 (l - rg.length) (by omega) q hq).2
  simp only [c2, ↓reduceIte]
  by_cases c3 : l = RT.size + RTi.size
  · simp only [c3, ↓reduceIte]
    rw [show RT.size + RTi.size = 2 * rg.length by omega, edgeList_getD_x]
    exact act_wAB hAB hw hq
  simp only [c3, ↓reduceIte]
  rw [show l = 2 * rg.length + 1 by omega, edgeList_getD_xi]
  exact act_wAB_inv hAB hw hq

theorem evalE_eq (RT RTi AB : Array (Array ℕ)) (a b : Γ) (rg : List Γ)
    (hAB : ABOK n AB a b) (hRT : RTOK n RT RTi rg) (w : List ℕ)
    (hw : ∀ l ∈ w, l < 4) (e : List ℕ) (he : ∀ l ∈ e, l < RT.size + RTi.size + 2) {p : ℕ}
    (hp : p < n) :
    evalE RT RTi AB w e p = act n (wprod (edgeList rg (wAB a b w)) e) p := by
  induction e with
  | nil => simp [evalE, wprod, act_one hp]
  | cons l e ih =>
    have ih' := ih (fun l' hl' => he l' (List.mem_cons_of_mem _ hl'))
    have e1 : evalE RT RTi AB w (l :: e) p = edgeLetter RT RTi AB w l (evalE RT RTi AB w e p) :=
      rfl
    rw [e1, ih', wprod_cons, act_mul _ _ hp]
    exact edgeLetter_eq RT RTi AB a b rg hAB ⟨hRT.1, hRT.2.1, hRT.2.2⟩ w hw
      (he l List.mem_cons_self) (act_lt _ hp)

theorem wprod_edge_mem (rg : List Γ) (x : Γ) (e : List ℕ) :
    wprod (edgeList rg x) e ∈ Subgroup.closure {y | y ∈ rg} ⊔ Subgroup.zpowers x := by
  unfold wprod
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨l, -, rfl⟩ := List.mem_map.mp hg
  rw [List.getD_eq_getElem?_getD]
  cases h : (edgeList rg x)[l]? with
  | none => exact Subgroup.one_mem _
  | some y =>
    have hy := List.mem_of_getElem? h
    simp only [edgeList, List.mem_append, List.mem_map, List.mem_cons, List.mem_nil_iff,
      or_false] at hy
    simp only [Option.getD_some]
    rcases hy with (hy | ⟨z, hz, rfl⟩) | rfl | rfl
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure hy)
    · exact Subgroup.mem_sup_left (Subgroup.inv_mem _ (Subgroup.subset_closure hz))
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · exact Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.mem_zpowers _))

theorem foldl_push_spec {α : Type*} (f : Array α → ℕ → α) (P : ℕ → α → Prop) (d : α) (N : ℕ)
    (h : ∀ acc : Array α, ∀ k < N, acc.size = k → (∀ j < k, P j (acc.getD j d)) →
      P k (f acc k)) :
    ((List.range N).foldl (fun acc k => acc.push (f acc k)) #[]).size = N ∧
      ∀ j < N, P j (((List.range N).foldl (fun acc k => acc.push (f acc k)) #[]).getD j d) := by
  induction N with
  | zero => simp
  | succ N ih =>
    obtain ⟨hs, hP⟩ := ih fun acc k hk => h acc k (by omega)
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    set A := (List.range N).foldl (fun acc k => acc.push (f acc k)) #[] with hA
    refine ⟨by simp [hs], fun j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
    · rw [getD_push_lt A _ d (by omega)]
      exact hP j hj
    · have hj' : j = A.size := by omega
      rw [hj', getD_push_self, hs]
      exact h A N (by omega) hs hP

noncomputable def enumElt (L : List Γ) (par lab : Array ℕ) (k : ℕ) : Γ :=
  if _h : 0 < k ∧ par.getD k 0 < k then
    L.getD (lab.getD k 0) 1 * enumElt L par lab (par.getD k 0)
  else 1
termination_by k
decreasing_by exact _h.2

theorem enumElt_zero (L : List Γ) (par lab : Array ℕ) : enumElt L par lab 0 = 1 := by
  rw [enumElt]; simp

theorem enumElt_pos (L : List Γ) (par lab : Array ℕ) {k : ℕ} (hk : 0 < k)
    (hp : par.getD k 0 < k) :
    enumElt L par lab k = L.getD (lab.getD k 0) 1 * enumElt L par lab (par.getD k 0) := by
  rw [enumElt]
  simp only [hk, hp, and_self, ↓reduceDIte]

theorem enumOK_spec {N : ℕ} {G : Array (Array ℕ)} {par lab : Array ℕ}
    (h : enumOK N G par lab = true) {k : ℕ} (hk : k < N) (hk0 : 0 < k) :
    par.getD k 0 < k ∧ lab.getD k 0 < G.size := by
  have := List.all_eq_true.mp h k (List.mem_range.mpr hk)
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at this
  rcases this with h0 | h1
  · omega
  · exact h1

theorem ptsArr_spec (G : Array (Array ℕ)) (L : List Γ) (par lab : Array ℕ) (N q : ℕ) (hq : q < n)
    (hG : ∀ t < G.size, ∀ p < n, img (G.getD t #[]) p = act n (L.getD t 1) p)
    (hok : enumOK N G par lab = true) :
    (ptsArr G par lab N q).size = N ∧
      ∀ k < N, (ptsArr G par lab N q).getD k 0 = act n (enumElt L par lab k) q := by
  have := foldl_push_spec (fun acc k =>
      if k = 0 then q else img (G.getD (lab.getD k 0) #[]) (acc.getD (par.getD k 0) 0))
    (fun k v => v = act n (enumElt L par lab k) q) 0 N ?_
  · exact this
  intro acc k hk _ hprev
  by_cases hk0 : k = 0
  · subst hk0
    simp [enumElt_zero, act_one hq]
  · simp only [hk0, ↓reduceIte]
    obtain ⟨hp, hl⟩ := enumOK_spec hok hk (Nat.pos_of_ne_zero hk0)
    rw [hprev _ hp, hG _ hl _ (act_lt _ hq), ← act_mul _ _ hq,
      enumElt_pos L par lab (Nat.pos_of_ne_zero hk0) hp]

theorem enumElt_mem (L : List Γ) (par lab : Array ℕ) (k : ℕ) :
    enumElt L par lab k ∈ Subgroup.closure {x | x ∈ L} := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [enumElt]
    split_ifs with h
    · refine Subgroup.mul_mem _ ?_ (ih _ h.2)
      rw [List.getD_eq_getElem?_getD]
      cases hl : L[lab.getD k 0]? with
      | none => exact Subgroup.one_mem _
      | some x => exact Subgroup.subset_closure (List.mem_of_getElem? hl)
    · exact Subgroup.one_mem _

@[expose] def keyOf (n : ℕ) [MulAction Γ (Fin n)] (B : List ℕ) (g : Γ) : ℕ :=
  keyNat n B.length (B.map (act n g))

theorem rows_spec {B : List ℕ} (hB : ∀ b ∈ B, b < n) (G : Array (Array ℕ)) (L : List Γ)
    (par lab : Array ℕ) (N : ℕ)
    (hG : ∀ t < G.size, ∀ p < n, img (G.getD t #[]) p = act n (L.getD t 1) p)
    (hok : enumOK N G par lab = true) {k : ℕ} (hk : k < N) :
    (B.map (ptsArr G par lab N)).map (fun A => A.getD k 0) =
      B.map (act n (enumElt L par lab k)) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro b hb
  exact (ptsArr_spec G L par lab N b (hB b hb) hG hok).2 k hk

theorem rowKeys_eq {B : List ℕ} (hB : ∀ b ∈ B, b < n) (G : Array (Array ℕ)) (L : List Γ)
    (par lab : Array ℕ) (N : ℕ)
    (hG : ∀ t < G.size, ∀ p < n, img (G.getD t #[]) p = act n (L.getD t 1) p)
    (hok : enumOK N G par lab = true) :
    rowKeys n B G par lab N = (List.range N).map fun k => keyOf n B (enumElt L par lab k) := by
  unfold rowKeys
  apply List.map_congr_left
  intro k hk
  rw [rows_spec hB G L par lab N hG hok (List.mem_range.mp hk)]
  rfl

theorem conjKeys_eq {B : List ℕ} (hB : ∀ b ∈ B, b < n) (G : Array (Array ℕ)) (L : List Γ)
    (par lab : Array ℕ) (N : ℕ)
    (hG : ∀ t < G.size, ∀ p < n, img (G.getD t #[]) p = act n (L.getD t 1) p)
    (hok : enumOK N G par lab = true) {x y : Γ} {Xi Y : Array ℕ}
    (hXi : ∀ p < n, img Xi p = act n x⁻¹ p) (hY : ∀ p < n, img Y p = act n y p) :
    conjKeys n B G par lab N Xi Y =
      (List.range N).map fun k => keyOf n B (x⁻¹ * enumElt L par lab k * y) := by
  unfold conjKeys
  apply List.map_congr_left
  intro k hk
  have hk' := List.mem_range.mp hk
  unfold keyOf
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro b hb
  have hbn := hB b hb
  have hy := hY b hbn
  have hyn : act n y b < n := act_lt _ hbn
  rw [Function.comp_apply, hy, (ptsArr_spec G L par lab N _ hyn hG hok).2 k hk',
    hXi _ (act_lt _ hyn), ← act_mul _ _ hyn, ← act_mul _ _ hbn]

theorem strictInc_le : ∀ {a : ℕ} {l : List ℕ}, strictInc (a :: l) = true → ∀ x ∈ l, a < x
  | _, [], _, x, hx => by simp at hx
  | a, b :: l, h, x, hx => by
    simp only [strictInc, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact h.1.trans (strictInc_le h.2 x hx)

theorem strictInc_nodup : ∀ l : List ℕ, strictInc l = true → l.Nodup
  | [], _ => List.nodup_nil
  | [a], _ => List.nodup_singleton a
  | a :: b :: l, h => by
    have h' := h
    simp only [strictInc, Bool.and_eq_true, decide_eq_true_eq] at h'
    refine List.nodup_cons.mpr ⟨fun hm => ?_, strictInc_nodup (b :: l) h'.2⟩
    exact lt_irrefl a (strictInc_le h a hm)

theorem distinctNat_nodup {l : List ℕ} (h : distinctNat l = true) : l.Nodup :=
  (List.mergeSort_perm l _).nodup_iff.mp (strictInc_nodup _ h)

theorem inj_of_nodup {B : List ℕ} {e : ℕ → Γ} {N : ℕ}
    (h : ((List.range N).map fun k => keyOf n B (e k)).Nodup) :
    ∀ i < N, ∀ j < N, e i = e j → i = j := fun i hi j hj hij =>
  List.inj_on_of_nodup_map h (List.mem_range.mpr hi) (List.mem_range.mpr hj) (by rw [hij])

theorem surj_of_card [Finite Γ] (R : Subgroup Γ) (e : ℕ → Γ) (N : ℕ)
    (hmem : ∀ k, e k ∈ R) (hinj : ∀ i < N, ∀ j < N, e i = e j → i = j)
    (hcard : Nat.card R = N) : ∀ g ∈ R, ∃ k < N, e k = g := by
  let f : Fin N → R := fun k => ⟨e k, hmem k⟩
  have hfi : Function.Injective f := fun i j hij =>
    Fin.ext (hinj i i.2 j j.2 (congrArg Subtype.val hij))
  have hfb : Function.Bijective f :=
    hfi.bijective_of_nat_card_le (by rw [hcard, Nat.card_eq_fintype_card, Fintype.card_fin])
  intro g hg
  obtain ⟨k, hk⟩ := hfb.2 ⟨g, hg⟩
  exact ⟨k, k.2, congrArg Subtype.val hk⟩

theorem closure_subset_of_closed [Finite Γ] (L : List Γ) (E : Set Γ)
    (h1 : (1 : Γ) ∈ E) (hmul : ∀ s ∈ L, ∀ y ∈ E, s * y ∈ E) :
    (Subgroup.closure {x | x ∈ L} : Set Γ) ⊆ E := by
  intro g hg
  have hg' : g ∈ Submonoid.closure {x | x ∈ L} := by
    rw [← Subgroup.closure_toSubmonoid_of_isOfFinOrder (fun x _ => isOfFinOrder_of_finite x)]
    exact hg
  clear hg
  induction hg' using Submonoid.closure_induction_left with
  | one => exact h1
  | mul_left s hs y _ ih => exact hmul s hs y ih

theorem enum_closure [Finite Γ] (L : List Γ) (e : ℕ → Γ) (N : ℕ) (hN : 0 < N) (he0 : e 0 = 1)
    (hmem : ∀ k, e k ∈ Subgroup.closure {x | x ∈ L})
    (hinj : ∀ i < N, ∀ j < N, e i = e j → i = j)
    (hcl : ∀ k < N, ∀ s ∈ L, ∃ k' < N, e k' = s * e k) :
    (∀ g ∈ Subgroup.closure {x | x ∈ L}, ∃ k < N, e k = g) ∧
      Nat.card (Subgroup.closure {x | x ∈ L}) = N := by
  have hsub := closure_subset_of_closed L {g | ∃ k < N, e k = g} ⟨0, hN, he0⟩
    (fun s hs y ⟨k, hk, hky⟩ => by
      obtain ⟨k', hk', h'⟩ := hcl k hk s hs
      exact ⟨k', hk', by rw [h', hky]⟩)
  refine ⟨fun g hg => hsub hg, ?_⟩
  let f : Fin N → Subgroup.closure {x | x ∈ L} := fun k => ⟨e k, hmem k⟩
  have hf : Function.Bijective f := by
    refine ⟨fun i j hij => Fin.ext (hinj i i.2 j j.2 (congrArg Subtype.val hij)), fun g => ?_⟩
    obtain ⟨k, hk, hkg⟩ := hsub g.2
    exact ⟨⟨k, hk⟩, Subtype.ext hkg⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, Fintype.card_fin]

theorem stab_iff (R : Subgroup Γ) (x : Γ) (r : R) :
    r ∈ MulAction.stabilizer R (x : Γ ⧸ R) ↔ x⁻¹ * r * x ∈ R := by
  rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def, MulAction.Quotient.smul_mk,
    QuotientGroup.eq]
  constructor
  · intro h
    have := R.inv_mem h
    simpa [mul_assoc] using this
  · intro h
    have := R.inv_mem h
    simpa [mul_assoc] using this

theorem card_le_hitCount [Finite Γ] (e : ℕ → Γ) (N : ℕ) (R : Subgroup Γ) (B : List ℕ)
    (hsurj : ∀ g ∈ R, ∃ k < N, e k = g) (x : Γ) :
    Nat.card (MulAction.stabilizer R (x : Γ ⧸ R)) ≤
      hitCount (Std.HashSet.ofList ((List.range N).map fun k => keyOf n B (e k)))
        ((List.range N).map fun k => keyOf n B (x⁻¹ * e k * x)) := by
  classical
  set S := Std.HashSet.ofList ((List.range N).map fun k => keyOf n B (e k)) with hS
  have hstab : ∀ r : MulAction.stabilizer R (x : Γ ⧸ R), ∃ k < N, e k = r ∧
      S.contains (keyOf n B (x⁻¹ * e k * x)) = true := by
    intro r
    obtain ⟨k, hk, hkr⟩ := hsurj r r.1.2
    refine ⟨k, hk, hkr, ?_⟩
    have hr : x⁻¹ * (r : Γ) * x ∈ R := (stab_iff R x r.1).mp r.2
    obtain ⟨k', hk', hk'r⟩ := hsurj _ hr
    rw [hS, Std.HashSet.contains_ofList, List.contains_iff_mem, List.mem_map, hkr]
    exact ⟨k', List.mem_range.mpr hk', by rw [hk'r]⟩
  choose idx hidx using hstab
  have hinjidx : Function.Injective idx := by
    intro r s h
    apply Subtype.ext; apply Subtype.ext
    rw [← (hidx r).2.1, ← (hidx s).2.1, h]
  have hcount : hitCount S ((List.range N).map fun k => keyOf n B (x⁻¹ * e k * x)) =
      ((Finset.range N).filter fun k => S.contains (keyOf n B (x⁻¹ * e k * x)) = true).card := by
    unfold hitCount
    rw [List.filter_map, List.length_map]
    rw [Finset.card_def, Finset.filter_val, Finset.range_val, Multiset.range,
      Multiset.filter_coe, Multiset.coe_card]
    rfl
  rw [hcount]
  have : Fintype (MulAction.stabilizer R (x : Γ ⧸ R)) := Fintype.ofFinite _
  have := Finset.card_le_card_of_injOn
    (s := (Finset.univ : Finset (MulAction.stabilizer R (x : Γ ⧸ R))))
    (t := (Finset.range N).filter fun k => S.contains (keyOf n B (x⁻¹ * e k * x)) = true) idx
    (fun r _ => by
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      exact ⟨(hidx r).1, (hidx r).2.2⟩) (fun r _ s _ h => hinjidx h)
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at this
  exact this

theorem not_mem_of_noHit (e : ℕ → Γ) (N : ℕ) (R : Subgroup Γ) (B : List ℕ)
    (hsurj : ∀ g ∈ R, ∃ k < N, e k = g) (x y : Γ)
    (h : noHit (Std.HashSet.ofList ((List.range N).map fun k => keyOf n B (e k)))
      ((List.range N).map fun k => keyOf n B (x⁻¹ * e k * y)) = true) :
    y ∉ doubleCoset x (R : Set Γ) R := by
  intro hy
  obtain ⟨r1, hr1, r2, hr2, rfl⟩ := mem_doubleCoset.mp hy
  obtain ⟨k, hk, hke⟩ := hsurj r1⁻¹ (R.inv_mem hr1)
  have hin : x⁻¹ * e k * (r1 * x * r2) = r2 := by rw [hke]; group
  obtain ⟨k', hk', hk'e⟩ := hsurj r2 hr2
  have := List.all_eq_true.mp h (keyOf n B (x⁻¹ * e k * (r1 * x * r2)))
    (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)
  have hmem : keyOf n B (x⁻¹ * e k * (r1 * x * r2)) ∈
      (List.range N).map fun k => keyOf n B (e k) :=
    List.mem_map.mpr ⟨k', List.mem_range.mpr hk', by rw [hk'e, hin]⟩
  rw [Std.HashSet.contains_ofList, List.contains_iff_mem.mpr hmem] at this
  exact absurd this (by decide)

open Pointwise in
theorem card_doubleCoset_ge [Finite Γ] (R : Subgroup Γ) (x : Γ) {c : ℕ}
    (hc : Nat.card (MulAction.stabilizer R (x : Γ ⧸ R)) ≤ c) :
    Nat.card R * (Nat.card R / c) ≤ Nat.card (doubleCoset x (R : Set Γ) R) := by
  have h1 := Subgroup.card_mul_eq_card_subgroup_mul_card_quotient R ((R : Set Γ) * {x})
  have hdc : doubleCoset x (R : Set Γ) R = (R : Set Γ) * {x} * R := rfl
  have himg : ((R : Set Γ) * {x}).image (fun g : Γ => (g : Γ ⧸ R)) =
      MulAction.orbit R (x : Γ ⧸ R) := by
    ext q
    simp only [Set.mem_image, MulAction.mem_orbit_iff, Set.mem_mul, Set.mem_singleton_iff]
    constructor
    · rintro ⟨g, ⟨r, hr, y, rfl, rfl⟩, rfl⟩
      exact ⟨⟨r, hr⟩, rfl⟩
    · rintro ⟨⟨r, hr⟩, rfl⟩
      exact ⟨r * x, ⟨r, hr, x, rfl, rfl⟩, rfl⟩
  rw [hdc, h1, himg]
  have h2 := (MulAction.stabilizer R (x : Γ ⧸ R)).card_mul_index
  rw [MulAction.index_stabilizer] at h2
  have hpos : 0 < Nat.card (MulAction.stabilizer R (x : Γ ⧸ R)) := Nat.card_pos
  have h3 : Nat.card (MulAction.orbit R (x : Γ ⧸ R)) =
      Nat.card R / Nat.card (MulAction.stabilizer R (x : Γ ⧸ R)) := by
    rw [Nat.card_coe_set_eq, ← h2, Nat.mul_div_cancel_left _ hpos]
  apply Nat.mul_le_mul_left
  rw [h3]
  exact Nat.div_le_div_left hc hpos

theorem listSum_eq (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  rw [Finset.sum_eq_multiset_sum, Finset.range_val, Multiset.range, Multiset.map_coe,
    Multiset.sum_coe]

theorem lab_closure (lb : ℕ → ℕ) (L : List Γ) (hL : ∀ s ∈ L, ∀ q < n, lb (act n s q) = lb q)
    {r : Γ} (hr : r ∈ Subgroup.closure {x | x ∈ L}) : ∀ q < n, lb (act n r q) = lb q := by
  induction hr using Subgroup.closure_induction with
  | mem s hs => exact hL s hs
  | one => intro q hq; rw [act_one hq]
  | mul s t _ _ hs ht => intro q hq; rw [act_mul _ _ hq, hs _ (act_lt _ hq), ht q hq]
  | inv s _ hs =>
    intro q hq
    have := hs (act n s⁻¹ q) (act_lt _ hq)
    rw [← act_mul _ _ hq, mul_inv_cancel, act_one hq] at this
    exact this.symm

theorem inv_eq (lb : ℕ → ℕ) (R : Subgroup Γ) (hR : ∀ r ∈ R, ∀ q < n, lb (act n r q) = lb q)
    (x : Γ) {r1 r2 : Γ} (h1 : r1 ∈ R) (h2 : r2 ∈ R) :
    ((List.range n).map fun q => wt (lb q) (lb (act n (r1 * x * r2) q))).sum =
      ((List.range n).map fun q => wt (lb q) (lb (act n x q))).sum := by
  rw [listSum_eq, listSum_eq]
  have e1 : ∀ q ∈ Finset.range n, wt (lb q) (lb (act n (r1 * x * r2) q)) =
      wt (lb (act n r2 q)) (lb (act n x (act n r2 q))) := by
    intro q hq
    have hq' := Finset.mem_range.mp hq
    rw [act_mul _ _ hq', act_mul _ _ (act_lt _ hq'), hR r1 h1 _ (act_lt _ (act_lt _ hq')),
      hR r2 h2 q hq']
  rw [Finset.sum_congr rfl e1]
  refine Finset.sum_nbij' (fun q => act n r2 q) (fun q => act n r2⁻¹ q) ?_ ?_ ?_ ?_ ?_
  · intro q hq; exact Finset.mem_range.mpr (act_lt _ (Finset.mem_range.mp hq))
  · intro q hq; exact Finset.mem_range.mpr (act_lt _ (Finset.mem_range.mp hq))
  · intro q hq
    have hq' := Finset.mem_range.mp hq
    rw [← act_mul _ _ hq', inv_mul_cancel, act_one hq']
  · intro q hq
    have hq' := Finset.mem_range.mp hq
    rw [← act_mul _ _ hq', mul_inv_cancel, act_one hq']
  · intro q _; rfl

theorem eq_top_of_card [Finite Γ] (S : Subgroup Γ) (h : Nat.card Γ < 2 * Nat.card S) :
    S = ⊤ := by
  by_contra hS
  have h1 := S.card_mul_index
  have h2 : 2 ≤ S.index := Subgroup.one_lt_index_of_ne_top hS
  nlinarith

theorem disjoint_of_not_mem (R : Subgroup Γ) {x y : Γ} (h : y ∉ doubleCoset x (R : Set Γ) R) :
    Disjoint (doubleCoset x (R : Set Γ) R) (doubleCoset y (R : Set Γ) R) := by
  by_contra hd
  have := DoubleCoset.eq_of_not_disjoint hd
  apply h
  rw [this]
  exact DoubleCoset.mem_doubleCoset_self R R y

theorem doubleCoset_subset {R S : Subgroup Γ} (hRS : R ≤ S) {x : Γ} (hx : x ∈ S) :
    doubleCoset x (R : Set Γ) R ⊆ S := by
  intro g hg
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_doubleCoset.mp hg
  exact S.mul_mem (S.mul_mem (hRS ha) hx) (hRS hb)

theorem mass_le_card [Finite Γ] (R : Subgroup Γ) (xs : ℕ → Γ) (J : List ℕ) (hnd : J.Nodup)
    (hdisj : ∀ i ∈ J, ∀ j ∈ J, i ≠ j →
      Disjoint (doubleCoset (xs i) (R : Set Γ) R) (doubleCoset (xs j) (R : Set Γ) R))
    (mass : ℕ → ℕ) (hmass : ∀ j ∈ J, mass j ≤ Nat.card (doubleCoset (xs j) (R : Set Γ) R)) :
    (J.map mass).sum ≤ (⋃ j ∈ J, doubleCoset (xs j) (R : Set Γ) R).ncard := by
  classical
  have : Fintype Γ := Fintype.ofFinite Γ
  let D : ℕ → Finset Γ := fun j => (doubleCoset (xs j) (R : Set Γ) R).toFinset
  have hcardD : ∀ j, (D j).card = Nat.card (doubleCoset (xs j) (R : Set Γ) R) := by
    intro j; rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
  have hU : (J.toFinset.biUnion D).card = ∑ j ∈ J.toFinset, (D j).card := by
    apply Finset.card_biUnion
    intro i hi j hj hij
    rw [Function.onFun, Set.disjoint_toFinset]
    exact hdisj i (List.mem_toFinset.mp hi) j (List.mem_toFinset.mp hj) hij
  have hset : ((J.toFinset.biUnion D : Finset Γ) : Set Γ) =
      ⋃ j ∈ J, doubleCoset (xs j) (R : Set Γ) R := by
    ext g; simp [D]
  rw [← hset, Set.ncard_coe_finset, hU, ← List.sum_toFinset _ hnd]
  exact Finset.sum_le_sum fun j hj => (hcardD j).symm ▸ hmass j (List.mem_toFinset.mp hj)

theorem eq_top_of_mass [Finite Γ] {R S : Subgroup Γ} (hRS : R ≤ S) (xs : ℕ → Γ) (J : List ℕ)
    (hnd : J.Nodup) (hmem : ∀ j ∈ J, xs j ∈ S)
    (hdisj : ∀ i ∈ J, ∀ j ∈ J, i ≠ j →
      Disjoint (doubleCoset (xs i) (R : Set Γ) R) (doubleCoset (xs j) (R : Set Γ) R))
    (mass : ℕ → ℕ) (hmass : ∀ j ∈ J, mass j ≤ Nat.card (doubleCoset (xs j) (R : Set Γ) R))
    (hbig : Nat.card Γ < 2 * (J.map mass).sum) : S = ⊤ := by
  apply eq_top_of_card
  have h1 := mass_le_card R xs J hnd hdisj mass hmass
  have h2 : (⋃ j ∈ J, doubleCoset (xs j) (R : Set Γ) R).ncard ≤ (S : Set Γ).ncard := by
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    intro g hg
    simp only [Set.mem_iUnion] at hg
    obtain ⟨j, hj, hgj⟩ := hg
    exact doubleCoset_subset hRS (hmem j hj) hgj
  have h3 : Nat.card ↥S = (S : Set Γ).ncard := Nat.card_coe_set_eq (S : Set Γ)
  omega

theorem gen_of_trees (R : Subgroup Γ) (xs : ℕ → Γ) (m c0 : ℕ) (E : ℕ → ℕ → Prop)
    (hE : ∀ s d, E s d → xs d ∈ R ⊔ Subgroup.zpowers (xs s)) (dIn dOut : ℕ → ℕ)
    (hin : ∀ i < m, i ≠ c0 → ∃ d < m, E i d ∧ dIn d < dIn i) (reach : List ℕ)
    (hout : ∀ j ∈ reach, j ≠ c0 → ∃ s ∈ reach, E s j ∧ dOut s < dOut j) :
    ∀ i < m, ∀ j ∈ reach, xs j ∈ R ⊔ Subgroup.zpowers (xs i) := by
  have hle : ∀ s d, xs d ∈ R ⊔ Subgroup.zpowers (xs s) →
      R ⊔ Subgroup.zpowers (xs d) ≤ R ⊔ Subgroup.zpowers (xs s) := fun s d h =>
    sup_le le_sup_left ((Subgroup.zpowers_le).mpr h)
  have h1 : ∀ i < m, xs c0 ∈ R ⊔ Subgroup.zpowers (xs i) := by
    intro i
    induction hdi : dIn i using Nat.strong_induction_on generalizing i with
    | _ k ih =>
      intro hi
      by_cases hc : i = c0
      · subst hc; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
      obtain ⟨d, hd, hEd, hlt⟩ := hin i hi hc
      exact hle i d (hE i d hEd) (ih (dIn d) (hdi ▸ hlt) d rfl hd)
  have h2 : ∀ j ∈ reach, xs j ∈ R ⊔ Subgroup.zpowers (xs c0) := by
    intro j
    induction hdj : dOut j using Nat.strong_induction_on generalizing j with
    | _ k ih =>
      intro hj
      by_cases hc : j = c0
      · subst hc; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
      obtain ⟨s, hs, hEs, hlt⟩ := hout j hj hc
      exact hle c0 s (ih (dOut s) (hdj ▸ hlt) s rfl hs) (hE s j hEs)
  intro i hi j hj
  exact hle i c0 (h1 i hi) (h2 j hj)

@[expose] def IsEnum (keyOf : Γ → ℕ) (W : Set Γ) (ks : List ℕ) : Prop :=
  ∃ (N : ℕ) (e : ℕ → Γ), ks = (List.range N).map (fun k => keyOf (e k)) ∧
    (∀ i < N, ∀ j < N, e i = e j → i = j) ∧ (∀ k < N, e k ∈ W) ∧ (∀ g ∈ W, ∃ k < N, e k = g)

omit [Group Γ] in
theorem filter_len_le [Finite Γ] (keyOf : Γ → ℕ) (P W : Set Γ) (S : Std.HashSet ℕ)
    (hP : ∀ g ∈ P, S.contains (keyOf g) = true) {ks : List ℕ} (hW : IsEnum keyOf W ks) :
    (ks.filter fun k => !S.contains k).length ≤ (W \ P).ncard := by
  classical
  obtain ⟨N, e, rfl, hinj, hmem, -⟩ := hW
  rw [List.filter_map, List.length_map]
  have hlen : ((List.range N).filter ((fun k => !S.contains k) ∘ fun k => keyOf (e k))).length =
      ((Finset.range N).filter fun k => S.contains (keyOf (e k)) = false).card := by
    rw [Finset.card_def, Finset.filter_val, Finset.range_val, Multiset.range,
      Multiset.filter_coe, Multiset.coe_card]
    congr 1
  rw [hlen, ← Set.ncard_coe_finset]
  have hinjOn :
      Set.InjOn e ↑((Finset.range N).filter fun k => S.contains (keyOf (e k)) = false) := by
    intro i hi j hj hij
    simp only [Finset.coe_filter, Finset.mem_range] at hi hj
    exact hinj i hi.1 j hj.1 hij
  rw [← hinjOn.ncard_image]
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  rintro _ ⟨k, hk, rfl⟩
  simp only [Finset.coe_filter, Finset.mem_range] at hk
  refine ⟨hmem k hk.1, fun hkP => ?_⟩
  have := hP _ hkP
  rw [hk.2] at this
  exact Bool.false_ne_true this

omit [Group Γ] in
theorem unionLB_aux [Finite Γ] (keyOf : Γ → ℕ) :
    ∀ (Ws : List (Set Γ × List ℕ)) (P : Set Γ) (c : ℕ) (S : Std.HashSet ℕ),
      (∀ g ∈ P, S.contains (keyOf g) = true) → c ≤ P.ncard →
      (∀ W ∈ Ws, IsEnum keyOf W.1 W.2) →
      ((Ws.map Prod.snd).foldl (fun (acc : Nat × Std.HashSet Nat) ks =>
        (acc.1 + (ks.filter fun k => !acc.2.contains k).length, acc.2.insertMany ks)) (c, S)).1 ≤
        (P ∪ ⋃ W ∈ Ws, W.1).ncard
  | [], P, c, S, _, hc, _ => by simpa using hc
  | W :: Ws, P, c, S, hS, hc, hW => by
    simp only [List.map_cons, List.foldl_cons]
    have hW1 := hW W List.mem_cons_self
    have key := unionLB_aux keyOf Ws (P ∪ W.1) (c + (W.2.filter fun k => !S.contains k).length)
      (S.insertMany W.2) ?_ ?_ (fun V hV => hW V (List.mem_cons_of_mem _ hV))
    · have hset : P ∪ W.1 ∪ ⋃ V ∈ Ws, V.1 = P ∪ ⋃ V ∈ W :: Ws, V.1 := by
        ext g; simp [or_assoc]
      rwa [hset] at key
    · intro g hg
      rw [Std.HashSet.contains_insertMany_list, Bool.or_eq_true]
      rcases hg with hg | hg
      · exact Or.inl (hS g hg)
      · right
        obtain ⟨N, e, he, -, -, hsurj⟩ := hW1
        obtain ⟨k, hk, rfl⟩ := hsurj g hg
        rw [he, List.contains_iff_mem, List.mem_map]
        exact ⟨k, List.mem_range.mpr hk, rfl⟩
    · have h1 := filter_len_le keyOf P W.1 S hS hW1
      have h2 : (P ∪ W.1).ncard = P.ncard + (W.1 \ P).ncard := by
        rw [← Set.union_sdiff_self, Set.ncard_union_eq Set.disjoint_sdiff_right (Set.toFinite _)
          (Set.toFinite _)]
      omega

omit [Group Γ] in
theorem unionLB_le [Finite Γ] (keyOf : Γ → ℕ) (Ws : List (Set Γ × List ℕ))
    (hW : ∀ W ∈ Ws, IsEnum keyOf W.1 W.2) :
    unionLB (Ws.map Prod.snd) ≤ (⋃ W ∈ Ws, W.1).ncard := by
  have := unionLB_aux keyOf Ws ∅ 0 ∅ (by simp) (by simp) hW
  simpa [unionLB] using this

theorem le_of_subset_union [Finite Γ] {R Y : Subgroup Γ} (Vs : List (Subgroup Γ))
    (hk : Vs.length ≤ 3) (hRY : R ≤ Y) (hRV : ∀ V ∈ Vs, R ≤ V)
    (hodd : ¬ 2 ∣ (R.subgroupOf Y).index) (hsub : ∀ g ∈ Y, ∃ V ∈ Vs, g ∈ V) :
    ∃ V ∈ Vs, Y ≤ V := by
  classical
  by_contra hno
  push Not at hno
  have : Fintype Γ := Fintype.ofFinite Γ
  have h3 : ∀ V ∈ Vs, 3 * Nat.card ↥(Y ⊓ V) ≤ Nat.card Y := by
    intro V hV
    set I := (Y ⊓ V).subgroupOf Y with hI
    have hle : R.subgroupOf Y ≤ I := Subgroup.subgroupOf_mono _ (le_inf hRY (hRV V hV))
    have hdvd : I.index ∣ (R.subgroupOf Y).index := Subgroup.index_dvd_of_le hle
    have hne1 : I.index ≠ 1 := by
      intro h1
      rw [Subgroup.index_eq_one] at h1
      apply hno V hV
      intro y hy
      have : (⟨y, hy⟩ : Y) ∈ I := by rw [h1]; trivial
      exact (Subgroup.mem_subgroupOf.mp this).2
    have hcard : Nat.card I = Nat.card ↥(Y ⊓ V) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    have hmul := I.card_mul_index
    have hYpos : 0 < Nat.card Y := Nat.card_pos
    have hpos : 0 < I.index := by
      rcases Nat.eq_zero_or_pos I.index with h0 | h0
      · rw [h0, mul_zero] at hmul; omega
      · exact h0
    have hodd' : ¬ 2 ∣ I.index := fun h2 => hodd (h2.trans hdvd)
    have hge3 : 3 ≤ I.index := by omega
    rw [hcard] at hmul
    nlinarith
  set Yf := (Y : Set Γ).toFinset with hYf
  let Vf : Subgroup Γ → Finset Γ := fun V => ((Y ⊓ V : Subgroup Γ) : Set Γ).toFinset
  have hsubF : Yf.erase 1 ⊆ Vs.toFinset.biUnion fun V => (Vf V).erase 1 := by
    intro g hg
    obtain ⟨hg1, hgY⟩ := Finset.mem_erase.mp hg
    rw [hYf, Set.mem_toFinset] at hgY
    obtain ⟨V, hV, hgV⟩ := hsub g hgY
    refine Finset.mem_biUnion.mpr ⟨V, List.mem_toFinset.mpr hV, Finset.mem_erase.mpr ⟨hg1, ?_⟩⟩
    rw [Set.mem_toFinset]
    exact ⟨hgY, hgV⟩
  have hcardY : Yf.card = Nat.card Y := by
    rw [hYf, Set.toFinset_card, ← Nat.card_eq_fintype_card]; rfl
  have hcardV : ∀ V, (Vf V).card = Nat.card ↥(Y ⊓ V) := by
    intro V; rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]; rfl
  have h1Y : (1 : Γ) ∈ Yf := by rw [hYf, Set.mem_toFinset]; exact Y.one_mem
  have hA := Finset.card_le_card hsubF
  rw [Finset.card_erase_of_mem h1Y, hcardY] at hA
  have hB := Finset.card_biUnion_le (s := Vs.toFinset) (t := fun V => (Vf V).erase 1)
  set q := Nat.card Y / 3 with hq
  have hC : ∀ V ∈ Vs.toFinset, ((Vf V).erase 1).card ≤ q - 1 := by
    intro V hV
    have h1V : (1 : Γ) ∈ Vf V := by
      rw [Set.mem_toFinset]; exact (Y ⊓ V).one_mem
    rw [Finset.card_erase_of_mem h1V, hcardV]
    have := h3 V (List.mem_toFinset.mp hV)
    omega
  have hD := Finset.sum_le_card_nsmul _ _ _ hC
  have hE : Vs.toFinset.card ≤ 3 := (List.toFinset_card_le Vs).trans hk
  obtain ⟨V0, hV0, -⟩ := hsub 1 Y.one_mem
  have hF := h3 V0 hV0
  have hG : 1 ≤ Nat.card ↥(Y ⊓ V0) := Nat.card_pos
  simp only [smul_eq_mul] at hD
  have hH : Vs.toFinset.card * (q - 1) ≤ 3 * (q - 1) := Nat.mul_le_mul_right _ hE
  omega

theorem closed_of_closedOK {B : List ℕ} (hB : ∀ b ∈ B, b < n)
    (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1) (G : Array (Array ℕ)) (L : List Γ)
    (hlen : L.length = G.size) (par lab : Array ℕ) (N : ℕ)
    (hG : ∀ t < G.size, ∀ p < n, img (G.getD t #[]) p = act n (L.getD t 1) p)
    (hok : enumOK N G par lab = true) (hcl : closedOK n B G par lab N = true) :
    ∀ k < N, ∀ s ∈ L, ∃ k' < N, enumElt L par lab k' = s * enumElt L par lab k := by
  intro k hk s hs
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hs
  unfold closedOK at hcl
  simp only [List.all_eq_true, List.mem_range] at hcl
  have h := hcl k hk t (hlen ▸ ht)
  unfold closedStep at h
  split at h
  · rename_i k' _
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨hk', hrow⟩ := h
    refine ⟨k', hk', eq_of_base hB hbase fun p hp => ?_⟩
    unfold rowOf at hrow
    rw [rows_spec hB G L par lab N hG hok hk, rows_spec hB G L par lab N hG hok hk',
      List.map_map] at hrow
    have hpt := (List.map_inj_left.mp hrow) p hp
    simp only [Function.comp_apply] at hpt
    have hq := act_lt (enumElt L par lab k) (hB p hp)
    rw [← hpt, hG t (hlen ▸ ht) _ hq, act_mul _ _ (hB p hp), List.getD_eq_getElem _ _ ht]
  · exact absurd h Bool.false_ne_true

theorem card_of_chkR [Finite Γ] (D : DcData) [MulAction Γ (Fin D.n)] (rg : List Γ)
    (hbase : ∀ g : Γ, (∀ p ∈ D.B, act D.n g p = p) → g = 1) (hB : ∀ b ∈ D.B, b < D.n)
    (hRTs : D.RT.size = rg.length)
    (hG : ∀ t < D.RT.size, ∀ p < D.n, img (D.RT.getD t #[]) p = act D.n (rg.getD t 1) p)
    (c2 : D.chkR = true) : Nat.card (Subgroup.closure {x | x ∈ rg}) = D.NR := by
  simp only [DcData.chkR, Bool.and_eq_true, decide_eq_true_eq] at c2
  obtain ⟨⟨⟨hokR, hdistR⟩, hclR⟩, hposR⟩ := c2
  have hrK : D.rKeys =
      (List.range D.NR).map fun k => keyOf D.n D.B (enumElt rg D.rpar D.rlab k) :=
    rowKeys_eq hB D.RT rg D.rpar D.rlab D.NR hG hokR
  have hinjR := inj_of_nodup (hrK ▸ distinctNat_nodup hdistR)
  exact (enum_closure rg _ D.NR hposR (enumElt_zero _ _ _) (enumElt_mem rg D.rpar D.rlab) hinjR
    (closed_of_closedOK hB hbase D.RT rg hRTs.symm D.rpar D.rlab D.NR hG hokR hclR)).2

theorem getD_mem_toList {α : Type*} {a : Array α} {i : ℕ} (h : i < a.size) (d : α) :
    a.getD i d ∈ a.toList := by
  rw [Array.mem_toList_iff, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h,
    Option.getD_some]
  exact Array.getElem_mem h

@[expose] def xs (a b : Γ) (D : DcData) (j : ℕ) : Γ := wAB a b (D.reps.getD j [])

@[expose] def vGens (a b : Γ) (rg : List Γ) (ws : List (List ℕ)) : List Γ :=
  rg ++ ws.map (wAB a b)

theorem img_X {D : DcData} [MulAction Γ (Fin D.n)] {a b : Γ} (hAB : ABOK D.n D.AB a b)
    (hreps : ∀ w ∈ D.reps.toList, ∀ l ∈ w, l < 4) (j : ℕ) {p : ℕ} (hp : p < D.n) :
    img (D.X j) p = act D.n (xs a b D j) p ∧ img (D.Xi j) p = act D.n (xs a b D j)⁻¹ p := by
  have hw : ∀ l ∈ D.reps.getD j [], l < 4 := by
    intro l hl
    rw [Array.getD_eq_getD_getElem?] at hl
    cases h : D.reps[j]? with
    | none => simp [h] at hl
    | some w =>
      rw [h, Option.getD_some] at hl
      exact hreps w (Array.mem_toList_iff.mpr (Array.mem_of_getElem? h)) l hl
  refine ⟨?_, ?_⟩
  · rw [DcData.X, img_tabW _ _ hp]
    exact act_wAB hAB hw hp
  · rw [DcData.Xi, img_tabW _ _ hp]
    exact act_wAB_inv hAB hw hp

theorem img_VG {D : DcData} [MulAction Γ (Fin D.n)] {a b : Γ} {rg : List Γ}
    (hAB : ABOK D.n D.AB a b) (hRT : RTOK D.n D.RT D.RTi rg) (ws : List (List ℕ))
    (hws : ∀ w ∈ ws, ∀ l ∈ w, l < 4) {t : ℕ} (ht : t < (D.VG ws).size) {p : ℕ} (hp : p < D.n) :
    img ((D.VG ws).getD t #[]) p = act D.n ((vGens a b rg ws).getD t 1) p := by
  obtain ⟨h1, -, h3⟩ := hRT
  unfold DcData.VG at ht ⊢
  unfold vGens
  by_cases c : t < D.RT.size
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_append_left c, ← Array.getD_eq_getD_getElem?,
      List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
      ← List.getD_eq_getElem?_getD]
    exact (h3 t (by omega) p hp).1
  · have hsz : (D.RT ++ (ws.map (tabW D.n D.AB)).toArray).size = D.RT.size + ws.length := by
      simp
    rw [hsz] at ht
    have hj : t - D.RT.size < ws.length := by omega
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_append_right (by omega),
      List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), ← h1]
    simp only [List.getElem?_toArray, List.getElem?_map, List.getElem?_eq_getElem hj,
      Option.map_some, Option.getD_some]
    rw [img_tabW _ _ hp]
    exact act_wAB hAB (hws _ (List.getElem_mem hj)) hp

theorem dc_main_le [Finite Γ] (D : DcData) [MulAction Γ (Fin D.n)] (a b : Γ) (rg : List Γ)
    (hbase : ∀ g : Γ, (∀ p ∈ D.B, act D.n g p = p) → g = 1)
    (hAB : ABOK D.n D.AB a b) (hRT : RTOK D.n D.RT D.RTi rg)
    (horder : Nat.card Γ = D.order) (hodd : ¬ 2 ∣ (Subgroup.closure {x | x ∈ rg}).index)
    (c1 : D.chkBasic = true) (c2 : D.chkR = true) (c3 : D.chkLab = true)
    (c4 : D.chkDist = true) (c5 : D.chkEdges = true) (c6 : D.chkVs = true)
    (c7 : D.chkMass = true) :
    ∀ Y : Subgroup Γ, Subgroup.closure {x | x ∈ rg} ≤ Y → Y ≠ ⊤ →
      ∃ V ∈ D.Vs, Y ≤ Subgroup.closure {x | x ∈ vGens a b rg V.1} ∧
        Nat.card (Subgroup.closure {x | x ∈ vGens a b rg V.1}) = V.2.2.2 ∧
        (∀ g ∈ Subgroup.closure {x | x ∈ vGens a b rg V.1},
          ∃ k < V.2.2.2, enumElt (vGens a b rg V.1) V.2.1 V.2.2.1 k = g) := by
  classical
  set R := Subgroup.closure {x | x ∈ rg} with hRdef
  simp only [DcData.chkBasic, Bool.and_eq_true, List.all_eq_true, Array.all_eq_true',
    decide_eq_true_eq, beq_iff_eq] at c1
  obtain ⟨⟨⟨⟨⟨⟨⟨hB, -⟩, -⟩, hreps⟩, hc0⟩, hreach⟩, hVlen⟩, hVw⟩ := c1
  have hRTs := hRT.1
  have hG : ∀ t < D.RT.size, ∀ p < D.n, img (D.RT.getD t #[]) p = act D.n (rg.getD t 1) p :=
    fun t ht p hp => (hRT.2.2 t (hRTs ▸ ht) p hp).1
  simp only [DcData.chkR, Bool.and_eq_true, decide_eq_true_eq] at c2
  obtain ⟨⟨⟨hokR, hdistR⟩, hclR⟩, hposR⟩ := c2
  set e := enumElt rg D.rpar D.rlab with he
  have hrK : D.rKeys = (List.range D.NR).map fun k => keyOf D.n D.B (e k) :=
    rowKeys_eq hB D.RT rg D.rpar D.rlab D.NR hG hokR
  have hinjR := inj_of_nodup (hrK ▸ distinctNat_nodup hdistR)
  obtain ⟨hsurjR, hNR⟩ := enum_closure rg e D.NR hposR (enumElt_zero _ _ _)
    (enumElt_mem rg D.rpar D.rlab) hinjR
    (closed_of_closedOK hB hbase D.RT rg hRTs.symm D.rpar D.rlab D.NR hG hokR hclR)
  have hrS : D.rSet = Std.HashSet.ofList ((List.range D.NR).map fun k => keyOf D.n D.B (e k)) := by
    rw [DcData.rSet, hrK]
  have hrepsL : ∀ w ∈ D.reps.toList, ∀ l ∈ w, l < 4 := fun w hw l hl =>
    hreps w (Array.mem_toList_iff.mp hw) l hl
  have hX : ∀ j, ∀ {p : ℕ}, p < D.n →
      img (D.X j) p = act D.n (xs a b D j) p ∧ img (D.Xi j) p = act D.n (xs a b D j)⁻¹ p :=
    fun j p hp => img_X hAB hrepsL j hp
  have hconj : ∀ i j, conjKeys D.n D.B D.RT D.rpar D.rlab D.NR (D.Xi i) (D.X j) =
      (List.range D.NR).map fun k => keyOf D.n D.B ((xs a b D i)⁻¹ * e k * xs a b D j) :=
    fun i j => conjKeys_eq hB D.RT rg D.rpar D.rlab D.NR hG hokR
      (fun p hp => (hX i hp).2) (fun p hp => (hX j hp).1)
  have hmass : ∀ j, D.massWith D.rSet j ≤ Nat.card (doubleCoset (xs a b D j) (R : Set Γ) R) := by
    intro j
    have hst := card_le_hitCount (n := D.n) e D.NR R D.B hsurjR (xs a b D j)
    rw [← hrS, ← hconj] at hst
    have := card_doubleCoset_ge R (xs a b D j) hst
    rw [hNR] at this
    exact this
  have hlab : ∀ r ∈ R, ∀ q < D.n, D.lb.getD (act D.n r q) 0 = D.lb.getD q 0 := by
    intro r hr
    refine lab_closure (fun q => D.lb.getD q 0) rg (fun s hs q hq => ?_) hr
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hs
    have h3 := c3
    simp only [DcData.chkLab, labOK, Array.all_eq_true', List.all_eq_true, beq_iff_eq] at h3
    have := h3 (D.RT.getD t #[]) (by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega)]
      exact Array.getElem_mem (by omega)) q (List.mem_range.mpr hq)
    rw [hG t (by omega) q hq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht] at this
    exact this
  have hinv : ∀ j, dcInv D.n D.lb (D.X j) =
      ((List.range D.n).map fun q =>
        wt (D.lb.getD q 0) (D.lb.getD (act D.n (xs a b D j) q) 0)).sum := by
    intro j
    have h : ∀ q ∈ List.range D.n, wt (D.lb.getD q 0) (D.lb.getD (img (D.X j) q) 0) =
        wt (D.lb.getD q 0) (D.lb.getD (act D.n (xs a b D j) q) 0) := fun q hq => by
      rw [(hX j (List.mem_range.mp hq)).1]
    unfold dcInv
    rw [List.map_congr_left h]
  have hdist : ∀ i < D.reps.size, ∀ j < D.reps.size, i < j →
      xs a b D j ∉ doubleCoset (xs a b D i) (R : Set Γ) R := by
    intro i hi j hj hij
    have h4 := c4
    simp only [DcData.chkDist, DcData.chkDistWith, List.all_eq_true, Bool.or_eq_true,
      decide_eq_true_eq, bne_iff_ne, ne_eq] at h4
    rcases h4 i (List.mem_range.mpr hi) j (List.mem_range.mpr hj) with (h | h) | h
    · omega
    · intro hmem
      obtain ⟨r1, hr1, r2, hr2, hx⟩ := mem_doubleCoset.mp hmem
      apply h
      have hl : ((List.range D.reps.size).map fun j => dcInv D.n D.lb (D.X j)).toArray.getD i 0 =
          dcInv D.n D.lb (D.X i) := by
        rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
          List.getElem?_range hi]
        rfl
      have hr : ((List.range D.reps.size).map fun j => dcInv D.n D.lb (D.X j)).toArray.getD j 0 =
          dcInv D.n D.lb (D.X j) := by
        rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
          List.getElem?_range hj]
        rfl
      rw [hl, hr, hinv, hinv, hx]
      exact (inv_eq (fun q => D.lb.getD q 0) R hlab (xs a b D i) hr1 hr2).symm
    · rw [hrS, hconj] at h
      exact not_mem_of_noHit (n := D.n) e D.NR R D.B hsurjR _ _ h
  have hdisj : ∀ i < D.reps.size, ∀ j < D.reps.size, i ≠ j →
      Disjoint (doubleCoset (xs a b D i) (R : Set Γ) R)
        (doubleCoset (xs a b D j) (R : Set Γ) R) := by
    intro i hi j hj hij
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact disjoint_of_not_mem R (hdist i hi j hj h)
    · exact (disjoint_of_not_mem R (hdist j hj i hi h)).symm
  simp only [DcData.chkEdges, Bool.and_eq_true] at c5
  obtain ⟨⟨⟨hed, hin⟩, hout⟩, hreachd⟩ := c5
  have hedge : ∀ ed ∈ D.edges.toList,
      xs a b D ed.2.1 ∈ R ⊔ Subgroup.zpowers (xs a b D ed.1) := by
    intro ed hed'
    have h := (Array.all_eq_true'.mp hed) ed (Array.mem_toList_iff.mp hed')
    simp only [edgeOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hs, hd⟩, hl⟩, hb⟩ := h
    have hws : ∀ l ∈ D.reps.getD ed.1 [], l < 4 := by
      intro l hl'
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hs, Option.getD_some] at hl'
      exact hreps _ (Array.getElem_mem hs) l hl'
    have heq : xs a b D ed.2.1 = wprod (edgeList rg (xs a b D ed.1)) ed.2.2 := by
      refine eq_of_base hB hbase fun p hp => ?_
      have := hb p hp
      have hwd : ∀ l ∈ D.reps.getD ed.2.1 [], l < 4 := by
        intro l hl'
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hd, Option.getD_some] at hl'
        exact hreps _ (Array.getElem_mem hd) l hl'
      rw [act_wAB hAB hwd (hB p hp), evalE_eq D.RT D.RTi D.AB a b rg hAB hRT _ hws ed.2.2 hl
        (hB p hp)] at this
      exact this
    rw [heq]
    exact wprod_edge_mem rg _ ed.2.2
  have hgen : ∀ i < D.reps.size, ∀ j ∈ D.reach, xs a b D j ∈ R ⊔ Subgroup.zpowers (xs a b D i) := by
    refine gen_of_trees R (xs a b D) D.reps.size D.c0 (fun s d => ∃ ed ∈ D.edges.toList, ed.1 = s ∧
      ed.2.1 = d) (fun s d ⟨ed, hed', h1, h2⟩ => h1 ▸ h2 ▸ hedge ed hed')
      (fun i => D.dIn.getD i 0) (fun j => D.dOut.getD j 0) ?_ D.reach ?_
    · intro i hi hic
      have h := List.all_eq_true.mp hin i (List.mem_range.mpr hi)
      simp only [Bool.or_eq_true, beq_iff_eq, hic, false_or, Bool.and_eq_true,
        decide_eq_true_eq] at h
      obtain ⟨⟨hidx, hsrc⟩, hlt⟩ := h
      set ed := D.edges.getD (D.inEdge.getD i 0) (0, 0, [])
      have hmem : ed ∈ D.edges.toList := getD_mem_toList hidx _
      have hedOK := (Array.all_eq_true'.mp hed) ed (Array.mem_toList_iff.mp hmem)
      simp only [edgeOK, Bool.and_eq_true, decide_eq_true_eq] at hedOK
      exact ⟨ed.2.1, hedOK.1.1.2, ⟨ed, hmem, hsrc, rfl⟩, hlt⟩
    · intro j hj hjc
      have h := List.all_eq_true.mp hout j hj
      simp only [Bool.or_eq_true, beq_iff_eq, hjc, false_or, Bool.and_eq_true,
        decide_eq_true_eq, List.contains_iff_mem] at h
      obtain ⟨⟨⟨hidx, hdst⟩, hsr⟩, hlt⟩ := h
      set ed := D.edges.getD (D.outEdge.getD j 0) (0, 0, [])
      have hmem : ed ∈ D.edges.toList := getD_mem_toList hidx _
      exact ⟨ed.1, hsr, ⟨ed, hmem, rfl, hdst⟩, hlt⟩
  simp only [DcData.chkMass, DcData.chkMassWith, Bool.and_eq_true, decide_eq_true_eq] at c7
  obtain ⟨hbig, htot⟩ := c7
  set M := D.massWith D.rSet with hMdef
  have hms : ∀ j < D.reps.size, ((List.range D.reps.size).map M).toArray.getD j 0 = M j := by
    intro j hj
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
      List.getElem?_range hj]
    rfl
  have hreachm : ∀ j ∈ D.reach, j < D.reps.size := hreach
  have hbig' : D.order < 2 * (D.reach.map M).sum := by
    have : D.reach.map (fun j => ((List.range D.reps.size).map M).toArray.getD j 0) =
        D.reach.map M := List.map_congr_left fun j hj => hms j (hreachm j hj)
    rwa [this] at hbig
  have htop : ∀ i < D.reps.size, R ⊔ Subgroup.zpowers (xs a b D i) = ⊤ := by
    intro i hi
    refine eq_top_of_mass le_sup_left (xs a b D) D.reach (distinctNat_nodup hreachd)
      (hgen i hi) (fun i' hi' j' hj' h => hdisj i' (hreachm i' hi') j' (hreachm j' hj') h)
      (D.massWith D.rSet) (fun j _ => hmass j) ?_
    rw [horder]; exact hbig'
  let VV : List (List ℕ) × Array ℕ × Array ℕ × ℕ → Subgroup Γ := fun V =>
    Subgroup.closure {x | x ∈ vGens a b rg V.1}
  simp only [DcData.chkVs, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at c6
  have hV : ∀ V ∈ D.Vs, (∀ g ∈ VV V, ∃ k < V.2.2.2, enumElt (vGens a b rg V.1) V.2.1 V.2.2.1 k = g)
      ∧ Nat.card (VV V) = V.2.2.2 ∧ R ≤ VV V ∧ VV V ≠ ⊤ ∧
      IsEnum (keyOf D.n D.B) (VV V : Set Γ) (D.vKeys V) := by
    intro V hVm
    obtain ⟨⟨⟨⟨hok, hdV⟩, hcl⟩, hpos⟩, hlt⟩ := c6 V hVm
    have hws : ∀ w ∈ V.1, ∀ l ∈ w, l < 4 := hVw V hVm
    have hGV : ∀ t < (D.VG V.1).size, ∀ p < D.n,
        img ((D.VG V.1).getD t #[]) p = act D.n ((vGens a b rg V.1).getD t 1) p :=
      fun t ht p hp => img_VG hAB hRT V.1 hws ht hp
    have hlen : (vGens a b rg V.1).length = (D.VG V.1).size := by
      simp [vGens, DcData.VG, hRTs]
    set eV := enumElt (vGens a b rg V.1) V.2.1 V.2.2.1
    have hkeys : D.vKeys V = (List.range V.2.2.2).map fun k => keyOf D.n D.B (eV k) :=
      rowKeys_eq hB (D.VG V.1) _ V.2.1 V.2.2.1 V.2.2.2 hGV hok
    have hinjV := inj_of_nodup (hkeys ▸ distinctNat_nodup hdV)
    have hclV := closed_of_closedOK hB hbase (D.VG V.1) (vGens a b rg V.1) hlen V.2.1 V.2.2.1
      V.2.2.2 hGV hok hcl
    have he0 : eV 0 = 1 := enumElt_zero _ _ _
    obtain ⟨hsurjV, hcardV⟩ := enum_closure (vGens a b rg V.1) eV V.2.2.2 hpos he0
      (enumElt_mem _ _ _) hinjV hclV
    refine ⟨hsurjV, hcardV, ?_, ?_, ?_⟩
    · exact Subgroup.closure_mono (fun x hx => List.mem_append_left _ hx)
    · intro htop'
      have h1 : Nat.card (VV V) = Nat.card Γ := by rw [htop']; exact Subgroup.card_top
      have h2 : Nat.card (VV V) = V.2.2.2 := hcardV
      omega
    · exact ⟨V.2.2.2, eV, hkeys, hinjV, fun k _ => enumElt_mem _ _ _ k, hsurjV⟩
  set Ws := D.Vs.map fun V => ((VV V : Set Γ), D.vKeys V) with hWs
  have hU := unionLB_le (keyOf D.n D.B) Ws (by
    intro W hW
    obtain ⟨V, hV', rfl⟩ := List.mem_map.mp hW
    exact (hV V hV').2.2.2.2)
  have hWs2 : Ws.map Prod.snd = D.Vs.map D.vKeys := by
    simp [hWs, List.map_map, Function.comp_def]
  rw [hWs2] at hU
  have hA := mass_le_card R (xs a b D) (List.range D.reps.size) List.nodup_range
    (fun i hi j hj h => hdisj i (List.mem_range.mp hi) j (List.mem_range.mp hj) h) M
    (fun j _ => hmass j)
  set U := ⋃ W ∈ Ws, W.1 with hUdef
  set A := ⋃ j ∈ List.range D.reps.size, doubleCoset (xs a b D j) (R : Set Γ) R with hAdef
  have hAU : Disjoint A U := by
    rw [Set.disjoint_left]
    intro g hgA hgU
    rw [hAdef, Set.mem_iUnion₂] at hgA
    obtain ⟨j, hj, hgj⟩ := hgA
    rw [hUdef, Set.mem_iUnion₂] at hgU
    obtain ⟨W, hW, hgW⟩ := hgU
    obtain ⟨V, hVm, rfl⟩ := List.mem_map.mp hW
    obtain ⟨-, -, hRV, hne, -⟩ := hV V hVm
    obtain ⟨r1, hr1, r2, hr2, rfl⟩ := mem_doubleCoset.mp hgj
    have hx : xs a b D j ∈ VV V := by
      have := (VV V).mul_mem ((VV V).mul_mem ((VV V).inv_mem (hRV hr1)) hgW)
        ((VV V).inv_mem (hRV hr2))
      simpa [mul_assoc] using this
    apply hne
    rw [eq_top_iff, ← htop j (List.mem_range.mp hj)]
    exact sup_le hRV (Subgroup.zpowers_le.mpr hx)
  have hcover : A ∪ U = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _) _ (Set.toFinite _)
    rw [Set.ncard_univ, Set.ncard_union_eq hAU (Set.toFinite _) (Set.toFinite _), horder]
    have htot' : D.order ≤ ((List.range D.reps.size).map (D.massWith D.rSet)).sum +
        unionLB (D.Vs.map D.vKeys) := by simpa using htot
    omega
  intro Y hRY hY
  have hsub : ∀ g ∈ Y, ∃ V ∈ D.Vs.map VV, g ∈ V := by
    intro g hg
    have hg' : g ∈ A ∪ U := by rw [hcover]; trivial
    rcases hg' with hgA | hgU
    · exfalso
      rw [hAdef, Set.mem_iUnion₂] at hgA
      obtain ⟨j, hj, hgj⟩ := hgA
      obtain ⟨r1, hr1, r2, hr2, rfl⟩ := mem_doubleCoset.mp hgj
      have hx : xs a b D j ∈ Y := by
        have := Y.mul_mem (Y.mul_mem (Y.inv_mem (hRY hr1)) hg) (Y.inv_mem (hRY hr2))
        simpa [mul_assoc] using this
      apply hY
      rw [eq_top_iff, ← htop j (List.mem_range.mp hj)]
      exact sup_le hRY (Subgroup.zpowers_le.mpr hx)
    · rw [hUdef, Set.mem_iUnion₂] at hgU
      obtain ⟨W, hW, hgW⟩ := hgU
      obtain ⟨V, hVm, rfl⟩ := List.mem_map.mp hW
      exact ⟨VV V, List.mem_map.mpr ⟨V, hVm, rfl⟩, hgW⟩
  have hoddY : ¬ 2 ∣ (R.subgroupOf Y).index := fun h2 =>
    hodd (h2.trans (Subgroup.relIndex_dvd_index_of_le hRY))
  obtain ⟨W, hWm, hYW⟩ := le_of_subset_union (D.Vs.map VV) (by simpa using hVlen) hRY
    (fun W hW => by
      obtain ⟨V, hV', rfl⟩ := List.mem_map.mp hW
      exact (hV V hV').2.2.1) hoddY hsub
  obtain ⟨V, hVm, rfl⟩ := List.mem_map.mp hWm
  exact ⟨V, hVm, hYW, (hV V hVm).2.1, (hV V hVm).1⟩

theorem dc_main [Finite Γ] (D : DcData) [MulAction Γ (Fin D.n)] (a b : Γ) (rg : List Γ)
    (hbase : ∀ g : Γ, (∀ p ∈ D.B, act D.n g p = p) → g = 1)
    (hAB : ABOK D.n D.AB a b) (hRT : RTOK D.n D.RT D.RTi rg)
    (horder : Nat.card Γ = D.order) (hodd : ¬ 2 ∣ (Subgroup.closure {x | x ∈ rg}).index)
    (c1 : D.chkBasic = true) (c2 : D.chkR = true) (c3 : D.chkLab = true)
    (c4 : D.chkDist = true) (c5 : D.chkEdges = true) (c6 : D.chkVs = true)
    (c7 : D.chkMass = true) :
    ∀ Y : Subgroup Γ, Subgroup.closure {x | x ∈ rg} ≤ Y → Y ≠ ⊤ →
      ∃ V ∈ D.Vs, Nat.card Y ∣ V.2.2.2 := by
  intro Y hRY hY
  obtain ⟨V, hV, hYV, hcard, -⟩ :=
    dc_main_le D a b rg hbase hAB hRT horder hodd c1 c2 c3 c4 c5 c6 c7 Y hRY hY
  exact ⟨V, hV, hcard ▸ Subgroup.card_dvd_of_le hYV⟩

end CFSG.Quasithin.H13.LocDbl.Dc
