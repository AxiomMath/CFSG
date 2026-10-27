module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusTabs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
public import CFSG.YGroups.Y443.Native.Hom

public section

namespace CFSG.StandardType.GGQ2Frame.ExcRaw

open Module

noncomputable section

variable {m : Fin 6} {T : Chk.Tabs}

private theorem ec_nat_all_eq_true {n : ℕ} {f : (i : ℕ) → i < n → Bool} :
    Nat.all n f = true ↔ ∀ (i : ℕ) (h : i < n), f i h = true := by
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · rintro h i hi
    exact h ⟨i, hi⟩ (List.mem_finRange ⟨i, hi⟩)
  · rintro h ⟨i, hi⟩ _
    exact h i hi

private theorem ec_nat_repeat_zero {α : Type*} (f : α → α) (a : α) :
    Nat.repeat f 0 a = a := by simp [Nat.repeat]

private theorem ec_nat_repeat_succ {α : Type*} (f : α → α) (n : ℕ) (a : α) :
    Nat.repeat f (n + 1) a = f (Nat.repeat f n a) := by simp [Nat.repeat]

private theorem ec_testBit_one_shiftLeft {a b : ℕ} :
    (1 <<< a).testBit b = true ↔ a = b := by
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq]

private theorem ec_testBit_trunc_of_lt {r c t : ℕ} (ht : t < r) :
    (Chk.trunc r c).testBit t = c.testBit t := by
  rw [Chk.trunc, Nat.testBit_land, Nat.testBit_two_pow_sub_one]
  simp [ht]

private theorem ec_testBit_trunc_of_le {r c t : ℕ} (ht : r ≤ t) :
    (Chk.trunc r c).testBit t = false := by
  rw [Chk.trunc, Nat.testBit_land, Nat.testBit_two_pow_sub_one]
  simp [Nat.not_lt.mpr ht]

private theorem ec_subN_eq {a b : ℕ} : Chk.subN a b = true ↔ a &&& b = a := by
  simp [Chk.subN, beq_iff_eq]

private theorem ec_testBit_of_subN {a b t : ℕ} (h : Chk.subN a b = true)
    (ht : a.testBit t = true) : b.testBit t = true := by
  rw [ec_subN_eq] at h
  have hb : (a &&& b).testBit t = true := by rw [h]; exact ht
  rwa [Nat.testBit_land, ht, Bool.true_and] at hb

private theorem ec_zmod_eq_of_sub_emod {a b : ℤ} (h : (a - b) % 3 = 0) :
    (a : ZMod 3) = (b : ZMod 3) := by
  have hd : (3 : ℤ) ∣ a - b := Int.dvd_iff_emod_eq_zero.mpr h
  have hzero : ((a - b : ℤ) : ZMod 3) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    simpa using hd
  push_cast at hzero
  exact sub_eq_zero.mp hzero

private theorem ec_zmod_eq_zero_of_emod {x : ℤ} (h : x % 3 = 0) : (x : ZMod 3) = 0 := by
  have hd : (3 : ℤ) ∣ x := Int.dvd_iff_emod_eq_zero.mpr h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  simpa using hd

private theorem ec_zmod_ne_zero_of_emod {x : ℤ} (h : x % 3 ≠ 0) : (x : ZMod 3) ≠ 0 := by
  intro hx
  exact h (Int.dvd_iff_emod_eq_zero.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd x 3).mp hx))

private theorem ec_list_foldl_add_cast {l : List (ℕ × ℕ)} {A : ℕ → ℕ → ℤ} (k : ℕ) (s : ℤ) :
    ((l.foldl (fun s e => s + (e.2 : ℤ) * A e.1 k) s : ℤ) : ZMod 3) =
      (s : ZMod 3) + (l.map (fun e => (e.2 : ZMod 3) * (A e.1 k : ZMod 3))).sum := by
  induction l generalizing s with
  | nil => simp
  | cons e l ih =>
    rw [List.foldl_cons, List.map_cons, List.sum_cons, ih]
    push_cast
    ring

theorem lineOK_rows (hT : Chk.tabsOK m T = true) {rows : List ℕ} {cz : ℕ} {B : Array (Array ℤ)}
    (h : Chk.lineOK T (dim m) (nroots m) rows cz B = true) {t : ℕ} (ht : t ∈ rows) :
    ∃ h : t < nroots m, root m ⟨t, h⟩ (vec m cz) = 0 := by
  have h' := h
  simp only [Chk.lineOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h'
  have hcz : cz < 3 ^ dim m := h'.1.1.1.1
  have hrows : (rows.all fun t => decide (t < nroots m) && (T.zm[cz]!).testBit t) = true :=
    h'.1.2
  obtain ⟨-, hbit⟩ := (Bool.and_eq_true _ _).mp (List.all_eq_true.mp hrows t ht)
  exact (tabsOK_zm hT hcz t).mp hbit

private theorem ec_pivN_find {d c : ℕ} (h : Chk.pivN d c < d) :
    (List.range d).find? (fun k => Chk.dig c k != 0) = some (Chk.pivN d c) := by
  have hne : (List.range d).find? (fun k => Chk.dig c k != 0) ≠ none := by
    intro hn
    have hpd : Chk.pivN d c = d := by simp [Chk.pivN, hn]
    omega
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hne
  have hpa : Chk.pivN d c = a := by simp [Chk.pivN, ha]
  rw [ha, ← hpa]

private theorem ec_pivN_dig_ne_zero {d c : ℕ} (h : Chk.pivN d c < d) :
    Chk.dig c (Chk.pivN d c) ≠ 0 := by
  have := List.find?_some (ec_pivN_find h)
  rwa [bne_iff_ne] at this

private theorem ec_dig_cast_ne_zero {c p : ℕ} (h : Chk.dig c p ≠ 0) :
    (Chk.dig c p : ZMod 3) ≠ 0 := by
  intro hz
  have hlt : Chk.dig c p < 3 := Nat.mod_lt _ (by norm_num)
  have hcases : Chk.dig c p = 0 ∨ Chk.dig c p = 1 ∨ Chk.dig c p = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · exact absurd h0 h
  · rw [h1] at hz; exact absurd hz (by decide)
  · rw [h2] at hz; exact absurd hz (by decide)

private theorem ec_line_BΦ {rows : List ℕ} {p : ℕ} {B : Array (Array ℤ)}
    (hb : Nat.all (dim m) (fun i _ => Nat.all (dim m) fun j _ =>
      (Nat.fold (dim m) (fun k _ s => s + (B[i]!)[k]! * Chk.phiN T (dim m) p rows k j) 0 -
        (if i = j then 1 else 0)) % 3 == 0) = true) :
    (Matrix.of fun i j : Fin (dim m) =>
        (((B[i.val]!)[j.val]! : ℤ) : ZMod 3)) *
      (Matrix.of fun i j : Fin (dim m) =>
        ((Chk.phiN T (dim m) p rows i.val j.val : ℤ) : ZMod 3)) = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.of_apply]
  have h1 := ec_nat_all_eq_true.mp hb i.val i.isLt
  have h2 := ec_nat_all_eq_true.mp h1 j.val j.isLt
  rw [beq_iff_eq] at h2
  have hcast := ec_zmod_eq_of_sub_emod h2
  push_cast at hcast
  have hδ : (if (i : ℕ) = (j : ℕ) then (1 : ZMod 3) else 0) = if i = j then 1 else 0 := by
    by_cases h : i = j
    · subst h; simp
    · have h' : (i : ℕ) ≠ (j : ℕ) := fun hh => h (Fin.ext hh)
      simp [h, h']
  rw [hδ] at hcast
  have hsum : (∑ l : Fin (dim m),
        (((B[i.val]!)[l.val]! : ℤ) : ZMod 3) *
          ((Chk.phiN T (dim m) p rows l.val j.val : ℤ) : ZMod 3)) =
      ((Nat.fold (dim m) (fun k _ s => s + (B[i.val]!)[k]! *
        Chk.phiN T (dim m) p rows k j.val) 0 : ℤ) : ZMod 3) := by
    rw [nat_fold_add]
    push_cast
    rfl
  rw [hsum]
  exact hcast

private theorem ec_line_Phi_mulVec {rows : List ℕ} {p : ℕ} {w : V m}
    (hT : Chk.tabsOK m T = true) (hlen : rows.length + 1 = dim m) (hp : p < dim m)
    (hwp : w ⟨p, hp⟩ = 0)
    (hrows : ∀ t ∈ rows, ∃ h : t < nroots m, root m ⟨t, h⟩ w = 0) :
    (Matrix.of fun i j : Fin (dim m) =>
        ((Chk.phiN T (dim m) p rows i.val j.val : ℤ) : ZMod 3)).mulVec w = 0 := by
  funext i
  change (Matrix.of fun i j : Fin (dim m) =>
    ((Chk.phiN T (dim m) p rows i.val j.val : ℤ) : ZMod 3)).mulVec w i = 0
  rw [Matrix.mulVec, dotProduct]
  simp only [Matrix.of_apply]
  by_cases hi : i.val + 1 < dim m
  · have hik : i.val < rows.length := by omega
    obtain ⟨hrow, hrowz⟩ := hrows (rows[i.val]) (List.getElem_mem hik)
    have hroot : (∑ j : Fin (dim m),
        ((Chk.phiN T (dim m) p rows i.val j.val : ℤ) : ZMod 3) * w j) =
        root m ⟨rows[i.val], hrow⟩ w := by
      rw [root_apply]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Chk.phiN, if_pos hi]
      have hget : rows.getD i.val 0 = rows[i.val] := List.getD_eq_getElem rows 0 hik
      rw [hget, tabsOK_f hT ⟨rows[i.val], hrow⟩ j]
    rw [hroot, hrowz]
  · have hid : i.val + 1 = dim m := by omega
    rw [Finset.sum_eq_single (a := ⟨p, hp⟩)]
    · simp only [Chk.phiN, if_neg hi]
      simp [hwp]
    · intro b _ hb
      simp only [Chk.phiN, if_neg hi]
      have hbp : b.val ≠ p := fun h => hb (Fin.ext h)
      simp [hbp]
    · intro hpnot
      exact absurd (Finset.mem_univ _) hpnot

private theorem ec_line_forward (hT : Chk.tabsOK m T = true) {rows : List ℕ} {cz : ℕ}
    {B : Array (Array ℤ)} (h : Chk.lineOK T (dim m) (nroots m) rows cz B = true)
    {v : V m} (hv : ∀ t : Root m, t.val ∈ rows → root m t v = 0) :
    v ∈ Submodule.span (ZMod 3) {vec m cz} := by
  have h' := h
  simp only [Chk.lineOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h'
  have hp : Chk.pivN (dim m) cz < dim m := h'.1.1.1.2
  have hlen : rows.length + 1 = dim m := h'.1.1.2
  have hB : Nat.all (dim m) (fun i _ => Nat.all (dim m) fun j _ =>
      (Nat.fold (dim m) (fun k _ s => s + (B[i]!)[k]! *
        Chk.phiN T (dim m) (Chk.pivN (dim m) cz) rows k j) 0 -
        (if i = j then 1 else 0)) % 3 == 0) = true := h'.2
  let p := Chk.pivN (dim m) cz
  have hp' : p < dim m := hp
  have hdig : Chk.dig cz p ≠ 0 := ec_pivN_dig_ne_zero hp'
  let z : V m := vec m cz
  let c : ZMod 3 := v ⟨p, hp'⟩ * (z ⟨p, hp'⟩)⁻¹
  let w : V m := v - c • z
  have hzp : z ⟨p, hp'⟩ ≠ 0 := by
    have hz : z ⟨p, hp'⟩ = (Chk.dig cz p : ZMod 3) := rfl
    rw [hz]
    exact ec_dig_cast_ne_zero hdig
  have hwp : w ⟨p, hp'⟩ = 0 := by
    simp only [w, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, c]
    field_simp [hzp]
    ring
  have hwrows : ∀ t ∈ rows, ∃ hh : t < nroots m, root m ⟨t, hh⟩ w = 0 := by
    intro t ht
    obtain ⟨hh, hz0⟩ := lineOK_rows hT h ht
    refine ⟨hh, ?_⟩
    change root m ⟨t, hh⟩ (v - c • z) = 0
    rw [map_sub, map_smul, hv ⟨t, hh⟩ ht, hz0, smul_zero]
    exact sub_self (0 : ZMod 3)
  let B' : Matrix (Fin (dim m)) (Fin (dim m)) (ZMod 3) :=
    Matrix.of fun i j => (((B[i.val]!)[j.val]! : ℤ) : ZMod 3)
  let Φ : Matrix (Fin (dim m)) (Fin (dim m)) (ZMod 3) :=
    Matrix.of fun i j => ((Chk.phiN T (dim m) p rows i.val j.val : ℤ) : ZMod 3)
  have hΦ : Φ.mulVec w = 0 := ec_line_Phi_mulVec hT hlen hp' hwp hwrows
  have hBΦ : B' * Φ = 1 := ec_line_BΦ (T := T) (p := p) hB
  have hwzero : w = 0 := by
    have h1 : w = (B' * Φ).mulVec w := by rw [hBΦ, Matrix.one_mulVec]
    have h2 : (B' * Φ).mulVec w = 0 := by
      rw [← Matrix.mulVec_mulVec, hΦ]
      simp
    rw [h1, h2]
  have hweq : v - c • z = 0 := hwzero
  have hv_eq : v = c • z := sub_eq_zero.mp hweq
  have hzdef : z = vec m cz := rfl
  rw [hv_eq, hzdef]
  exact Submodule.mem_span_singleton.mpr ⟨c, rfl⟩

private theorem ec_line_backward (hT : Chk.tabsOK m T = true) {rows : List ℕ} {cz : ℕ}
    {B : Array (Array ℤ)} (h : Chk.lineOK T (dim m) (nroots m) rows cz B = true)
    {v : V m} (hv : v ∈ Submodule.span (ZMod 3) {vec m cz}) :
    ∀ t : Root m, t.val ∈ rows → root m t v = 0 := by
  intro t ht
  obtain ⟨hh, hz0⟩ := lineOK_rows hT h ht
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hv
  rw [← ha, map_smul]
  have hz0' : root m t (vec m cz) = 0 := by simpa using hz0
  rw [hz0', smul_zero]

theorem lineOK_sound (hT : Chk.tabsOK m T = true) {rows : List ℕ} {cz : ℕ} {B : Array (Array ℤ)}
    (h : Chk.lineOK T (dim m) (nroots m) rows cz B = true) (v : V m) :
    (∀ t : Root m, t.val ∈ rows → root m t v = 0) ↔ v ∈ Submodule.span (ZMod 3) {vec m cz} := by
  constructor
  · intro hv
    exact ec_line_forward hT h hv
  · intro hv t ht
    exact ec_line_backward hT h hv t ht
theorem inOK_sound (hT : Chk.tabsOK m T = true) {c cv : ℕ} {coef : List (ℕ × ℕ)}
    (h : Chk.inOK T (dim m) (nroots m) c coef cv = true) : vec m cv ∈ inside m (ofMask m c) := by
  have h' := h
  simp only [Chk.inOK, Bool.and_eq_true] at h'
  have hcoef : (coef.all fun e => decide (e.1 < nroots m) && c.testBit e.1) = true := h'.1
  have hcoord := h'.2
  have hall := List.all_eq_true.mp hcoef
  have hlt : ∀ e ∈ coef, e.1 < nroots m := fun e he =>
    of_decide_eq_true ((Bool.and_eq_true _ _).mp (hall e he)).1
  have hbit : ∀ e ∈ coef, c.testBit e.1 = true := fun e he =>
    ((Bool.and_eq_true _ _).mp (hall e he)).2
  let term : ℕ × ℕ → V m := fun e =>
    if h : e.1 < nroots m then (e.2 : ZMod 3) • coroot m ⟨e.1, h⟩ else 0
  have hmem_aux : ∀ (l : List (ℕ × ℕ)),
      (∀ e ∈ l, e.1 < nroots m) → (∀ e ∈ l, c.testBit e.1 = true) →
      (l.map term).sum ∈ inside m (ofMask m c) := by
    intro l
    induction l with
    | nil => intro _ _; simp
    | cons e l ih =>
      intro hltl hbitl
      rw [List.map_cons, List.sum_cons]
      refine Submodule.add_mem _ ?_ (ih (fun x hx => hltl x (List.mem_cons_of_mem e hx))
        (fun x hx => hbitl x (List.mem_cons_of_mem e hx)))
      rw [show term e = (e.2 : ZMod 3) • coroot m ⟨e.1, hltl e List.mem_cons_self⟩ from
        dif_pos (hltl e List.mem_cons_self)]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      exact ⟨⟨e.1, hltl e List.mem_cons_self⟩,
        mem_ofMask.mpr (hbitl e List.mem_cons_self), rfl⟩
  have hcoord_aux : ∀ (l : List (ℕ × ℕ)),
      (∀ e ∈ l, e.1 < nroots m) → (∀ e ∈ l, c.testBit e.1 = true) →
      ∀ k : Fin (dim m), ((l.map term).sum) k =
        (l.map (fun e => (e.2 : ZMod 3) * ((((T.h[e.1]!)[k.val]! : ℤ)) : ZMod 3))).sum := by
    intro l
    induction l with
    | nil => intro _ _ k; simp
    | cons e l ih =>
      intro hltl hbitl k
      rw [List.map_cons, List.sum_cons, Pi.add_apply, List.map_cons, List.sum_cons,
        ih (fun x hx => hltl x (List.mem_cons_of_mem e hx))
          (fun x hx => hbitl x (List.mem_cons_of_mem e hx)) k,
        show term e = (e.2 : ZMod 3) • coroot m ⟨e.1, hltl e List.mem_cons_self⟩ from
          dif_pos (hltl e List.mem_cons_self)]
      simp only [Pi.smul_apply, smul_eq_mul, coroot,
        tabsOK_h hT ⟨e.1, hltl e List.mem_cons_self⟩ k]
  have hvec : vec m cv = (coef.map term).sum := by
    funext k
    rw [hcoord_aux coef hlt hbit k]
    have hfs : (coef.map (fun e => (e.2 : ZMod 3) *
        ((((T.h[e.1]!)[k.val]! : ℤ)) : ZMod 3))).sum =
        ((coef.foldl (fun s e => s + (e.2 : ℤ) * ((T.h[e.1]!)[k.val]! : ℤ)) 0 : ℤ) : ZMod 3) := by
      have hf := ec_list_foldl_add_cast (l := coef) (A := fun i k => (T.h[i]!)[k]!) k.val 0
      simpa using hf.symm
    rw [hfs]
    have hk := ec_nat_all_eq_true.mp hcoord k.val k.isLt
    rw [beq_iff_eq] at hk
    simp only [vec]
    exact (ec_zmod_eq_of_sub_emod hk).symm
  rw [hvec]
  exact hmem_aux coef hlt hbit

theorem outOK_sound (hT : Chk.tabsOK m T = true) {c φ cv : ℕ}
    (h : Chk.outOK T (dim m) (nroots m) c φ cv = true) : vec m cv ∉ inside m (ofMask m c) := by
  have h' := h
  simp only [Chk.outOK, Bool.and_eq_true, bne_iff_ne] at h'
  have hkill := h'.1
  have hcv := h'.2
  let ψ : V m →ₗ[ZMod 3] ZMod 3 :=
    { toFun := fun v => ∑ k, (Chk.dig φ k.val : ZMod 3) * v k
      map_add' := by
        intro v w
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro a v
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring }
  have hψ_apply : ∀ v : V m, ψ v = ∑ k : Fin (dim m),
      (Chk.dig φ k.val : ZMod 3) * v k := fun v => rfl
  have hfold_coroot : ∀ t : Root m,
      ((Nat.fold (dim m) (fun k _ s => s + (Chk.dig φ k : ℤ) * ((T.h[t.val]!)[k]! : ℤ)) 0 :
          ℤ) : ZMod 3) =
        ∑ k : Fin (dim m), (Chk.dig φ k.val : ZMod 3) *
          ((((T.h[t.val]!)[k.val]! : ℤ)) : ZMod 3) := by
    intro t
    rw [nat_fold_add]
    push_cast
    rfl
  have hψ_coroot : ∀ t : Root m, ψ (coroot m t) =
      ∑ k : Fin (dim m), (Chk.dig φ k.val : ZMod 3) *
        ((((T.h[t.val]!)[k.val]! : ℤ)) : ZMod 3) := by
    intro t
    rw [hψ_apply]
    exact Finset.sum_congr rfl fun k _ => by
      simp only [coroot]
      rw [tabsOK_h hT t k]
  have hψv : ψ (vec m cv) =
      ((Nat.fold (dim m) (fun k _ s => s + (Chk.dig φ k : ℤ) * (Chk.dig cv k : ℤ)) 0 : ℤ) :
        ZMod 3) := by
    have hfold_cv :
        ((Nat.fold (dim m) (fun k _ s => s + (Chk.dig φ k : ℤ) * (Chk.dig cv k : ℤ)) 0 : ℤ) :
            ZMod 3) =
          ∑ k : Fin (dim m), (Chk.dig φ k.val : ZMod 3) * (Chk.dig cv k.val : ZMod 3) := by
      rw [nat_fold_add]
      push_cast
      rfl
    rw [hψ_apply]
    simp only [vec]
    exact hfold_cv.symm
  have hψv_ne : ψ (vec m cv) ≠ 0 := by
    rw [hψv]
    exact ec_zmod_ne_zero_of_emod hcv
  have hkill' : ∀ t : Root m, t ∈ ofMask m c → ψ (coroot m t) = 0 := by
    intro t ht
    have htbit : c.testBit t.val = true := mem_ofMask.mp ht
    have hk := ec_nat_all_eq_true.mp hkill t.val t.isLt
    rw [Bool.or_eq_true] at hk
    have hz : (Nat.fold (dim m)
        (fun k _ s => s + (Chk.dig φ k : ℤ) * ((T.h[t.val]!)[k]! : ℤ)) 0 : ℤ) % 3 = 0 := by
      rcases hk with hbad | hgood
      · rw [htbit] at hbad
        exact absurd hbad (by simp)
      · exact beq_iff_eq.mp hgood
    calc ψ (coroot m t) =
          ((Nat.fold (dim m) (fun k _ s => s + (Chk.dig φ k : ℤ) *
            ((T.h[t.val]!)[k]! : ℤ)) 0 : ℤ) : ZMod 3) := by
            rw [hψ_coroot, ← hfold_coroot t]
      _ = 0 := ec_zmod_eq_zero_of_emod hz
  have hker : inside m (ofMask m c) ≤ LinearMap.ker ψ := by
    rw [inside, Submodule.span_le]
    rintro x ⟨i, hi, rfl⟩
    exact LinearMap.mem_ker.mpr (hkill' i hi)
  intro hv
  exact hψv_ne (LinearMap.mem_ker.mp (hker hv))

private theorem ec_adj_symm {m : Fin 6} {i j : Root m} : Adj m i j ↔ Adj m j i := by
  simp only [Adj, or_comm]

theorem growN_fold_spec {m : Fin 6} {T : Chk.Tabs} (hT : Chk.tabsOK m T = true)
    {c c' A : ℕ} (C : Finset (Root m))
    (hCc : ∀ t (ht : t < nroots m), c'.testBit t = true → (⟨t, ht⟩ : Root m) ∈ ofMask m c)
    (hclosed : ∀ i ∈ C, ∀ j ∈ ofMask m c, Adj m i j → j ∈ C)
    (hA : ∀ t (ht : t < nroots m), A.testBit t = true → (⟨t, ht⟩ : Root m) ∈ C)
    (hAhi : ∀ t, nroots m ≤ t → A.testBit t = false)
    (hchi : ∀ t, nroots m ≤ t → c'.testBit t = false) :
    ∀ n, (∀ t, nroots m ≤ t →
        (Nat.fold n (fun u _ acc => if A.testBit u then acc ||| (T.adj[u]! &&& c') else acc)
          A).testBit t = false) ∧
      (∀ t (ht : t < nroots m),
        (Nat.fold n (fun u _ acc => if A.testBit u then acc ||| (T.adj[u]! &&& c') else acc)
          A).testBit t = true → (⟨t, ht⟩ : Root m) ∈ C) := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun t ht => ?_, fun t ht hb => ?_⟩
    · rw [Nat.fold_zero]; exact hAhi t ht
    · rw [Nat.fold_zero] at hb; exact hA t ht hb
  | succ n ih =>
    rw [Nat.fold_succ]
    by_cases hAn : A.testBit n = true
    · rw [if_pos hAn]
      refine ⟨fun t ht => ?_, fun t ht hb => ?_⟩
      · rw [Nat.testBit_lor, ih.1 t ht, Nat.testBit_land, hchi t ht]
        simp
      · rw [Nat.testBit_lor, Bool.or_eq_true] at hb
        rcases hb with hb | hb
        · exact ih.2 t ht hb
        · rw [Nat.testBit_land] at hb
          obtain ⟨hadj, hc'⟩ := (Bool.and_eq_true _ _).mp hb
          have hn : n < nroots m := by
            by_contra hge
            rw [hAhi n (Nat.le_of_not_lt hge)] at hAn
            exact absurd hAn (by simp)
          have hiC : (⟨n, hn⟩ : Root m) ∈ C := hA n hn hAn
          have hjC : (⟨t, ht⟩ : Root m) ∈ ofMask m c := hCc t ht hc'
          have hadj' : Adj m ⟨n, hn⟩ ⟨t, ht⟩ :=
            (tabsOK_adj hT ⟨n, hn⟩ t).mp hadj |>.choose_spec
          exact hclosed ⟨n, hn⟩ hiC ⟨t, ht⟩ hjC hadj'
    · rw [if_neg hAn]
      exact ih

theorem growN_repeat_spec {m : Fin 6} {T : Chk.Tabs} (hT : Chk.tabsOK m T = true)
    {c c' : ℕ} (C : Finset (Root m))
    (hCc : ∀ t (ht : t < nroots m), c'.testBit t = true → (⟨t, ht⟩ : Root m) ∈ ofMask m c)
    (hclosed : ∀ i ∈ C, ∀ j ∈ ofMask m c, Adj m i j → j ∈ C)
    (start : ℕ)
    (hstart : ∀ t (ht : t < nroots m), start.testBit t = true → (⟨t, ht⟩ : Root m) ∈ C)
    (hstart_hi : ∀ t, nroots m ≤ t → start.testBit t = false)
    (hchi : ∀ t, nroots m ≤ t → c'.testBit t = false) :
    ∀ n, (∀ t, nroots m ≤ t →
        (Nat.repeat (Chk.growN T (nroots m) c') n start).testBit t = false) ∧
      (∀ t (ht : t < nroots m),
        (Nat.repeat (Chk.growN T (nroots m) c') n start).testBit t = true →
          (⟨t, ht⟩ : Root m) ∈ C) := by
  intro n
  induction n with
  | zero =>
    rw [ec_nat_repeat_zero]
    exact ⟨hstart_hi, hstart⟩
  | succ n ih =>
    rw [ec_nat_repeat_succ]
    exact growN_fold_spec hT C hCc hclosed ih.2 ih.1 hchi (nroots m)

theorem not_isComp_of_discOK (hT : Chk.tabsOK m T = true) {c S : ℕ}
    (h : Chk.discOK T (nroots m) c S = true) (P : Root m → Prop) : ¬ IsComp m P (ofMask m c) := by
  have h' := h
  simp only [Chk.discOK, Bool.or_eq_true] at h'
  rcases h' with hz | hc
  · rintro ⟨hne, -⟩
    obtain ⟨t, ht⟩ := hne
    have htbit : c.testBit t.val = true := mem_ofMask.mp ht
    have h0 : (Chk.trunc (nroots m) c).testBit t.val = true := by
      rw [ec_testBit_trunc_of_lt t.isLt]; exact htbit
    have hz0 : Chk.trunc (nroots m) c = 0 := by simpa using hz
    rw [hz0] at h0
    exact absurd h0 (by simp)
  · have hc' := hc
    simp only [Chk.closedOK, Bool.and_eq_true, bne_iff_ne] at hc'
    obtain ⟨⟨hS0, hSc⟩, hcl⟩ := hc'
    let S' : ℕ := S &&& Chk.trunc (nroots m) c
    let T' : Finset (Root m) := ofMask m S'
    have hS'def : S' = S &&& Chk.trunc (nroots m) c := rfl
    have hex : ∃ t, S'.testBit t = true := by
      by_contra hnone
      have hzero : S' = 0 := Nat.eq_of_testBit_eq fun t => by
        rw [Nat.zero_testBit]
        cases hb : S'.testBit t with
        | false => rfl
        | true => exact absurd ⟨t, hb⟩ hnone
      exact hS0 (hS'def ▸ hzero)
    have hsub : T' ⊆ ofMask m c := by
      intro i hi
      rw [mem_ofMask] at hi ⊢
      rw [hS'def, Nat.testBit_land] at hi
      have hc' : (Chk.trunc (nroots m) c).testBit i.val = true :=
        (Bool.and_eq_true _ _).mp hi |>.2
      rwa [ec_testBit_trunc_of_lt i.isLt] at hc'
    have hne : T'.Nonempty := by
      obtain ⟨t, ht⟩ := hex
      have hlt : t < nroots m := by
        by_contra hge
        have hz' : (Chk.trunc (nroots m) c).testBit t = false :=
          ec_testBit_trunc_of_le (Nat.le_of_not_lt hge)
        rw [hS'def, Nat.testBit_land, hz'] at ht
        exact absurd ht (by simp)
      exact ⟨⟨t, hlt⟩, mem_ofMask.mpr ht⟩
    have hclosed : ∀ i ∈ T', ∀ j ∈ ofMask m c, Adj m i j → j ∈ T' := by
      intro i hi j hj hadj
      have hi' : S'.testBit i.val = true := mem_ofMask.mp hi
      have hsubn : Chk.subN (T.adj[i.val]! &&& Chk.trunc (nroots m) c) S' = true := by
        have h1 := ec_nat_all_eq_true.mp hcl i.val i.isLt
        rw [Bool.or_eq_true] at h1
        rcases h1 with hbad | hgood
        · rw [hi'] at hbad
          exact absurd hbad (by simp)
        · exact hgood
      have hjbit : c.testBit j.val = true := mem_ofMask.mp hj
      have hjc' : (Chk.trunc (nroots m) c).testBit j.val = true := by
        rw [ec_testBit_trunc_of_lt j.isLt]; exact hjbit
      have hadj' : (T.adj[i.val]!).testBit j.val = true :=
        (tabsOK_adj hT i j.val).mpr ⟨j.isLt, hadj⟩
      have hbit : (T.adj[i.val]! &&& Chk.trunc (nroots m) c).testBit j.val = true := by
        rw [Nat.testBit_land, hadj', hjc']; rfl
      show j ∈ ofMask m S'
      exact mem_ofMask.mpr (ec_testBit_of_subN hsubn hbit)
    have hne_c : T' ≠ ofMask m c := by
      intro hEq
      apply hSc
      apply Nat.eq_of_testBit_eq
      intro t
      by_cases ht : t < nroots m
      · have hm := congrArg (fun F : Finset (Root m) => (⟨t, ht⟩ : Root m) ∈ F) hEq
        simp only [T', mem_ofMask] at hm
        have hm' : S'.testBit t = c.testBit t := Bool.eq_iff_iff.mpr (Iff.of_eq hm)
        rw [← hS'def, ec_testBit_trunc_of_lt ht]
        exact hm'
      · rw [← hS'def, Nat.testBit_land, ec_testBit_trunc_of_le (Nat.le_of_not_lt ht)]
        simp
    rintro ⟨-, -, -, hmax⟩
    exact hne_c (hmax T' hsub hne hclosed)

theorem connN_sound (hT : Chk.tabsOK m T = true) {c : ℕ} (h : Chk.connN T (nroots m) c = true) :
    (ofMask m c).Nonempty ∧ ∀ S ⊆ ofMask m c, S.Nonempty →
      (∀ i ∈ S, ∀ j ∈ ofMask m c, Adj m i j → j ∈ S) → S = ofMask m c := by
  have h' := h
  simp only [Chk.connN, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h'
  obtain ⟨ht0, hreach⟩ := h'
  let c' : ℕ := Chk.trunc (nroots m) c
  let t0 : ℕ := Chk.lowN (nroots m) c'
  have hreach' : Nat.repeat (Chk.growN T (nroots m) c') (nroots m) (1 <<< t0) = c' := hreach
  have ht0' : t0 < nroots m := ht0
  have hfind : (List.range (nroots m)).find? (fun t => c'.testBit t) = some t0 := by
    have hne : (List.range (nroots m)).find? (fun t => c'.testBit t) ≠ none := by
      intro hnone
      have hlt : t0 < nroots m := ht0'
      have hEq : t0 = nroots m := by simp [t0, Chk.lowN, hnone]
      rw [hEq] at hlt
      exact Nat.lt_irrefl _ hlt
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hne
    have hta : t0 = a := by simp [t0, Chk.lowN, ha]
    rw [ha, ← hta]
  have ht0bit : c'.testBit t0 = true := List.find?_some hfind
  have hchi : ∀ t, nroots m ≤ t → c'.testBit t = false := fun t ht =>
    ec_testBit_trunc_of_le ht
  have hCc : ∀ t (ht : t < nroots m), c'.testBit t = true → (⟨t, ht⟩ : Root m) ∈ ofMask m c := by
    intro t ht hb
    rw [mem_ofMask, ← ec_testBit_trunc_of_lt ht]
    exact hb
  have ht0mem : (⟨t0, ht0'⟩ : Root m) ∈ ofMask m c := hCc t0 ht0' ht0bit
  have hstart_hi : ∀ t, nroots m ≤ t → (1 <<< t0).testBit t = false := by
    intro t ht
    cases hb : (1 <<< t0).testBit t with
    | false => rfl
    | true =>
      have he : t0 = t := ec_testBit_one_shiftLeft.mp hb
      rw [← he] at ht
      exact absurd ht (Nat.not_le.mpr ht0')
  refine ⟨⟨⟨t0, ht0'⟩, ht0mem⟩, ?_⟩
  intro S hS hSne hScl
  by_cases ht0S : (⟨t0, ht0'⟩ : Root m) ∈ S
  · have hstart : ∀ t (ht : t < nroots m),
        (1 <<< t0).testBit t = true → (⟨t, ht⟩ : Root m) ∈ S := by
      intro t ht hb
      have he : t0 = t := ec_testBit_one_shiftLeft.mp hb
      have hfin : (⟨t, ht⟩ : Root m) = ⟨t0, ht0'⟩ := Fin.ext he.symm
      rw [hfin]
      exact ht0S
    have hrep := growN_repeat_spec hT S hCc hScl (1 <<< t0) hstart hstart_hi hchi
    have hc'S : ∀ t (ht : t < nroots m), c'.testBit t = true → (⟨t, ht⟩ : Root m) ∈ S := by
      intro t ht hb
      exact (hrep (nroots m)).2 t ht (by rw [hreach']; exact hb)
    refine Finset.Subset.antisymm hS ?_
    intro i hi
    rw [mem_ofMask] at hi
    exact hc'S i.val i.isLt (by rw [ec_testBit_trunc_of_lt i.isLt]; exact hi)
  · let C : Finset (Root m) := ofMask m c \ S
    have hCclosed : ∀ i ∈ C, ∀ j ∈ ofMask m c, Adj m i j → j ∈ C := by
      intro i hi j hj hadj
      rw [Finset.mem_sdiff] at hi ⊢
      refine ⟨hj, ?_⟩
      intro hjS
      exact hi.2 (hScl j hjS i hi.1 (ec_adj_symm.mp hadj))
    have hstartC : ∀ t (ht : t < nroots m),
        (1 <<< t0).testBit t = true → (⟨t, ht⟩ : Root m) ∈ C := by
      intro t ht hb
      have he : t0 = t := ec_testBit_one_shiftLeft.mp hb
      have hfin : (⟨t, ht⟩ : Root m) = ⟨t0, ht0'⟩ := Fin.ext he.symm
      have htmem : (⟨t, ht⟩ : Root m) ∈ ofMask m c := by
        rw [hfin]
        exact ht0mem
      have htnotS : (⟨t, ht⟩ : Root m) ∉ S := by
        have hfin : (⟨t, ht⟩ : Root m) = ⟨t0, ht0'⟩ := Fin.ext he.symm
        exact fun hmem => ht0S (hfin ▸ hmem)
      exact Finset.mem_sdiff.mpr ⟨htmem, htnotS⟩
    have hrep := growN_repeat_spec hT C hCc hCclosed (1 <<< t0) hstartC hstart_hi hchi
    have hc'C : ∀ t (ht : t < nroots m), c'.testBit t = true → (⟨t, ht⟩ : Root m) ∈ C := by
      intro t ht hb
      exact (hrep (nroots m)).2 t ht (by rw [hreach']; exact hb)
    obtain ⟨j, hjS⟩ := hSne
    have hjC : j ∈ C := hc'C j.val j.isLt
      (by rw [ec_testBit_trunc_of_lt j.isLt]; exact mem_ofMask.mp (hS hjS))
    rw [Finset.mem_sdiff] at hjC
    exact absurd hjS hjC.2

private theorem ec_foldl_none {L : List (ℕ × ℕ)} {g : ℕ × ℕ → ℕ → Option ℕ} :
    L.foldl (fun acc e => acc.bind (g e)) none = none := by
  induction L with
  | nil => rfl
  | cons e L ihL => rw [List.foldl_cons]; exact ihL

private theorem ec_deriv_fold_mem {m : Fin 6} {T : Chk.Tabs} (hT : Chk.tabsOK m T = true)
    {gens : ℕ} {G : Subgroup (V m ≃ₗ[ZMod 3] V m)}
    (hgens : ∀ u (hu : u < nroots m), gens.testBit u = true → reflection m ⟨u, hu⟩ ∈ G) :
    ∀ (L : List (ℕ × ℕ)) (A : ℕ),
      (∀ t (ht : t < nroots m), A.testBit t = true → reflection m ⟨t, ht⟩ ∈ G) →
      ∀ S, L.foldl (fun acc e => acc.bind fun S =>
        if decide (e.1 < nroots m) && decide (e.2 < nroots m) && gens.testBit e.1 && S.testBit e.2 then
          some (S ||| 1 <<< (T.rt[e.1]!)[e.2]!)
        else none) (some A) = some S →
      ∀ t (ht : t < nroots m), S.testBit t = true → reflection m ⟨t, ht⟩ ∈ G := by
  intro L
  induction L with
  | nil =>
    intro A hA S hS t ht hbit
    simp only [List.foldl_nil, Option.some.injEq] at hS
    rw [← hS] at hbit
    exact hA t ht hbit
  | cons e L ih =>
    intro A hA S hS
    rw [List.foldl_cons] at hS
    cases hstep : (some A).bind (fun S =>
      if decide (e.1 < nroots m) && decide (e.2 < nroots m) && gens.testBit e.1 && S.testBit e.2 then
        some (S ||| 1 <<< (T.rt[e.1]!)[e.2]!)
      else none) with
    | none =>
      rw [hstep] at hS
      rw [ec_foldl_none (g := fun e S =>
        if decide (e.1 < nroots m) && decide (e.2 < nroots m) && gens.testBit e.1 && S.testBit e.2
        then some (S ||| 1 <<< (T.rt[e.1]!)[e.2]!) else none)] at hS
      exact absurd hS (by simp)
    | some A' =>
      rw [hstep] at hS
      refine ih A' ?_ S hS
      intro t ht hbit
      by_cases hc : (decide (e.1 < nroots m) && decide (e.2 < nroots m) && gens.testBit e.1 &&
          A.testBit e.2) = true
      · have hc' := hc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc'
        obtain ⟨⟨⟨he1, he2⟩, hgensbit⟩, hAbit⟩ := hc'
        have hA' : A' = A ||| 1 <<< (T.rt[e.1]!)[e.2]! := by
          have hsome : some (A ||| 1 <<< (T.rt[e.1]!)[e.2]!) = some A' := by
            rw [← hstep]
            simp only [Option.bind_some, if_pos hc]
          exact (Option.some.injEq _ _).mp hsome.symm
        rw [hA', Nat.testBit_lor, Bool.or_eq_true] at hbit
        rcases hbit with hbit | hbit
        · exact hA t ht hbit
        · rw [ec_testBit_one_shiftLeft] at hbit
          have huG : reflection m ⟨e.1, he1⟩ ∈ G := hgens e.1 he1 hgensbit
          have htG : reflection m ⟨e.2, he2⟩ ∈ G := hA e.2 he2 hAbit
          have hconj : reflection m ⟨(T.rt[e.1]!)[e.2]!, tabsOK_rt_lt hT ⟨e.1, he1⟩ ⟨e.2, he2⟩⟩ ∈ G := by
            rw [reflection_rt hT ⟨e.1, he1⟩ ⟨e.2, he2⟩]
            exact G.mul_mem (G.mul_mem huG htG) huG
          have hfin : (⟨(T.rt[e.1]!)[e.2]!, tabsOK_rt_lt hT ⟨e.1, he1⟩ ⟨e.2, he2⟩⟩ : Root m) =
              ⟨t, ht⟩ := Fin.ext hbit
          rwa [hfin] at hconj
      · have hsome : (some A).bind (fun S =>
            if decide (e.1 < nroots m) && decide (e.2 < nroots m) && gens.testBit e.1 && S.testBit e.2 then
              some (S ||| 1 <<< (T.rt[e.1]!)[e.2]!)
            else none) = some A' := hstep
        simp only [Option.bind_some, if_neg hc] at hsome
        exact absurd hsome (by simp)

theorem genOK_subset {gens c : ℕ} {L : List (ℕ × ℕ)}
    (h : Chk.genOK T (nroots m) gens c L = true) : ofMask m gens ⊆ ofMask m c := by
  have h' := h
  simp only [Chk.genOK, Bool.and_eq_true, decide_eq_true_eq] at h'
  have hsub : Chk.subN gens c = true := h'.1.2
  intro t ht
  rw [mem_ofMask] at ht ⊢
  exact ec_testBit_of_subN hsub ht

theorem genOK_sound (hT : Chk.tabsOK m T = true) {gens c : ℕ} {L : List (ℕ × ℕ)}
    (h : Chk.genOK T (nroots m) gens c L = true) :
    Subgroup.closure (reflection m '' (ofMask m gens : Set (Root m))) = weyl m (ofMask m c) := by
  have h' := h
  simp only [Chk.genOK, Bool.and_eq_true, decide_eq_true_eq] at h'
  have hderiv : (match Chk.derivN T (nroots m) gens L with
      | some S => Chk.subN (Chk.trunc (nroots m) c) S
      | none => false) = true := h'.2
  have hgens : ∀ u (hu : u < nroots m), gens.testBit u = true →
      reflection m ⟨u, hu⟩ ∈ Subgroup.closure (reflection m '' (ofMask m gens : Set (Root m))) :=
    fun u hu hb => Subgroup.subset_closure ⟨⟨u, hu⟩, mem_ofMask.mpr hb, rfl⟩
  refine le_antisymm ?_ ?_
  · exact Subgroup.closure_mono (by
      rintro x ⟨i, hi, rfl⟩
      exact ⟨i, genOK_subset h hi, rfl⟩)
  · rw [weyl, Subgroup.closure_le]
    rintro x ⟨i, hi, rfl⟩
    cases hd : Chk.derivN T (nroots m) gens L with
    | none => rw [hd] at hderiv; exact absurd hderiv (by simp)
    | some S =>
      have hsubn : Chk.subN (Chk.trunc (nroots m) c) S = true := by simpa [hd] using hderiv
      have hcbit : (Chk.trunc (nroots m) c).testBit i.val = true := by
        rw [ec_testBit_trunc_of_lt i.isLt]; exact mem_ofMask.mp hi
      have hSbit : S.testBit i.val = true := ec_testBit_of_subN hsubn hcbit
      have hfold : L.foldl (fun acc e => acc.bind fun S =>
          if decide (e.1 < nroots m) && decide (e.2 < nroots m) && gens.testBit e.1 && S.testBit e.2
          then some (S ||| 1 <<< (T.rt[e.1]!)[e.2]!) else none) (some gens) = some S := by
        simpa [Chk.derivN] using hd
      exact ec_deriv_fold_mem hT hgens L gens hgens S hfold i.val i.isLt hSbit

theorem joinOK_lt {ℓ k t : ℕ} {L : List (ℕ × ℕ)} (h : Chk.joinOK T (nroots m) ℓ k t L = true) :
    t < nroots m := by
  have h' := h
  simp only [Chk.joinOK, Bool.and_eq_true, decide_eq_true_eq] at h'
  exact h'.1

theorem joinOK_sound (hT : Chk.tabsOK m T = true) {ℓ k t : ℕ} {L : List (ℕ × ℕ)}
    (h : Chk.joinOK T (nroots m) ℓ k t L = true) :
    reflection m ⟨t, joinOK_lt h⟩ ∈ weyl m (ofMask m ℓ) ⊔ weyl m (ofMask m k) := by
  have h' := h
  simp only [Chk.joinOK, Bool.and_eq_true, decide_eq_true_eq] at h'
  obtain ⟨ht, hderiv⟩ := h'
  let G : Subgroup (V m ≃ₗ[ZMod 3] V m) := weyl m (ofMask m ℓ) ⊔ weyl m (ofMask m k)
  let start : ℕ := Chk.trunc (nroots m) ℓ ||| Chk.trunc (nroots m) k
  have hgens : ∀ u (hu : u < nroots m), start.testBit u = true → reflection m ⟨u, hu⟩ ∈ G := by
    intro u hu hb
    have hb' : (Chk.trunc (nroots m) ℓ).testBit u = true ∨
        (Chk.trunc (nroots m) k).testBit u = true := by
      rw [show start = Chk.trunc (nroots m) ℓ ||| Chk.trunc (nroots m) k from rfl,
        Nat.testBit_lor, Bool.or_eq_true] at hb
      exact hb
    rcases hb' with hb | hb
    · have huℓ : (⟨u, hu⟩ : Root m) ∈ ofMask m ℓ := by
        rw [mem_ofMask, ← ec_testBit_trunc_of_lt hu]; exact hb
      exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨⟨u, hu⟩, huℓ, rfl⟩)
    · have huk : (⟨u, hu⟩ : Root m) ∈ ofMask m k := by
        rw [mem_ofMask, ← ec_testBit_trunc_of_lt hu]; exact hb
      exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨⟨u, hu⟩, huk, rfl⟩)
  cases hd : Chk.derivN T (nroots m) start L with
  | none => rw [hd] at hderiv; exact absurd hderiv (by simp)
  | some S =>
    have hderiv' : (match Chk.derivN T (nroots m) start L with
        | some S => S.testBit t
        | none => false) = true := hderiv
    rw [hd] at hderiv'
    have hbit : S.testBit t = true := hderiv'
    have hfold : L.foldl (fun acc e => acc.bind fun S =>
        if decide (e.1 < nroots m) && decide (e.2 < nroots m) && start.testBit e.1 && S.testBit e.2
        then some (S ||| 1 <<< (T.rt[e.1]!)[e.2]!) else none) (some start) = some S := by
      simpa [Chk.derivN] using hd
    have hres := ec_deriv_fold_mem hT hgens L start hgens S hfold t ht hbit
    simpa using hres

theorem normalizerGroup_ofMask {c : ℕ} (h : Chk.notB2 m c = true) :
    normalizerGroup m (ofMask m c) = weyl m (ofMask m c) := by
  have h' := h
  simp only [Chk.notB2, Bool.not_eq_true'] at h'
  have hnot : ¬ (m.val = 0 ∧ (ofMask m c).card = 4) := by
    rintro ⟨h0, hcard⟩
    have hcardN : Chk.cardN (nroots m) c = 4 := by
      rw [← card_ofMask m c]; exact hcard
    have htrue : (m.val == 0 && Chk.cardN (nroots m) c == 4) = true := by
      rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
      exact ⟨h0, hcardN⟩
    rw [htrue] at h'
    exact absurd h' (by simp)
  rw [normalizerGroup, if_neg hnot]

theorem normalizerGroup_le_weyl (c : Finset (Root m)) : normalizerGroup m c ≤ weyl m c := by
  rw [normalizerGroup]
  split_ifs
  · exact inf_le_left
  · exact le_rfl

theorem indepOK_sound (hT : Chk.tabsOK m T = true) {w : Chk.LinW} {B : Array (Array ℤ)}
    (h : Chk.indepOK T (dim m) w B = true)
    (hw : ∀ i : Fin (Chk.rkN w.tc w.n), Chk.nodeN w i < nroots m) :
    LinearIndependent (ZMod 3)
      fun i : Fin (Chk.rkN w.tc w.n) => coroot m ⟨Chk.nodeN w i, hw i⟩ := by
  have h' := h
  simp only [Chk.indepOK] at h'
  set k := Chk.rkN w.tc w.n with hk
  let v : Fin k → V m := fun i => coroot m ⟨Chk.nodeN w i, hw i⟩
  let ψ : Fin k → V m →ₗ[ZMod 3] ZMod 3 := fun j =>
    { toFun := fun u => ∑ l : Fin (dim m), u l * (((B[l.val]!)[j.val]! : ℤ) : ZMod 3)
      map_add' := by
        intro u w'
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro a u
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring }
  have hψ_apply : ∀ (j : Fin k) (u : V m), ψ j u =
      ∑ l : Fin (dim m), u l * (((B[l.val]!)[j.val]! : ℤ) : ZMod 3) := fun j u => rfl
  have hfold (i j : Fin k) :
      ((Nat.fold (dim m) (fun l _ s => s + (T.h[Chk.nodeN w i]!)[l]! * (B[l]!)[j]!) 0 : ℤ) :
          ZMod 3) =
        ∑ l : Fin (dim m), v i l * (((B[l.val]!)[j.val]! : ℤ) : ZMod 3) := by
    rw [nat_fold_add]
    push_cast
    apply Finset.sum_congr rfl
    intro l _
    have hv : v i l = ((H m ⟨Chk.nodeN w i, hw i⟩ l : ℤ) : ZMod 3) := rfl
    rw [hv, tabsOK_h hT ⟨Chk.nodeN w i, hw i⟩ l]
    rfl
  have hψv (i j : Fin k) : ψ j (v i) = if i = j then 1 else 0 := by
    have h1 := ec_nat_all_eq_true.mp h' i.val i.isLt
    have h2 := ec_nat_all_eq_true.mp h1 j.val j.isLt
    rw [beq_iff_eq] at h2
    have hcast := ec_zmod_eq_of_sub_emod h2
    push_cast at hcast
    have hδ : (if (i : ℕ) = (j : ℕ) then (1 : ZMod 3) else 0) =
        if i = j then 1 else 0 := by
      by_cases h : i = j
      · subst h; simp
      · have h' : (i : ℕ) ≠ (j : ℕ) := fun hh => h (Fin.ext hh)
        simp [h, h']
    rw [hδ] at hcast
    rw [hψ_apply, ← hfold i j]
    exact hcast
  change LinearIndependent (ZMod 3) v
  refine (Fintype.linearIndependent_iff (v := v)).mpr ?_
  intro g hg j
  have hsum : ψ j (∑ i, g i • v i) = g j := by
    simp only [map_sum, map_smul, hψv, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hbj
      simp [hbj]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have h0 : ψ j (∑ i, g i • v i) = ψ j 0 := congrArg (ψ j) hg
  rw [map_zero] at h0
  exact hsum.symm.trans h0

private theorem ec_det_cast {k : ℕ} {M : ℕ → ℕ → ℤ}
    (M' : Matrix (Fin k) (Fin k) (ZMod 3))
    (hM' : M' = (Matrix.of fun i j : Fin k => M i j).map (Int.castRingHom (ZMod 3))) :
    M'.det = (((Matrix.of fun i j : Fin k => M i j).det : ℤ) : ZMod 3) := by
  rw [hM', ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rfl

theorem invOK_det_ne_zero {k : ℕ} {M : ℕ → ℕ → ℤ} {B : Array (Array ℤ)}
    (h : Chk.invOK k M B = true) :
    (((Matrix.of fun i j : Fin k => M i j).det : ℤ) : ZMod 3) ≠ 0 := by
  have h' := h
  simp only [Chk.invOK] at h'
  let B' : Matrix (Fin k) (Fin k) (ZMod 3) :=
    Matrix.of fun i j => (((B[i.val]!)[j.val]! : ℤ) : ZMod 3)
  let M' : Matrix (Fin k) (Fin k) (ZMod 3) := Matrix.of fun i j => (M i.val j.val : ZMod 3)
  have hBM : B' * M' = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    have h1 := ec_nat_all_eq_true.mp h' i.val i.isLt
    have h2 := ec_nat_all_eq_true.mp h1 j.val j.isLt
    rw [beq_iff_eq] at h2
    have hcast := ec_zmod_eq_of_sub_emod h2
    push_cast at hcast
    have hδ : (if (i : ℕ) = (j : ℕ) then (1 : ZMod 3) else 0) =
        if i = j then 1 else 0 := by
      by_cases h : i = j
      · subst h; simp
      · have h' : (i : ℕ) ≠ (j : ℕ) := fun hh => h (Fin.ext hh)
        simp [h, h']
    rw [hδ] at hcast
    have hsum : (∑ l : Fin k, B' i l * M' l j) =
        ((Nat.fold k (fun l _ s => s + (B[i]!)[l]! * M l j) 0 : ℤ) : ZMod 3) := by
      rw [nat_fold_add]
      push_cast
      rfl
    rw [hsum]
    exact hcast
  have hdet : B'.det * M'.det = 1 := by
    have := congrArg Matrix.det hBM
    rwa [Matrix.det_mul, Matrix.det_one] at this
  have hMdet : M'.det ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hdet
    exact zero_ne_one hdet
  have hMeq : M' = (Matrix.of fun i j : Fin k => M i j).map (Int.castRingHom (ZMod 3)) := by
    ext i j
    simp [M', Matrix.map_apply]
  have hcastdet := ec_det_cast M' hMeq
  rw [hcastdet] at hMdet
  exact hMdet

theorem singOK_det_eq_zero {k : ℕ} {M : ℕ → ℕ → ℤ} {x : Array ℤ}
    (h : Chk.singOK k M x = true) :
    (((Matrix.of fun i j : Fin k => M i j).det : ℤ) : ZMod 3) = 0 := by
  have h' := h
  simp only [Chk.singOK, Bool.and_eq_true, List.any_eq_true, bne_iff_ne] at h'
  obtain ⟨⟨l, hl, hlx⟩, hzero⟩ := h'
  have hlk : l < k := List.mem_range.mp hl
  let M' : Matrix (Fin k) (Fin k) (ZMod 3) := Matrix.of fun i j => (M i.val j.val : ZMod 3)
  let x' : Fin k → ZMod 3 := fun j => ((x[j.val]! : ℤ) : ZMod 3)
  have hx' : x' ≠ 0 := by
    intro hx0
    have hl0 : x' ⟨l, hlk⟩ = 0 := by
      have := congrFun hx0 ⟨l, hlk⟩
      simpa using this
    have hz : ((x[l]! : ℤ) : ZMod 3) = 0 := by simpa [x'] using hl0
    exact hlx (Int.dvd_iff_emod_eq_zero.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd (x[l]!) 3).mp hz))
  have hmul : Matrix.mulVec M' x' = 0 := by
    funext i
    have h1 := ec_nat_all_eq_true.mp hzero i.val i.isLt
    rw [beq_iff_eq] at h1
    have hcast := ec_zmod_eq_zero_of_emod h1
    have hsum : Matrix.mulVec M' x' i = ((Nat.fold k (fun l _ s => s + M i l * x[l]!) 0 : ℤ) : ZMod 3) := by
      simp only [Matrix.mulVec, dotProduct]
      rw [nat_fold_add]
      push_cast
      rfl
    rw [hsum]
    exact hcast
  have hMdet : M'.det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨x', hx', hmul⟩
  have hMeq : M' = (Matrix.of fun i j : Fin k => M i j).map (Int.castRingHom (ZMod 3)) := by
    ext i j
    simp [M', Matrix.map_apply]
  rw [ec_det_cast M' hMeq] at hMdet
  exact hMdet

end

end CFSG.StandardType.GGQ2Frame.ExcRaw

end
