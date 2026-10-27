module

public import CFSG.Quasithin.H13.LocDblDcos
public import Certificates.Data.DcHS

public section

namespace CFSG.Quasithin.H13.LocDbl.HSLoc

open CFSG.QuasithinUnique.K1.SporadicPerm hiding img keyNat
open CFSG.Quasithin.H13.LocDbl.DcNative CFSG.Quasithin.H13.LocDbl.DcRank CFSG.Quasithin.H13.LocDbl.Dc

theorem invT_foldl_size (s : Array ℕ) (l : List ℕ) (r : Array ℕ) :
    (l.foldl (fun r i => r.set! (s.getD i 0) i) r).size = r.size := by
  induction l generalizing r with
  | nil => rfl
  | cons a l ih => rw [List.foldl_cons, ih]; simp

theorem invT_size (s : Array ℕ) : (invT s).size = s.size := by
  unfold invT
  rw [invT_foldl_size]
  simp

theorem invT_getD_aux {s : Array ℕ} (hlt : ∀ j < s.size, s.getD j 0 < s.size)
    (hinj : ∀ j < s.size, ∀ k < s.size, s.getD j 0 = s.getD k 0 → j = k) :
    ∀ k ≤ s.size, ∀ i < k,
      ((List.range k).foldl (fun r i => r.set! (s.getD i 0) i) (Array.replicate s.size 0)).getD
        (s.getD i 0) 0 = i := by
  intro k
  induction k with
  | zero => intro _ i hi; omega
  | succ k ih =>
    intro hk i hi
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    set r := (List.range k).foldl (fun r i => r.set! (s.getD i 0) i) (Array.replicate s.size 0)
      with hr
    have hrs : r.size = s.size := by
      rw [hr, invT_foldl_size]; simp
    have hkn : k < s.size := by omega
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hik | hik
    · have hne : s.getD k 0 ≠ s.getD i 0 := fun h => by
        have := hinj k hkn i (by omega) h
        omega
      have := ih (by omega) i hik
      rw [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
        Array.getElem?_setIfInBounds_ne hne]
      rw [Array.getD_eq_getD_getElem?] at this
      exact this
    · subst hik
      have hlt' := hlt i hkn
      rw [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self,
        if_pos (by omega)]
      rfl

theorem invT_getD {s : Array ℕ} (hlt : ∀ j < s.size, s.getD j 0 < s.size)
    (hinj : ∀ j < s.size, ∀ k < s.size, s.getD j 0 = s.getD k 0 → j = k) {i : ℕ} (hi : i < s.size) :
    (invT s).getD (s.getD i 0) 0 = i :=
  invT_getD_aux hlt hinj s.size le_rfl i hi

variable {Γ : Type} [Group Γ] [MulAction Γ (Fin 100)]

@[expose] def T (g : Γ) : Array ℕ := (tab 100 g).toArray

theorem T_size (g : Γ) : (T g).size = 100 := by simp [T, tab]

theorem img_T (g : Γ) (p : ℕ) : img (T g) p = act 100 g p := by
  simp only [T, img, act, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getD_eq_getElem?_getD]

theorem T_lt (g : Γ) {p : ℕ} (hp : p < 100) : img (T g) p < 100 := by
  rw [img_T]; exact act_lt g hp

theorem T_mul (g h : Γ) : T (g * h) = compT (T g) (T h) := by
  unfold compT
  simp only [T, tab_mul, compTab, List.map_toArray]
  congr 1
  apply List.map_congr_left
  intro j _
  simp only [img, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]

theorem T_one : T (1 : Γ) = idT 100 := by
  simp [T, tab, idT, Array.range_eq_range']

theorem eq_T_of_img {A : Array ℕ} {g : Γ} (hA : A.size = 100)
    (h : ∀ q < 100, img A q = act 100 g q) : A = T g := by
  apply Array.ext
  · rw [hA, T_size]
  · intro i h1 h2
    have hi : i < 100 := by rwa [hA] at h1
    have := h i hi
    rw [← img_T] at this
    simpa [img, Array.getD_eq_getD_getElem?, h1, h2] using this

variable [FaithfulSMul Γ (Fin 100)]

theorem eq_of_act {g h : Γ} (H : ∀ q < 100, act 100 g q = act 100 h q) : g = h :=
  eq_of_base (B := List.range 100) (fun b hb => List.mem_range.mp hb) base_of_faithful
    fun b hb => H b (List.mem_range.mp hb)

theorem eq_of_T {g h : Γ} (hgh : T g = T h) : g = h :=
  eq_of_act fun q _ => by rw [← img_T, ← img_T, hgh]

theorem T_inv (g : Γ) : T g⁻¹ = invT (T g) := by
  have hsz : (T g).size = 100 := T_size g
  have hlt : ∀ j < (T g).size, (T g).getD j 0 < (T g).size := by
    intro j hj
    rw [hsz] at hj ⊢
    exact T_lt g hj
  have hinj : ∀ j < (T g).size, ∀ k < (T g).size, (T g).getD j 0 = (T g).getD k 0 → j = k := by
    intro j hj k hk h
    rw [hsz] at hj hk
    have h' : act 100 g j = act 100 g k := by
      rw [← img_T, ← img_T]; exact h
    have h'' := congrArg (act 100 g⁻¹) h'
    rwa [← act_mul _ _ hj, ← act_mul _ _ hk, inv_mul_cancel, act_one hj, act_one hk] at h''
  symm
  apply eq_T_of_img
  · rw [invT_size, hsz]
  · intro q hq
    have hp : act 100 g⁻¹ q < 100 := act_lt _ hq
    have e : (T g).getD (act 100 g⁻¹ q) 0 = q := by
      show img (T g) (act 100 g⁻¹ q) = q
      rw [img_T, ← act_mul _ _ hq, mul_inv_cancel, act_one hq]
    have := invT_getD hlt hinj (i := act 100 g⁻¹ q) (by rw [hsz]; exact hp)
    rw [e] at this
    simp only [img]
    exact this

theorem T_conj (x g : Γ) : T (x * g * x⁻¹) = conjT (T x) (invT (T x)) (T g) := by
  rw [mul_assoc, T_mul, T_mul, T_inv]
  rfl

theorem commT_iff {g h : Γ} : commT (T g) (T h) = true ↔ g * h = h * g := by
  unfold commT
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq, img_T]
  constructor
  · intro H
    apply eq_of_act
    intro q hq
    rw [act_mul _ _ hq, act_mul _ _ hq]
    exact H q hq
  · intro H q hq
    have := congrArg (fun z => act 100 z q) H
    simpa only [act_mul _ _ hq] using this

end CFSG.Quasithin.H13.LocDbl.HSLoc
