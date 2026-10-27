module

public import CFSG.Quasithin.Background.Asc81cPfCheck
public import CFSG.Monster.B.Co2.PermArr
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Quasithin

namespace Asc81c

namespace Pf

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.KGroups.Native Check

section Lin

theorem mod_two_pow_succ_eq (i m : ℕ) :
    i % 2 ^ (m + 1) = if i.testBit m then i % 2 ^ m ^^^ 2 ^ m else i % 2 ^ m := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow]
  split_ifs with h
  · rw [Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_two_pow]
    rcases lt_trichotomy j m with hj | rfl | hj
    · simp [hj, Nat.lt_succ_of_lt hj, hj.ne']
    · simp [h]
    · simp [hj.ne, show ¬ j < m from by omega, show ¬ j < m + 1 from by omega]
  · rw [Nat.testBit_mod_two_pow]
    rcases lt_trichotomy j m with hj | rfl | hj
    · simp [hj, Nat.lt_succ_of_lt hj]
    · simp [h]
    · simp [show ¬ j < m from by omega, show ¬ j < m + 1 from by omega]

theorem linV_eq {n : ℕ} (t : Fin (2 ^ n) → Fin (2 ^ n)) (ht : ∀ i j, t (i ^^^ j) = t i ^^^ t j)
    (c : List ℕ) (hc : ∀ k (hk : k < n), c.getD k 0 = (t ⟨2 ^ k, Nat.pow_lt_pow_right
      (by norm_num) hk⟩ : ℕ)) (i : Fin (2 ^ n)) : linV n c i = (t i : ℕ) := by
  let T : ℕ → ℕ := fun x => if h : x < 2 ^ n then (t ⟨x, h⟩ : ℕ) else 0
  have hT : ∀ x y, x < 2 ^ n → y < 2 ^ n → T (x ^^^ y) = T x ^^^ T y := by
    intro x y hx hy
    have hxy : x ^^^ y < 2 ^ n := Nat.xor_lt_two_pow hx hy
    simp only [T, hx, hy, hxy, ↓reduceDIte]
    have h1 : (⟨x ^^^ y, hxy⟩ : Fin (2 ^ n)) = ⟨x, hx⟩ ^^^ ⟨y, hy⟩ :=
      Fin.ext (by rw [Fin.xor_val, Nat.mod_eq_of_lt hxy])
    rw [h1, ht, Fin.xor_val, Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (Fin.isLt _) (Fin.isLt _))]
  have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
  have hT0 : T 0 = 0 := by
    have h := hT 0 0 hpos hpos
    rw [Nat.xor_self] at h
    rw [h, Nat.xor_self]
  have hmod : ∀ m, m ≤ n → i.val % 2 ^ m < 2 ^ n := fun m hm =>
    lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos m)) (Nat.pow_le_pow_right (by norm_num) hm)
  have key : ∀ m, m ≤ n → (List.range m).foldl (fun acc k =>
      if (i : ℕ).testBit k then acc ^^^ c.getD k 0 else acc) 0 = T ((i : ℕ) % 2 ^ m) := by
    intro m hm
    induction m with
    | zero => simp only [List.range_zero, List.foldl_nil, pow_zero, Nat.mod_one, hT0]
    | succ m ih =>
      have hm' : m < n := by omega
      rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil,
        mod_two_pow_succ_eq]
      by_cases hb : (i : ℕ).testBit m
      · simp only [hb, ↓reduceIte]
        rw [hT _ _ (hmod m (by omega)) (Nat.pow_lt_pow_right (by norm_num) hm'), hc m hm']
        simp only [T, (Nat.pow_lt_pow_right (by norm_num) hm' : 2 ^ m < 2 ^ n), ↓reduceDIte]
      · simp only [hb, Bool.false_eq_true, ↓reduceIte]
  have h := key n le_rfl
  rw [Nat.mod_eq_of_lt i.2] at h
  rw [linV, h]
  simp only [T, i.2, ↓reduceDIte]

theorem rep_linA {n : ℕ} (t : Equiv.Perm (Fin (2 ^ n))) (ht : ∀ i j, t (i ^^^ j) = t i ^^^ t j)
    (c : List ℕ) (hc : ∀ k (hk : k < n), c.getD k 0 = (t ⟨2 ^ k, Nat.pow_lt_pow_right
      (by norm_num) hk⟩ : ℕ)) : Rep (2 ^ n) (linA n c) t := fun x => by
  rw [linA, getElem!_ofFn_nat _ x.2]
  exact linV_eq t ht c hc x

end Lin

section Coord

variable {Q : Type*} [CommGroup Q] {n : ℕ}

@[expose] def coordMap (e : Fin n → Q) (i : Fin (2 ^ n)) : Q :=
  ∏ k : Fin n, if (i : ℕ).testBit k then e k else 1

theorem coordMap_xor {e : Fin n → Q} (he : ∀ k, e k * e k = 1) (i j : Fin (2 ^ n)) :
    coordMap e (i ^^^ j) = coordMap e i * coordMap e j := by
  unfold coordMap
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Fin.xor_val, Nat.mod_eq_of_lt (Nat.xor_lt_two_pow i.2 j.2), Nat.testBit_xor]
  cases (i : ℕ).testBit k <;> cases (j : ℕ).testBit k <;> simp [he]

variable {φ : Fin (2 ^ n) → Q}

@[expose] noncomputable def permOf (hφ : Function.Bijective φ) (σ : MulAut Q) :
    Equiv.Perm (Fin (2 ^ n)) :=
  (Equiv.ofBijective φ hφ).trans (σ.toEquiv.trans (Equiv.ofBijective φ hφ).symm)

theorem coordMap_permOf (hφ : Function.Bijective φ) (σ : MulAut Q) (i : Fin (2 ^ n)) :
    φ (permOf hφ σ i) = σ (φ i) := by
  simp [permOf, Equiv.ofBijective_apply_symm_apply]

theorem permOf_eq_iff (hφ : Function.Bijective φ) (σ : MulAut Q) (i j : Fin (2 ^ n)) :
    permOf hφ σ i = j ↔ σ (φ i) = φ j := by
  rw [← coordMap_permOf hφ σ i]
  exact ⟨fun h => by rw [h], fun h => hφ.1 h⟩

theorem permOf_xor (hφ : Function.Bijective φ) (hx : ∀ i j, φ (i ^^^ j) = φ i * φ j)
    (σ : MulAut Q) (i j : Fin (2 ^ n)) :
    permOf hφ σ (i ^^^ j) = permOf hφ σ i ^^^ permOf hφ σ j := by
  rw [permOf_eq_iff, hx, hx, coordMap_permOf hφ σ i, coordMap_permOf hφ σ j, map_mul]

@[expose] noncomputable def permOfHom (hφ : Function.Bijective φ) :
    MulAut Q →* Equiv.Perm (Fin (2 ^ n)) where
  toFun := permOf hφ
  map_one' := Equiv.ext fun i => by
    rw [permOf_eq_iff]
    rfl
  map_mul' σ τ := Equiv.ext fun i => by
    rw [permOf_eq_iff, Equiv.Perm.mul_apply, coordMap_permOf hφ σ, coordMap_permOf hφ τ]
    rfl

theorem permOfHom_apply (hφ : Function.Bijective φ) (σ : MulAut Q) :
    permOfHom hφ σ = permOf hφ σ := rfl

theorem permOfHom_injective (hφ : Function.Bijective φ) :
    Function.Injective (permOfHom hφ) := by
  intro σ τ h
  ext q
  obtain ⟨i, rfl⟩ := hφ.2 q
  rw [← coordMap_permOf hφ σ i, ← coordMap_permOf hφ τ i]
  rw [permOfHom_apply, permOfHom_apply] at h
  rw [h]

end Coord

section Words

@[expose] def evalG {M : Type*} [Monoid M] (a b : M) : List Bool → M
  | [] => 1
  | false :: w => a * evalG a b w
  | true :: w => b * evalG a b w

theorem map_evalG {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) (a b : M) (w : List Bool) :
    f (evalG a b w) = evalG (f a) (f b) w := by
  induction w with
  | nil => simp [evalG]
  | cons c w ih => cases c <;> simp [evalG, ih]

theorem evalG_append {M : Type*} [Monoid M] (a b : M) (w : List Bool) (c : Bool) :
    evalG a b (w ++ [c]) = evalG a b w * (if c then b else a) := by
  induction w with
  | nil => cases c <;> simp [evalG]
  | cons d w ih => cases d <;> simp [evalG, ih, mul_assoc]

theorem evalG_mem_closure {G : Type*} [Group G] (a b : G) (w : List Bool) :
    evalG a b w ∈ Subgroup.closure ({a, b} : Set G) := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons c w ih =>
    cases c
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) ih
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) ih

theorem rep_evalWA {N : ℕ} {a b : Array ℕ} {σ τ : Equiv.Perm (Fin N)} (ha : Rep N a σ)
    (hb : Rep N b τ) (w : List Bool) : Rep N (evalWA N a b w) (evalG σ τ w) := by
  induction w with
  | nil => exact rep_idA
  | cons c w ih =>
    cases c
    · exact rep_compA ha ih
    · exact rep_compA hb ih

end Words

end Pf

end Asc81c

end CFSG.Quasithin
