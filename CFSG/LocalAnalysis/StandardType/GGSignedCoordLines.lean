module

public import CFSG.LocalAnalysis.StandardType.GGSignedCoordConj

public section

namespace CFSG.StandardType

open SpCoord Multiplicative

variable {n p : ℕ}

private theorem toAdd_zpow_apply (f : Fin n → Multiplicative (ZMod p)) (t : ℤ) (k : Fin n) :
    toAdd ((f ^ t) k) = (t : ZMod p) * toAdd (f k) := by
  rw [Pi.pow_apply, toAdd_zpow, zsmul_eq_mul]

private theorem toAdd_zpow_mul_zpow_apply (a b : Fin n → Multiplicative (ZMod p))
    (s t : ℤ) (k : Fin n) :
    toAdd ((a ^ s * b ^ t) k) =
      (s : ZMod p) * toAdd (a k) + (t : ZMod p) * toAdd (b k) := by
  rw [toAdd_mul_apply, toAdd_zpow_apply, toAdd_zpow_apply]

private theorem eq_one_of_toAdd_eq_zero {x : Multiplicative (ZMod p)} (h : toAdd x = 0) :
    x = 1 := by
  rw [← ofAdd_toAdd x, h]
  rfl

private theorem eq_one_of_forall_toAdd_eq_zero {f : Fin n → Multiplicative (ZMod p)}
    (h : ∀ k, toAdd (f k) = 0) : f = 1 := by
  funext k
  exact eq_one_of_toAdd_eq_zero (h k)

private theorem eq_one_of_axis {f : Fin n → Multiplicative (ZMod p)} {j : Fin n}
    (hf : ∀ k, k ≠ j → f k = 1) (hj : f j = 1) : f = 1 := by
  funext k
  by_cases hk : k = j
  · subst hk
    exact hj
  · exact hf k hk

private theorem toAdd_zpow_ne_zero_of_axis {b : Fin n → Multiplicative (ZMod p)} {j : Fin n}
    (hb : ∀ k, k ≠ j → b k = 1) {t : ℤ} (hbt : b ^ t ≠ 1) :
    toAdd ((b ^ t) j) ≠ 0 := by
  intro h
  apply hbt
  refine eq_one_of_axis (j := j) (fun k hk => ?_) (eq_one_of_toAdd_eq_zero h)
  exact eq_one_of_toAdd_eq_zero (by rw [toAdd_zpow_apply, hb k hk, toAdd_one, mul_zero])

private theorem exists_zpow_mul_zpow_of_mem_closure_pair
    {a b w : Fin n → Multiplicative (ZMod p)}
    (hw : w ∈ Subgroup.closure ({a, b} : Set (Fin n → Multiplicative (ZMod p)))) :
    ∃ s t : ℤ, a ^ s * b ^ t = w :=
  Subgroup.mem_closure_pair.mp hw

private theorem zpow_ne_one_of_notMem_zpowers {a b w : Fin n → Multiplicative (ZMod p)}
    {s t : ℤ} (hwa : w ∉ Subgroup.zpowers a) (hst : a ^ s * b ^ t = w) : b ^ t ≠ 1 := by
  intro h
  apply hwa
  rw [Subgroup.mem_zpowers_iff]
  exact ⟨s, by rw [← hst, h, mul_one]⟩

private theorem eq_or_eq_neg_of_signs {x y : ZMod p} (hx : x = 1 ∨ x = -1)
    (hy : y = 1 ∨ y = -1) : x = y ∨ x = -y := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp

private theorem sign_mul_sign {x y : ZMod p} (hp : p.Prime) (hx : x = 1 ∨ x = -1)
    (hy : y = 1 ∨ y = -1) : x * y = 1 ∨ x * y = -1 := by
  have := Fact.mk hp
  have hsq : (x * y) * (x * y) = 1 := by
    calc (x * y) * (x * y) = (x * x) * (y * y) := by ring
      _ = 1 * 1 := by rw [coord_sign_mul_self hx, coord_sign_mul_self hy]
      _ = 1 := one_mul 1
  exact sq_eq_one_iff.mp (by rw [sq]; exact hsq)

private theorem toAdd_zpow_const_apply {δ : MulAut (Fin n → Multiplicative (ZMod p))}
    {ε : Fin n → ZMod p} {c : ZMod p}
    (hε : ∀ c' i, toAdd (δ (fun _ => ofAdd c') i) = ε i * c') (t : ℤ) (k : Fin n) :
    toAdd (((δ (fun _ => ofAdd c)) ^ t) k) = ε k * ((t : ZMod p) * c) := by
  rw [toAdd_zpow_apply, hε c k]
  ring

private theorem toAdd_negOff_apply (j : Fin n) (f : Fin n → Multiplicative (ZMod p))
    (k : Fin n) :
    toAdd (negOff j f k) = if k = j then toAdd (f k) else -toAdd (f k) := by
  by_cases hk : k = j
  · rw [negOff_apply, if_pos hk, if_pos hk]
  · rw [negOff_apply, if_neg hk, if_neg hk, toAdd_inv]

private theorem toAdd_negOff_mul_apply_const_one (j : Fin n)
    {δ : MulAut (Fin n → Multiplicative (ZMod p))} {ε : Fin n → ZMod p}
    (hε : ∀ c i, toAdd (δ (fun _ => ofAdd c) i) = ε i * c) (k : Fin n) :
    toAdd (((negOff j : MulAut (Fin n → Multiplicative (ZMod p))) * δ)
      (fun _ => ofAdd (1 : ZMod p)) k) = if k = j then ε k else -ε k := by
  rw [MulAut.mul_apply (Fin n → Multiplicative (ZMod p)), toAdd_negOff_apply, hε 1 k]
  by_cases hk : k = j <;> simp [hk]

private theorem map_conj_mul (S : Subgroup (MulAut (Fin n → Multiplicative (ZMod p))))
    (u v : MulAut (Fin n → Multiplicative (ZMod p))) :
    (S.map (MulAut.conj u).toMonoidHom).map (MulAut.conj v).toMonoidHom =
      S.map (MulAut.conj (v * u)).toMonoidHom := by
  have hcomp : (MulAut.conj v).toMonoidHom.comp (MulAut.conj u).toMonoidHom =
      (MulAut.conj (v * u)).toMonoidHom := by
    refine MonoidHom.ext fun w => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply]
    group
  rw [Subgroup.map_map, hcomp]

private theorem apply_const_one_eq_or_inv {δ δ' : MulAut (Fin n → Multiplicative (ZMod p))}
    {ε ε' : Fin n → ZMod p} {σ : ZMod p}
    (hε : ∀ c i, toAdd (δ (fun _ => ofAdd c) i) = ε i * c)
    (hε' : ∀ c i, toAdd (δ' (fun _ => ofAdd c) i) = ε' i * c)
    (hσ : σ = 1 ∨ σ = -1) (hsign : ∀ k, ε k = σ * ε' k) :
    δ (fun _ => ofAdd 1) = δ' (fun _ => ofAdd 1) ∨
      δ (fun _ => ofAdd 1) = (δ' (fun _ => ofAdd 1))⁻¹ := by
  rcases hσ with h1 | h1
  · left
    apply eq_of_toAdd_eq
    intro k
    rw [hε 1 k, hε' 1 k, hsign k, h1]
    ring
  · right
    apply eq_of_toAdd_eq
    intro k
    rw [toAdd_inv_apply, hε 1 k, hε' 1 k, hsign k, h1]
    ring

private theorem apply_const_one_eq_or_inv_negOff_mul (i0 : Fin n)
    {δ δ₀ : MulAut (Fin n → Multiplicative (ZMod p))} {ε ε₀ : Fin n → ZMod p} {σ : ZMod p}
    (hε : ∀ c i, toAdd (δ (fun _ => ofAdd c) i) = ε i * c)
    (hε₀ : ∀ c i, toAdd (δ₀ (fun _ => ofAdd c) i) = ε₀ i * c)
    (hσ : σ = 1 ∨ σ = -1) (hoff : ∀ k, k ≠ i0 → ε k = σ * ε₀ k)
    (hat : ε i0 = -(σ * ε₀ i0)) :
    δ (fun _ => ofAdd 1) = ((negOff i0 : MulAut (Fin n → Multiplicative (ZMod p))) * δ₀)
        (fun _ => ofAdd 1) ∨
      δ (fun _ => ofAdd 1) = (((negOff i0 : MulAut (Fin n → Multiplicative (ZMod p))) * δ₀)
        (fun _ => ofAdd 1))⁻¹ := by
  rcases hσ with h1 | h1
  · right
    apply eq_of_toAdd_eq
    intro k
    rw [toAdd_inv_apply, hε 1 k, toAdd_negOff_mul_apply_const_one i0 hε₀ k]
    by_cases hk : k = i0
    · subst hk
      rw [if_pos rfl, hat, h1]
      ring
    · rw [if_neg hk, hoff k hk, h1]
      ring
  · left
    apply eq_of_toAdd_eq
    intro k
    rw [hε 1 k, toAdd_negOff_mul_apply_const_one i0 hε₀ k]
    by_cases hk : k = i0
    · subst hk
      rw [if_pos rfl, hat, h1]
      ring
    · rw [if_neg hk, hoff k hk, h1]
      ring

private theorem apply_const_one_eq_or_inv_negOff (j : Fin n)
    {δ : MulAut (Fin n → Multiplicative (ZMod p))} {ε : Fin n → ZMod p} {σ : ZMod p}
    (hε : ∀ c i, toAdd (δ (fun _ => ofAdd c) i) = ε i * c)
    (hσ : σ = 1 ∨ σ = -1) (hoff : ∀ k, k ≠ j → ε k = σ) (hat : ε j = -σ) :
    δ (fun _ => ofAdd 1) = negOff j (fun _ => ofAdd 1) ∨
      δ (fun _ => ofAdd 1) = (negOff j (fun _ => ofAdd 1))⁻¹ := by
  rcases hσ with h1 | h1
  · right
    apply eq_of_toAdd_eq
    intro k
    rw [toAdd_inv_apply, hε 1 k, toAdd_negOff_apply j (fun _ => ofAdd 1) k, toAdd_ofAdd,
      mul_one]
    by_cases hk : k = j
    · subst hk
      rw [if_pos rfl, hat, h1]
    · rw [if_neg hk, hoff k hk, h1]
      ring
  · left
    apply eq_of_toAdd_eq
    intro k
    rw [hε 1 k, toAdd_negOff_apply j (fun _ => ofAdd 1) k, toAdd_ofAdd, mul_one]
    by_cases hk : k = j
    · subst hk
      rw [if_pos rfl, hat, h1]
      ring
    · rw [if_neg hk, hoff k hk, h1]

private theorem exists_common_sign_of_mem_closure_axis_const (hp : p.Prime) (hn : 2 ≤ n)
    {i0 : Fin n} {δ₀ δ : MulAut (Fin n → Multiplicative (ZMod p))} {c₀ c : ZMod p}
    {a w : Fin n → Multiplicative (ZMod p)} {ε ε₀ : Fin n → ZMod p}
    (hεsign : ∀ i, ε i = 1 ∨ ε i = -1) (hε₀sign : ∀ i, ε₀ i = 1 ∨ ε₀ i = -1)
    (ha : ∀ k, k ≠ i0 → a k = 1)
    (hε : ∀ c' i, toAdd (δ (fun _ => ofAdd c') i) = ε i * c')
    (hε₀ : ∀ c' i, toAdd (δ₀ (fun _ => ofAdd c') i) = ε₀ i * c')
    {s t : ℤ} (hst : a ^ s * (δ₀ (fun _ => ofAdd c₀)) ^ t = w)
    (hwa : w ∉ Subgroup.zpowers a) (hwδ : w = δ (fun _ => ofAdd c)) :
    ∃ σ : ZMod p, c ≠ 0 ∧ (σ = 1 ∨ σ = -1) ∧ ∀ k, k ≠ i0 → ε k = σ * ε₀ k := by
  have := Fact.mk hp
  have hbt : (δ₀ (fun _ => ofAdd c₀)) ^ t ≠ 1 := zpow_ne_one_of_notMem_zpowers hwa hst
  have hd_ne : (t : ZMod p) * c₀ ≠ 0 := by
    intro hd0
    apply hbt
    refine eq_one_of_forall_toAdd_eq_zero fun k => ?_
    rw [toAdd_zpow_const_apply hε₀, hd0, mul_zero]
  have hcoord : ∀ k, k ≠ i0 → ε k * c = ε₀ k * ((t : ZMod p) * c₀) := by
    intro k hk
    rw [← hε c k, ← hwδ, ← hst, toAdd_zpow_mul_zpow_apply, ha k hk, toAdd_one, mul_zero,
      zero_add, ← toAdd_zpow_apply, toAdd_zpow_const_apply hε₀]
  obtain ⟨k₁, hk₁⟩ :=
    Fintype.exists_ne_of_one_lt_card (by rw [Fintype.card_fin]; omega) i0
  have hc_ne : c ≠ 0 := by
    intro hc0
    have h := hcoord k₁ hk₁
    rw [hc0, mul_zero] at h
    exact (coord_mul_ne_zero hp (coord_sign_ne_zero hp (hε₀sign k₁)) hd_ne) h.symm
  have hd_eq : (t : ZMod p) * c₀ = (ε k₁ * ε₀ k₁) * c := by
    have hk := hcoord k₁ hk₁
    have hsq := coord_sign_mul_self (hε₀sign k₁)
    calc (t : ZMod p) * c₀ = ε₀ k₁ * (ε k₁ * c) := by
          rw [hk, ← mul_assoc, hsq, one_mul]
      _ = (ε k₁ * ε₀ k₁) * c := by ring
  have hσsign : ε k₁ * ε₀ k₁ = 1 ∨ ε k₁ * ε₀ k₁ = -1 :=
    sign_mul_sign hp (hεsign k₁) (hε₀sign k₁)
  have hσ_eq : ∀ k, k ≠ i0 → ε k = (ε k₁ * ε₀ k₁) * ε₀ k := by
    intro k hk
    refine mul_right_cancel₀ hc_ne ?_
    rw [hcoord k hk, hd_eq]
    ring
  exact ⟨ε k₁ * ε₀ k₁, hc_ne, hσsign, hσ_eq⟩

private theorem exists_const_sign_off_axis (hp : p.Prime) (hn : 2 ≤ n)
    {j : Fin n} {δ : MulAut (Fin n → Multiplicative (ZMod p))} {c : ZMod p}
    {a b w : Fin n → Multiplicative (ZMod p)} {ε : Fin n → ZMod p}
    (hεsign : ∀ i, ε i = 1 ∨ ε i = -1)
    (ha : ∀ i k, a i = a k) (hb : ∀ k, k ≠ j → b k = 1)
    (hε : ∀ c' i, toAdd (δ (fun _ => ofAdd c') i) = ε i * c')
    {s t : ℤ} (hst : a ^ s * b ^ t = w)
    (hwa : w ∉ Subgroup.zpowers a) (hwδ : w = δ (fun _ => ofAdd c)) :
    ∃ σ : ZMod p, (σ = 1 ∨ σ = -1) ∧ ∀ k, k ≠ j → ε k = σ := by
  have := Fact.mk hp
  have hbt : b ^ t ≠ 1 := zpow_ne_one_of_notMem_zpowers hwa hst
  have hβ_ne : (t : ZMod p) * toAdd (b j) ≠ 0 := by
    rw [← toAdd_zpow_apply]
    exact toAdd_zpow_ne_zero_of_axis hb hbt
  have hwj : toAdd (w j) = (s : ZMod p) * toAdd (a j) + (t : ZMod p) * toAdd (b j) := by
    rw [← hst, toAdd_zpow_mul_zpow_apply]
  have hwk : ∀ k, k ≠ j → toAdd (w k) = (s : ZMod p) * toAdd (a j) := by
    intro k hk
    rw [← hst, toAdd_zpow_mul_zpow_apply, hb k hk, toAdd_one, mul_zero, add_zero, ha k j]
  obtain ⟨k₁, hk₁⟩ :=
    Fintype.exists_ne_of_one_lt_card (by rw [Fintype.card_fin]; omega) j
  have hc_ne : c ≠ 0 := by
    intro hc0
    have hA : (s : ZMod p) * toAdd (a j) = 0 := by
      rw [← hwk k₁ hk₁, hwδ, hε c k₁, hc0, mul_zero]
    have hj0 : toAdd (w j) = 0 := by rw [hwδ, hε c j, hc0, mul_zero]
    rw [hwj, hA, zero_add] at hj0
    exact hβ_ne hj0
  have hσ_eq : ∀ k, k ≠ j → ε k = ε k₁ := by
    intro k hk
    have h1 : ε k * c = (s : ZMod p) * toAdd (a j) := by
      rw [← hε c k, ← hwδ, hwk k hk]
    have h2 : ε k₁ * c = (s : ZMod p) * toAdd (a j) := by
      rw [← hε c k₁, ← hwδ, hwk k₁ hk₁]
    exact mul_right_cancel₀ hc_ne (h1.trans h2.symm)
  exact ⟨ε k₁, hεsign k₁, hσ_eq⟩

theorem axis_eq_of_mem_closure_axis_axis {i0 j : Fin n} (hij : j ≠ i0)
    {a b w : Fin n → Multiplicative (ZMod p)} (ha : ∀ k, k ≠ i0 → a k = 1)
    (hb : ∀ k, k ≠ j → b k = 1) (hw : w ∈ Subgroup.closure {a, b})
    (hwa : w ∉ Subgroup.zpowers a) {j' : Fin n} (h : ∀ k, k ≠ j' → w k = 1) : j' = j := by
  obtain ⟨s, t, hst⟩ := exists_zpow_mul_zpow_of_mem_closure_pair hw
  have hbt : b ^ t ≠ 1 := zpow_ne_one_of_notMem_zpowers hwa hst
  have hbtj : toAdd ((b ^ t) j) ≠ 0 := toAdd_zpow_ne_zero_of_axis hb hbt
  have hapow_j : (a ^ s) j = 1 := by
    rw [Pi.pow_apply, ha j hij, one_zpow]
  have hwj : w j ≠ 1 := by
    rw [← hst, Pi.mul_apply, hapow_j, one_mul]
    exact fun h1 => hbtj (by rw [h1, toAdd_one])
  by_contra hne
  exact hwj (h j (Ne.symm hne))

theorem ne_apply_const_of_mem_closure_axis_axis (hn : 3 ≤ n) {i0 j : Fin n} (hij : j ≠ i0)
    {a b w : Fin n → Multiplicative (ZMod p)} (ha : ∀ k, k ≠ i0 → a k = 1)
    (hb : ∀ k, k ≠ j → b k = 1) (hw : w ∈ Subgroup.closure {a, b})
    (hwa : w ∉ Subgroup.zpowers a) {δ : MulAut (Fin n → Multiplicative (ZMod p))}
    (hδ : δ ∈ bSignedFull n p) (c : ZMod p) : w ≠ δ (fun _ => ofAdd c) := by
  intro hwδ
  obtain ⟨s, t, hst⟩ := exists_zpow_mul_zpow_of_mem_closure_pair hw
  obtain ⟨ε, hεsign, hε⟩ := exists_signs_apply_const hδ
  have hbt : b ^ t ≠ 1 := zpow_ne_one_of_notMem_zpowers hwa hst
  have hbtj : toAdd ((b ^ t) j) ≠ 0 := toAdd_zpow_ne_zero_of_axis hb hbt
  have hapow_j : (a ^ s) j = 1 := by
    rw [Pi.pow_apply, ha j hij, one_zpow]
  have hwj : w j ≠ 1 := by
    rw [← hst, Pi.mul_apply, hapow_j, one_mul]
    exact fun h1 => hbtj (by rw [h1, toAdd_one])
  obtain ⟨k, hki0, hkj⟩ := coord_exists_ne_ne hn i0 j
  have hwk : toAdd (w k) = 0 := by
    rw [← hst, toAdd_zpow_mul_zpow_apply, ha k hki0, hb k hkj, toAdd_one, mul_zero,
      mul_zero, add_zero]
  have hprod : ε k * c = 0 := by
    rw [← hε c k, ← hwδ]
    exact hwk
  have hc_eq : c = 0 := by
    rcases hεsign k with h | h
    · rw [h, one_mul] at hprod
      exact hprod
    · rw [h, neg_one_mul] at hprod
      exact neg_eq_zero.mp hprod
  exact hwj (eq_one_of_toAdd_eq_zero (by rw [hwδ, hε c j, hc_eq, mul_zero]))

theorem not_axis_of_mem_closure_axis_const (hn : 3 ≤ n) {i0 : Fin n}
    {δ₀ : MulAut (Fin n → Multiplicative (ZMod p))} (hδ₀ : δ₀ ∈ bSignedFull n p) {c₀ : ZMod p}
    {a w : Fin n → Multiplicative (ZMod p)} (ha : ∀ k, k ≠ i0 → a k = 1)
    (hw : w ∈ Subgroup.closure {a, δ₀ (fun _ => ofAdd c₀)}) (hwa : w ∉ Subgroup.zpowers a)
    (j' : Fin n) : ¬ ∀ k, k ≠ j' → w k = 1 := by
  intro h
  obtain ⟨s, t, hst⟩ := exists_zpow_mul_zpow_of_mem_closure_pair hw
  obtain ⟨ε₀, hε₀sign, hε₀⟩ := exists_signs_apply_const hδ₀
  have hbt : (δ₀ (fun _ => ofAdd c₀)) ^ t ≠ 1 := zpow_ne_one_of_notMem_zpowers hwa hst
  have hd_ne : (t : ZMod p) * c₀ ≠ 0 := by
    intro hd0
    apply hbt
    refine eq_one_of_forall_toAdd_eq_zero fun k => ?_
    rw [toAdd_zpow_const_apply hε₀, hd0, mul_zero]
  have hwk_ne : ∀ k, k ≠ i0 → w k ≠ 1 := by
    intro k hk
    have hz : toAdd (w k) ≠ 0 := by
      rw [← hst, toAdd_zpow_mul_zpow_apply, ha k hk, toAdd_one, mul_zero, zero_add,
        ← toAdd_zpow_apply, toAdd_zpow_const_apply hε₀]
      rcases hε₀sign k with h | h
      · rwa [h, one_mul]
      · rw [h, neg_one_mul]
        exact neg_ne_zero.mpr hd_ne
    exact fun h1 => hz (by rw [h1, toAdd_one])
  obtain ⟨k, hki0, hkj'⟩ := coord_exists_ne_ne hn i0 j'
  exact hwk_ne k hki0 (h k hkj')

theorem aPermutationFull_map_conj_eq_of_mem_closure_axis_const (hp : p.Prime)
    (hn : 2 ≤ n) {i0 : Fin n} {δ₀ δ : MulAut (Fin n → Multiplicative (ZMod p))}
    (hδ₀ : δ₀ ∈ bSignedFull n p) (hδ : δ ∈ bSignedFull n p) {c₀ c : ZMod p}
    {a w : Fin n → Multiplicative (ZMod p)} (ha : ∀ k, k ≠ i0 → a k = 1)
    (hw : w ∈ Subgroup.closure {a, δ₀ (fun _ => ofAdd c₀)}) (hwa : w ∉ Subgroup.zpowers a)
    (hwδ : w = δ (fun _ => ofAdd c)) :
    (aPermutationFull n p).map (MulAut.conj δ).toMonoidHom =
        (aPermutationFull n p).map (MulAut.conj δ₀).toMonoidHom ∨
      (aPermutationFull n p).map (MulAut.conj δ).toMonoidHom =
        ((aPermutationFull n p).map (MulAut.conj δ₀).toMonoidHom).map
          (MulAut.conj (negOff i0)).toMonoidHom := by
  have := Fact.mk hp
  obtain ⟨s, t, hst⟩ := exists_zpow_mul_zpow_of_mem_closure_pair hw
  obtain ⟨ε₀, hε₀sign, hε₀⟩ := exists_signs_apply_const hδ₀
  obtain ⟨ε, hεsign, hε⟩ := exists_signs_apply_const hδ
  obtain ⟨σ, hc_ne, hσsign, hσ_eq⟩ :=
    exists_common_sign_of_mem_closure_axis_const hp hn hεsign hε₀sign ha hε hε₀ hst hwa hwδ
  have hτsign := sign_mul_sign hp hσsign (hε₀sign i0)
  rcases eq_or_eq_neg_of_signs (hεsign i0) hτsign with hεi0 | hεi0
  · have hsign : ∀ k, ε k = σ * ε₀ k := by
      intro k
      by_cases hk : k = i0
      · subst hk
        exact hεi0
      · exact hσ_eq k hk
    exact Or.inl (aPermutationFull_map_conj_eq_of_apply_one hδ hδ₀
      (apply_const_one_eq_or_inv hε hε₀ hσsign hsign))
  · have hδ₁ : negOff i0 * δ₀ ∈ bSignedFull n p :=
      Subgroup.mul_mem (bSignedFull n p)
        (bCoordinateBlock_le_bSignedFull i0 (negOff_mem_bCoordinateBlock i0)) hδ₀
    have happly := apply_const_one_eq_or_inv_negOff_mul i0 hε hε₀ hσsign hσ_eq hεi0
    have heq := aPermutationFull_map_conj_eq_of_apply_one hδ hδ₁ happly
    exact Or.inr (heq.trans (map_conj_mul (aPermutationFull n p) δ₀ (negOff i0)).symm)

theorem axis_eq_of_mem_closure_const_axis (hn : 3 ≤ n) {j : Fin n}
    {a b w : Fin n → Multiplicative (ZMod p)} (ha : ∀ i k, a i = a k)
    (hb : ∀ k, k ≠ j → b k = 1) (hw : w ∈ Subgroup.closure {a, b})
    (hwa : w ∉ Subgroup.zpowers a) {j' : Fin n} (h : ∀ k, k ≠ j' → w k = 1) : j' = j := by
  obtain ⟨s, t, hst⟩ := exists_zpow_mul_zpow_of_mem_closure_pair hw
  have hbt : b ^ t ≠ 1 := zpow_ne_one_of_notMem_zpowers hwa hst
  have hβ_ne : (t : ZMod p) * toAdd (b j) ≠ 0 := by
    rw [← toAdd_zpow_apply]
    exact toAdd_zpow_ne_zero_of_axis hb hbt
  by_contra hne
  obtain ⟨k, hkj, hkj'⟩ := coord_exists_ne_ne hn j j'
  have hwj : toAdd (w j) =
      (s : ZMod p) * toAdd (a j) + (t : ZMod p) * toAdd (b j) := by
    rw [← hst, toAdd_zpow_mul_zpow_apply]
  have hwk : toAdd (w k) = (s : ZMod p) * toAdd (a j) := by
    rw [← hst, toAdd_zpow_mul_zpow_apply, hb k hkj, toAdd_one, mul_zero, add_zero, ha k j]
  have hA : (s : ZMod p) * toAdd (a j) = 0 := by
    have hz : toAdd (w k) = 0 := by rw [h k hkj', toAdd_one]
    rwa [hwk] at hz
  have hB : (t : ZMod p) * toAdd (b j) = 0 := by
    have hz : toAdd (w j) = 0 := by rw [h j (Ne.symm hne), toAdd_one]
    rw [hwj, hA, zero_add] at hz
    exact hz
  exact hβ_ne hB

theorem aPermutationFull_map_conj_eq_negOff_of_mem_closure_const_axis (hp : p.Prime)
    (hn : 2 ≤ n) {j : Fin n} {δ : MulAut (Fin n → Multiplicative (ZMod p))}
    (hδ : δ ∈ bSignedFull n p) {c : ZMod p} {a b w : Fin n → Multiplicative (ZMod p)}
    (ha : ∀ i k, a i = a k) (hb : ∀ k, k ≠ j → b k = 1) (hw : w ∈ Subgroup.closure {a, b})
    (hwa : w ∉ Subgroup.zpowers a) (hwδ : w = δ (fun _ => ofAdd c)) :
    (aPermutationFull n p).map (MulAut.conj δ).toMonoidHom =
      (aPermutationFull n p).map (MulAut.conj (negOff j)).toMonoidHom := by
  obtain ⟨s, t, hst⟩ := exists_zpow_mul_zpow_of_mem_closure_pair hw
  obtain ⟨ε, hεsign, hε⟩ := exists_signs_apply_const hδ
  obtain ⟨σ, hσsign, hσ_eq⟩ :=
    exists_const_sign_off_axis hp hn hεsign ha hb hε hst hwa hwδ
  have hbt : b ^ t ≠ 1 := zpow_ne_one_of_notMem_zpowers hwa hst
  have hβ_ne : (t : ZMod p) * toAdd (b j) ≠ 0 := by
    rw [← toAdd_zpow_apply]
    exact toAdd_zpow_ne_zero_of_axis hb hbt
  have hwj : toAdd (w j) =
      (s : ZMod p) * toAdd (a j) + (t : ZMod p) * toAdd (b j) := by
    rw [← hst, toAdd_zpow_mul_zpow_apply]
  have hwk : ∀ k, k ≠ j → toAdd (w k) = (s : ZMod p) * toAdd (a j) := by
    intro k hk
    rw [← hst, toAdd_zpow_mul_zpow_apply, hb k hk, toAdd_one, mul_zero, add_zero, ha k j]
  obtain ⟨k₁, hk₁⟩ :=
    Fintype.exists_ne_of_one_lt_card (by rw [Fintype.card_fin]; omega) j
  have hεj_ne : ε j ≠ σ := by
    intro heq
    have h1 : ε j * c = (s : ZMod p) * toAdd (a j) + (t : ZMod p) * toAdd (b j) := by
      rw [← hε c j, ← hwδ, hwj]
    have h2 : σ * c = (s : ZMod p) * toAdd (a j) := by
      rw [← hσ_eq k₁ hk₁, ← hε c k₁, ← hwδ, hwk k₁ hk₁]
    have hzero : (s : ZMod p) * toAdd (a j) + (t : ZMod p) * toAdd (b j) =
        (s : ZMod p) * toAdd (a j) + 0 := by
      rw [add_zero, ← h1, heq, h2]
    exact hβ_ne (add_left_cancel hzero)
  have hεj : ε j = -σ := by
    rcases eq_or_eq_neg_of_signs (hεsign j) hσsign with h | h
    · exact absurd h hεj_ne
    · exact h
  have hδ' : negOff j ∈ bSignedFull n p :=
    bCoordinateBlock_le_bSignedFull j (negOff_mem_bCoordinateBlock j)
  exact aPermutationFull_map_conj_eq_of_apply_one hδ hδ'
    (apply_const_one_eq_or_inv_negOff j hε hσsign hσ_eq hεj)

end CFSG.StandardType

end
