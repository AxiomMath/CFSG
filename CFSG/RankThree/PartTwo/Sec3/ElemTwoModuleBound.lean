module

public import CFSG.RankThree.PartTwo.Sec3.ElemNineAut
public import Mathlib.Data.Int.Star
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.PartTwo.Sec3

variable {V : Type*} [CommGroup V] {B : Type*} [CommGroup B]

@[expose] def commHom (τ : MulAut V) : V →* V where
  toFun v := v⁻¹ * τ v
  map_one' := by rw [inv_one, map_one, one_mul]
  map_mul' v w := by
    rw [map_mul, mul_inv]
    ac_rfl

theorem commHom_apply (τ : MulAut V) (v : V) : commHom τ v = v⁻¹ * τ v := rfl

theorem mem_ker_commHom {τ : MulAut V} {v : V} : v ∈ (commHom τ).ker ↔ τ v = v := by
  rw [MonoidHom.mem_ker, commHom_apply, inv_mul_eq_one, eq_comm]

@[expose] def avgThree (β : B →* MulAut V) (d : B) : V →* V where
  toFun v := v * β d v * β (d ^ 2) v
  map_one' := by rw [map_one, map_one, one_mul, one_mul]
  map_mul' v w := by
    simp only [map_mul]
    ac_rfl

theorem avgThree_apply (β : B →* MulAut V) (d : B) (v : V) :
    avgThree β d v = v * β d v * β (d ^ 2) v := rfl

theorem beta_apply_beta (β : B →* MulAut V) (a b : B) (v : V) : β a (β b v) = β (a * b) v := by
  rw [map_mul, MulAut.mul_apply]

@[expose] def fixedSub (β : B →* MulAut V) (b : B) : Subgroup V := (commHom (β b)).ker

theorem mem_fixedSub {β : B →* MulAut V} {b : B} {v : V} : v ∈ fixedSub β b ↔ β b v = v :=
  mem_ker_commHom

section Exponents

variable (hV2 : ∀ v : V, v * v = 1) (h3 : ∀ b : B, b ^ 3 = 1)
include hV2 h3

omit hV2 in
theorem beta_avgThree (β : B →* MulAut V) (d : B) (v : V) :
    β d (avgThree β d v) = avgThree β d v := by
  rw [avgThree_apply, map_mul, map_mul, beta_apply_beta, beta_apply_beta, ← pow_two,
    show d * d ^ 2 = 1 by rw [← pow_succ', h3], map_one, MulAut.one_apply]
  ac_rfl

omit h3 in
theorem avgThree_eq_self (β : B →* MulAut V) {d : B} {v : V} (hv : β d v = v) :
    avgThree β d v = v := by
  have hv2 : β (d ^ 2) v = v := by rw [pow_two, ← beta_apply_beta, hv, hv]
  rw [avgThree_apply, hv, hv2, hV2, one_mul]

omit hV2 h3 in
theorem beta_avgThree_comm (β : B →* MulAut V) (d b : B) (v : V) :
    β b (avgThree β d v) = avgThree β d (β b v) := by
  rw [avgThree_apply, avgThree_apply, map_mul, map_mul, beta_apply_beta, beta_apply_beta,
    beta_apply_beta, beta_apply_beta, mul_comm b d, mul_comm b (d ^ 2)]

omit hV2 in
theorem avgThree_beta_self (β : B →* MulAut V) (d : B) (v : V) :
    avgThree β d (β d v) = avgThree β d v := by
  rw [← beta_avgThree_comm, beta_avgThree h3]

end Exponents

section AvgAll

variable [Fintype B]

@[expose] def avgAll (β : B →* MulAut V) : V →* V where
  toFun v := ∏ b : B, β b v
  map_one' := by simp
  map_mul' v w := by simp only [map_mul, Finset.prod_mul_distrib]

theorem avgAll_apply (β : B →* MulAut V) (v : V) : avgAll β v = ∏ b : B, β b v := rfl

theorem avgAll_beta (β : B →* MulAut V) (a : B) (v : V) : avgAll β (β a v) = avgAll β v := by
  rw [avgAll_apply, avgAll_apply]
  simp_rw [beta_apply_beta]
  exact Fintype.prod_equiv (Equiv.mulRight a) _ _ (fun _ => rfl)

theorem beta_avgAll (β : B →* MulAut V) (a : B) (v : V) : β a (avgAll β v) = avgAll β v := by
  rw [avgAll_apply, map_prod]
  simp_rw [beta_apply_beta]
  exact Fintype.prod_equiv (Equiv.mulLeft a) _ _ (fun _ => rfl)

theorem avgAll_of_fixed (hV2 : ∀ v : V, v * v = 1) (h9 : Nat.card B = 9)
    (β : B →* MulAut V) {v : V} (hv : ∀ b, β b v = v) : avgAll β v = v := by
  rw [avgAll_apply]
  simp_rw [hv]
  rw [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card, h9]
  have : v ^ 9 = (v * v) ^ 4 * v := by rw [← pow_two, ← pow_mul, ← pow_succ]
  rw [this, hV2, one_pow, one_mul]

theorem avgAll_avgAll (hV2 : ∀ v : V, v * v = 1) (h9 : Nat.card B = 9) (β : B →* MulAut V)
    (v : V) : avgAll β (avgAll β v) = avgAll β v :=
  avgAll_of_fixed hV2 h9 β (fun b => beta_avgAll β b v)

theorem eq_one_of_mem_ker_of_fixed (hV2 : ∀ v : V, v * v = 1) (h9 : Nat.card B = 9)
    (β : B →* MulAut V) {w : V} (hw : avgAll β w = 1) (hfix : ∀ b, β b w = w) : w = 1 := by
  rw [← avgAll_of_fixed hV2 h9 β hfix, hw]

theorem avgAll_avgThree (β : B →* MulAut V) (d : B) {u : V} (hu : avgAll β u = 1) :
    avgAll β (avgThree β d u) = 1 := by
  rw [avgThree_apply, map_mul, map_mul, avgAll_beta, avgAll_beta, hu, one_mul, one_mul]

end AvgAll

section Coordinates

variable [Finite B] (h3 : ∀ b : B, b ^ 3 = 1) (h9 : Nat.card B = 9)
include h3 h9

omit [Finite B] h9 in
theorem exists_lt_three_of_mem_zpowers {a b : B} (hb : b ∈ Subgroup.zpowers a) :
    ∃ k : ℕ, k < 3 ∧ b = a ^ k := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  refine ⟨(k % 3).toNat, by omega, ?_⟩
  rw [zpow_eq_zpow_emod' k (h3 a), ← zpow_natCast,
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
  rfl

theorem not_mem_zpowers_of_basis {x y : B} (hx : x ≠ 1) (hy : y ∉ Subgroup.zpowers x) :
    y ∉ Subgroup.zpowers x ∧ x * y ∉ Subgroup.zpowers x ∧ x * y ^ 2 ∉ Subgroup.zpowers x ∧
      x ∉ Subgroup.zpowers y ∧ x * y ∉ Subgroup.zpowers y ∧ x * y ^ 2 ∉ Subgroup.zpowers y ∧
      x ∉ Subgroup.zpowers (x * y) ∧ y ∉ Subgroup.zpowers (x * y) ∧
      x * y ^ 2 ∉ Subgroup.zpowers (x * y) ∧ x ∉ Subgroup.zpowers (x * y ^ 2) ∧
      y ∉ Subgroup.zpowers (x * y ^ 2) ∧ x * y ∉ Subgroup.zpowers (x * y ^ 2) := by
  have hbij := bijective_pow_mul_pow h3 h9 hx hy
  have hc : ∀ i j i' j' : ℕ, i < 3 → j < 3 → i' < 3 → j' < 3 →
      x ^ i * y ^ j = x ^ i' * y ^ j' → i = i' ∧ j = j' := by
    intro i j i' j' hi hj hi' hj' h
    have := hbij.1 (a₁ := (⟨i, hi⟩, ⟨j, hj⟩)) (a₂ := (⟨i', hi'⟩, ⟨j', hj'⟩)) h
    simp only [Prod.mk.injEq, Fin.mk.injEq] at this
    exact this
  have hpow : ∀ (c : B) (k : ℕ), c ^ k = c ^ (k % 3) := pow_eq_pow_mod_three h3
  have hmul : ∀ i j k : ℕ, (x ^ i * y ^ j) ^ k = x ^ (i * k % 3) * y ^ (j * k % 3) := by
    intro i j k
    rw [mul_pow, ← pow_mul, ← pow_mul, hpow x, hpow y]
  have key : ∀ i j i' j' : ℕ, i < 3 → j < 3 → i' < 3 → j' < 3 →
      (∀ k : ℕ, k < 3 → ¬ (i = i' * k % 3 ∧ j = j' * k % 3)) →
      ∀ a c : B, a = x ^ i * y ^ j → c = x ^ i' * y ^ j' → a ∉ Subgroup.zpowers c := by
    intro i j i' j' hi hj hi' hj' hnk a c ha hc' hmem
    rw [ha, hc'] at hmem
    obtain ⟨k, hk3, hk⟩ := exists_lt_three_of_mem_zpowers h3 hmem
    rw [hmul] at hk
    exact hnk k hk3
      (hc i j _ _ hi hj (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) hk)
  have e1 : x = x ^ 1 * y ^ 0 := by rw [pow_one, pow_zero, mul_one]
  have e2 : y = x ^ 0 * y ^ 1 := by rw [pow_one, pow_zero, one_mul]
  have e3 : x * y = x ^ 1 * y ^ 1 := by rw [pow_one, pow_one]
  have e4 : x * y ^ 2 = x ^ 1 * y ^ 2 := by rw [pow_one]
  refine ⟨hy, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact key 1 1 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by intro k hk; interval_cases k <;> simp) _ _ e3 e1
  · exact key 1 2 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by intro k hk; interval_cases k <;> simp) _ _ e4 e1
  · exact key 1 0 0 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by intro k hk; interval_cases k <;> simp) _ _ e1 e2
  · exact key 1 1 0 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by intro k hk; interval_cases k <;> simp) _ _ e3 e2
  · exact key 1 2 0 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by intro k hk; interval_cases k <;> simp) _ _ e4 e2
  · exact key 1 0 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by intro k hk; interval_cases k <;> simp) _ _ e1 e3
  · exact key 0 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by intro k hk; interval_cases k <;> simp) _ _ e2 e3
  · exact key 1 2 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by intro k hk; interval_cases k <;> simp) _ _ e4 e3
  · exact key 1 0 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by intro k hk; interval_cases k <;> simp) _ _ e1 e4
  · exact key 0 1 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by intro k hk; interval_cases k <;> simp) _ _ e2 e4
  · exact key 1 1 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by intro k hk; interval_cases k <;> simp) _ _ e3 e4

theorem fixed_of_basis {x y : B} (hx : x ≠ 1) (hy : y ∉ Subgroup.zpowers x)
    (β : B →* MulAut V) {w : V} (hwx : β x w = w) (hwy : β y w = w) (b : B) : β b w = w := by
  obtain ⟨⟨i, j⟩, rfl⟩ := (bijective_pow_mul_pow h3 h9 hx hy).2 b
  have hpow : ∀ (a : B) (k : ℕ), β a w = w → β (a ^ k) w = w := by
    intro a k ha
    induction k with
    | zero => rw [pow_zero, map_one, MulAut.one_apply]
    | succ k ih => rw [pow_succ, ← beta_apply_beta, ha, ih]
  simp only
  rw [← beta_apply_beta, hpow y _ hwy, hpow x _ hwx]

end Coordinates


theorem card_eq_card_inf_ker_mul_card_map {G : Type*} [Group G] [Finite G] (f : G →* G)
    (W : Subgroup G) : Nat.card W = Nat.card ↥(W ⊓ f.ker) * Nat.card ↥(W.map f) := by
  set g := f.domRestrict W with hg
  have h1 := Subgroup.card_mul_index g.ker
  rw [Subgroup.index_ker, hg, MonoidHom.domRestrict_range] at h1
  rw [← h1]
  congr 1
  rw [MonoidHom.ker_domRestrict]
  exact Nat.card_congr
    { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_fixed_sq_le [Finite V] {W : Subgroup V} {δ τ : MulAut V}
    (hδW : ∀ w ∈ W, δ w ∈ W) (hδ3 : ∀ w, δ (δ (δ w)) = w)
    (hfree : ∀ w ∈ W, δ w = w → w = 1) (hinv : ∀ w, τ (δ w) = δ⁻¹ (τ w)) :
    Nat.card ↥(W ⊓ (commHom τ).ker) ^ 2 ≤ Nat.card W := by
  set X := W ⊓ (commHom τ).ker with hX
  have hmemX : ∀ {w : V}, w ∈ X ↔ w ∈ W ∧ τ w = w := fun {w} => by
    rw [hX, Subgroup.mem_inf, mem_ker_commHom]
  let F : X × X → W := fun p => ⟨p.1 * δ p.2, W.mul_mem (hmemX.mp p.1.2).1
    (hδW _ (hmemX.mp p.2.2).1)⟩
  have hF : Function.Injective F := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h' : (a : V) * δ b = a' * δ b' := congrArg Subtype.val h
    set c : V := b' * (b : V)⁻¹ with hc
    have hcX : c ∈ X := X.mul_mem b'.2 (X.inv_mem b.2)
    have hw : (a' : V)⁻¹ * a = δ c := by
      rw [hc, map_mul, map_inv]
      calc (a' : V)⁻¹ * a = (a' : V)⁻¹ * (a * δ b) * (δ b)⁻¹ := by group
        _ = (a' : V)⁻¹ * (a' * δ b') * (δ b)⁻¹ := by rw [h']
        _ = δ b' * (δ b)⁻¹ := by group
    have hwX : (a' : V)⁻¹ * a ∈ X := X.mul_mem (X.inv_mem a'.2) a.2
    have h1 : δ c = (δ⁻¹ : MulAut V) c := by
      rw [← hw, ← (hmemX.mp hwX).2, hw, hinv, (hmemX.mp hcX).2]
    have h2 : δ (δ c) = c := by rw [h1, MulAut.apply_inv_self]
    have h3c : δ c = c := by
      have := hδ3 c
      rw [h2] at this
      exact this
    have hc1 : c = 1 := hfree c (hmemX.mp hcX).1 h3c
    have hbb : b = b' := by
      apply Subtype.ext
      have : (b' : V) * (b : V)⁻¹ = 1 := hc1
      exact (mul_inv_eq_one.mp this).symm
    subst hbb
    have haa : (a : V) = a' := mul_right_cancel h'
    exact Prod.ext (Subtype.ext haa) rfl
  have := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_prod, ← pow_two] at this

theorem card_le_card_map_sq [Finite V] {W : Subgroup V} {τ : MulAut V}
    (h : Nat.card ↥(W ⊓ (commHom τ).ker) ^ 2 ≤ Nat.card W) :
    Nat.card W ≤ Nat.card ↥(W.map (commHom τ)) ^ 2 := by
  have hW := card_eq_card_inf_ker_mul_card_map (commHom τ) W
  set c := Nat.card ↥(W ⊓ (commHom τ).ker)
  set r := Nat.card ↥(W.map (commHom τ))
  have hc : c ≤ r := by
    rcases Nat.eq_zero_or_pos c with h0 | hpos
    · omega
    · rw [hW, pow_two] at h
      exact Nat.le_of_mul_le_mul_left h hpos
  rw [hW, pow_two]
  exact Nat.mul_le_mul_right r hc

section Lines

variable [Finite V] [Fintype B] (hV2 : ∀ v : V, v * v = 1) (h3 : ∀ b : B, b ^ 3 = 1)
  (h9 : Nat.card B = 9) (β : B →* MulAut V)
include hV2 h3 h9

omit [Finite V] hV2 in
theorem avgThree_avgThree_eq_avgAll {x y : B} (hx : x ≠ 1) (hy : y ∉ Subgroup.zpowers x)
    (v : V) : avgThree β x (avgThree β y v) = avgAll β v := by
  have hbij := bijective_pow_mul_pow h3 h9 hx hy
  have hw : ∀ a : B, β a (avgThree β y v) = β a v * β (a * y) v * β (a * y ^ 2) v :=
    fun a => by rw [avgThree_apply, map_mul, map_mul, beta_apply_beta, beta_apply_beta]
  rw [avgAll_apply, ← Fintype.prod_bijective _ hbij
    (fun p : Fin 3 × Fin 3 => β (x ^ (p.1 : ℕ) * y ^ (p.2 : ℕ)) v) (fun b => β b v)
    (fun _ => rfl), Fintype.prod_prod_type, Fin.prod_univ_three, Fin.prod_univ_three,
    Fin.prod_univ_three, Fin.prod_univ_three]
  rw [avgThree_apply β x, hw x, hw (x ^ 2), avgThree_apply β y]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_mul, mul_one,
    map_one, MulAut.one_apply]

omit [Finite V] in
theorem avgThree_mul_avgThree_mul {x y : B} (hx : x ≠ 1) (hy : y ∉ Subgroup.zpowers x)
    (v : V) :
    avgThree β x v * avgThree β y v * avgThree β (x * y) v * avgThree β (x * y ^ 2) v =
      v * avgAll β v := by
  rw [← avgThree_avgThree_eq_avgAll h3 h9 β hx hy v]
  have hw : ∀ a : B, β a (avgThree β y v) = β a v * β (a * y) v * β (a * y ^ 2) v :=
    fun a => by rw [avgThree_apply, map_mul, map_mul, beta_apply_beta, beta_apply_beta]
  rw [avgThree_apply β x (avgThree β y v), hw x, hw (x ^ 2)]
  simp only [avgThree_apply]
  rw [mul_pow, mul_pow, ← pow_mul y 2 2, pow_eq_pow_mod_three h3 y (2 * 2),
    show 2 * 2 % 3 = 1 from rfl, pow_one]
  set a := β x v
  set b := β (x ^ 2) v
  set c := β y v
  set e := β (y ^ 2) v
  set f := β (x * y) v
  set g := β (x ^ 2 * y ^ 2) v
  set h := β (x * y ^ 2) v
  set k := β (x ^ 2 * y) v
  calc v * a * b * (v * c * e) * (v * f * g) * (v * h * k)
      = (v * v) * (v * v) * (a * b * c * e * f * g * h * k) := by ac_rfl
    _ = (v * v) * (a * b * c * e * f * g * h * k) := by simp only [hV2, one_mul]
    _ = v * (v * c * e * (a * f * h) * (b * k * g)) := by ac_rfl

@[expose] def cU (β : B →* MulAut V) (d : B) : Subgroup V := fixedSub β d ⊓ (avgAll β).ker

omit [Finite V] hV2 h3 h9 in
theorem mem_cU {d : B} {v : V} : v ∈ cU β d ↔ β d v = v ∧ avgAll β v = 1 := by
  rw [cU, Subgroup.mem_inf, mem_fixedSub, MonoidHom.mem_ker]

omit [Finite V] in
theorem avgThree_eq_one_of_mem_cU {d d' : B} (hd : d ≠ 1) (hd' : d' ∉ Subgroup.zpowers d)
    {c : V} (hc : c ∈ cU β d') : avgThree β d c = 1 := by
  obtain ⟨hcd', hcU⟩ := (mem_cU β).mp hc
  apply eq_one_of_mem_ker_of_fixed hV2 h9 β (avgAll_avgThree β d hcU)
  apply fixed_of_basis h3 h9 hd hd' β
  · exact beta_avgThree h3 β d c
  · rw [beta_avgThree_comm, hcd']

omit [Finite V] hV2 h3 h9 in
theorem beta_mem_cU {d : B} {c : V} (hc : c ∈ cU β d) (b : B) : β b c ∈ cU β d := by
  obtain ⟨hcd, hcU⟩ := (mem_cU β).mp hc
  refine (mem_cU β).mpr ⟨?_, by rw [avgAll_beta, hcU]⟩
  rw [beta_apply_beta, mul_comm, ← beta_apply_beta, hcd]

omit [Finite V] in
theorem eq_one_of_mem_cU_of_fixed {d d' : B} (hd : d ≠ 1) (hd' : d' ∉ Subgroup.zpowers d)
    {c : V} (hc : c ∈ cU β d) (hcd' : β d' c = c) : c = 1 := by
  obtain ⟨hcd, hcU⟩ := (mem_cU β).mp hc
  exact eq_one_of_mem_ker_of_fixed hV2 h9 β hcU (fixed_of_basis h3 h9 hd hd' β hcd hcd')

theorem four_le_card_cU_of_ne_bot {d : B} (hd : d ≠ 1) (hne : cU β d ≠ ⊥) :
    4 ≤ Nat.card (cU β d) := by
  obtain ⟨⟨c, hc⟩, hc1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hc1 : c ≠ 1 := fun h => hc1' (Subtype.ext h)
  obtain ⟨d', hd'⟩ := exists_not_mem_zpowers h3 h9 d
  have hc₁ := beta_mem_cU β hc d'
  have hc₂ := beta_mem_cU β hc (d' ^ 2)
  have hne1 : β d' c ≠ c := fun h => hc1 (eq_one_of_mem_cU_of_fixed hV2 h3 h9 β hd hd' hc h)
  have hd'3 : d' ^ 3 = 1 := h3 d'
  have hne2 : β (d' ^ 2) c ≠ c := fun h => hne1 (by
    have : β d' (β (d' ^ 2) c) = β d' c := by rw [h]
    rw [beta_apply_beta, ← pow_succ', hd'3, map_one, MulAut.one_apply] at this
    exact this.symm)
  have hne3 : β d' c ≠ β (d' ^ 2) c := fun h => hne1 (by
    have : β (d' ^ 2) (β d' c) = β (d' ^ 2) (β (d' ^ 2) c) := by rw [h]
    rw [beta_apply_beta, beta_apply_beta, ← pow_succ, hd'3, map_one, MulAut.one_apply,
      ← pow_add, pow_eq_pow_mod_three h3, show (2 + 2) % 3 = 1 from rfl, pow_one] at this
    exact this.symm)
  have hb1 : ∀ b : B, β b c ≠ 1 := fun b h => hc1 (by
    rw [← map_one (β b)] at h; exact (β b).injective h)
  have hpow : β (d' ^ 2) = β d' ^ 2 := map_pow β d' 2
  have hne2' : (β d' ^ 2) c ≠ c := by rw [← hpow]; exact hne2
  have hne3' : β d' c ≠ (β d' ^ 2) c := by rw [← hpow]; exact hne3
  have hb2' : (β d' ^ 2) c ≠ 1 := by rw [← hpow]; exact hb1 _
  let F : Fin 4 → cU β d := ![⟨1, (cU β d).one_mem⟩, ⟨c, hc⟩, ⟨β d' c, hc₁⟩,
    ⟨β (d' ^ 2) c, hc₂⟩]
  have hF : Function.Injective F := by
    intro i j hij
    have h := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp [F] at h ⊢ <;>
      first
      | exact absurd h.symm hc1 | exact absurd h hc1
      | exact absurd h.symm (hb1 d') | exact absurd h (hb1 d')
      | exact absurd h.symm (hb1 _) | exact absurd h (hb1 _)
      | exact absurd h.symm hne1 | exact absurd h hne1
      | exact absurd h.symm hne2 | exact absurd h hne2
      | exact absurd h.symm hne3 | exact absurd h hne3
      | exact absurd h.symm hne2' | exact absurd h hne2'
      | exact absurd h.symm hne3' | exact absurd h hne3'
      | exact absurd h.symm hb2'
  have := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at this

omit hV2 h3 h9 in
theorem card_cU_le_of_conj {ν : MulAut V} {σ : MulAut B} (hν : ∀ b, ν * β b * ν⁻¹ = β (σ b))
    (d : B) : Nat.card (cU β d) ≤ Nat.card (cU β (σ d)) := by
  have happ : ∀ b v, β (σ b) (ν v) = ν (β b v) := fun b v => by
    rw [← hν b, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
  have hprod : ∀ v, ∏ b : B, β b (ν v) = ν (∏ b : B, β b v) := fun v => by
    rw [map_prod]
    exact (Fintype.prod_equiv σ.toEquiv (fun a => ν (β a v)) (fun b => β b (ν v))
      (fun a => (happ a v).symm)).symm
  let F : cU β d → cU β (σ d) := fun c => ⟨ν c, by
    obtain ⟨hcd, hcU⟩ := (mem_cU β).mp c.2
    refine (mem_cU β).mpr ⟨by rw [happ, hcd], ?_⟩
    rw [avgAll_apply, hprod, ← avgAll_apply, hcU, map_one]⟩
  exact Nat.card_le_card_of_injective F
    (fun c c' h => Subtype.ext (ν.injective (congrArg Subtype.val h)))

theorem four_le_card_cU (hβ : ∃ b v, β b v ≠ v)
    (htr : ∀ d d' : B, d ≠ 1 → d' ≠ 1 → ∃ (ν : MulAut V) (σ : MulAut B),
      σ d = d' ∧ ∀ b, ν * β b * ν⁻¹ = β (σ b))
    {d : B} (hd : d ≠ 1) : 4 ≤ Nat.card (cU β d) := by
  obtain ⟨b₀, v₀, hv₀⟩ := hβ
  set u := avgAll β v₀ * v₀ with hu
  have huU : avgAll β u = 1 := by rw [hu, map_mul, avgAll_avgAll hV2 h9, hV2]
  have hu1 : u ≠ 1 := by
    intro h
    apply hv₀
    have h' : avgAll β v₀ * v₀ = 1 := h
    have : v₀ = avgAll β v₀ :=
      (eq_inv_of_mul_eq_one_right h').trans (inv_eq_of_mul_eq_one_right (hV2 _))
    rw [this, beta_avgAll]
  obtain ⟨y, hy⟩ := exists_not_mem_zpowers h3 h9 d
  obtain ⟨-, h2, h3', -⟩ := not_mem_zpowers_of_basis h3 h9 hd hy
  have hspan := avgThree_mul_avgThree_mul hV2 h3 h9 β hd hy u
  rw [huU, mul_one] at hspan
  have hmem : ∀ a : B, avgThree β a u ∈ cU β a := fun a =>
    (mem_cU β).mpr ⟨beta_avgThree h3 β a u, avgAll_avgThree β a huU⟩
  obtain ⟨a, ha1, hane⟩ : ∃ a : B, a ≠ 1 ∧ avgThree β a u ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hu1
    rw [← hspan, hcon d hd, hcon y (ne_one_of_not_mem_zpowers hy),
      hcon (d * y) (ne_one_of_not_mem_zpowers h2), hcon (d * y ^ 2) (ne_one_of_not_mem_zpowers h3'),
      one_mul, one_mul, one_mul]
  have hne : cU β a ≠ ⊥ := Subgroup.ne_bot_iff_exists_ne_one.mpr
    ⟨⟨_, hmem a⟩, fun h => hane (congrArg Subtype.val h)⟩
  have hcard_a := four_le_card_cU_of_ne_bot hV2 h3 h9 β ha1 hne
  obtain ⟨ν, σ, hσ, hν⟩ := htr a d ha1 hd
  have := card_cU_le_of_conj β hν a
  rw [hσ] at this
  omega

omit [Finite V] in
theorem avgThree_prod_of_mem_cU {a : B} (ha : a ≠ 1) {c : V} (hc : c ∈ cU β a)
    {l : List (B × V)} (hl : ∀ p ∈ l, p.1 ∉ Subgroup.zpowers a ∧ p.2 ∈ cU β p.1) :
    avgThree β a (c * (l.map Prod.snd).prod) = c := by
  rw [map_mul, avgThree_eq_self hV2 β ((mem_cU β).mp hc).1, map_list_prod]
  have : ∀ w ∈ (l.map Prod.snd).map (avgThree β a), w = 1 := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
    exact avgThree_eq_one_of_mem_cU hV2 h3 h9 β ha (hl p hp).1 (hl p hp).2
  rw [List.prod_eq_one this, mul_one]

end Lines

section Bounds

variable [Finite V] [Fintype B] (hV2 : ∀ v : V, v * v = 1) (h3 : ∀ b : B, b ^ 3 = 1)
  (h9 : Nat.card B = 9) (β : B →* MulAut V)
include hV2 h3 h9

theorem eight_le_card_range_commHom (hβ : ∃ b v, β b v ≠ v)
    (htr : ∀ d d' : B, d ≠ 1 → d' ≠ 1 → ∃ (ν : MulAut V) (σ : MulAut B),
      σ d = d' ∧ ∀ b, ν * β b * ν⁻¹ = β (σ b))
    {τ : MulAut V} {d : B} (hd : d ≠ 1) (hτd : ∀ v, τ (β d v) = β d⁻¹ (τ v)) :
    8 ≤ Nat.card (commHom τ).range := by
  obtain ⟨y, hy⟩ := exists_not_mem_zpowers h3 h9 d
  obtain ⟨-, h2, h3', -, h5, h6, -, h8, h9', -, -, -⟩ := not_mem_zpowers_of_basis h3 h9 hd hy
  have hy1 := ne_one_of_not_mem_zpowers hy
  have hdy1 := ne_one_of_not_mem_zpowers h2
  set W := (avgThree β d).ker with hWdef
  have hsub : ∀ d' : B, d' ∉ Subgroup.zpowers d → cU β d' ≤ W := fun d' hd' c hc =>
    (MonoidHom.mem_ker).mpr (avgThree_eq_one_of_mem_cU hV2 h3 h9 β hd hd' hc)
  have hW64 : 64 ≤ Nat.card W := by
    let F : cU β y × cU β (d * y) × cU β (d * y ^ 2) → W := fun p =>
      ⟨p.1 * p.2.1 * p.2.2, W.mul_mem (W.mul_mem (hsub y hy p.1.2) (hsub _ h2 p.2.1.2))
        (hsub _ h3' p.2.2.2)⟩
    have hF : Function.Injective F := by
      rintro ⟨c₁, c₂, c₃⟩ ⟨c₁', c₂', c₃'⟩ h
      have h' : (c₁ : V) * c₂ * c₃ = c₁' * c₂' * c₃' := congrArg Subtype.val h
      set a₁ := (c₁ : V) * (c₁' : V)⁻¹
      set a₂ := (c₂ : V) * (c₂' : V)⁻¹
      set a₃ := (c₃ : V) * (c₃' : V)⁻¹
      have ha₁ : a₁ ∈ cU β y := (cU β y).mul_mem c₁.2 ((cU β y).inv_mem c₁'.2)
      have ha₂ : a₂ ∈ cU β (d * y) := (cU β _).mul_mem c₂.2 ((cU β _).inv_mem c₂'.2)
      have ha₃ : a₃ ∈ cU β (d * y ^ 2) := (cU β _).mul_mem c₃.2 ((cU β _).inv_mem c₃'.2)
      have hprod : a₁ * a₂ * a₃ = 1 := by
        calc a₁ * a₂ * a₃ = (c₁ * c₂ * c₃ : V) * (c₁' * c₂' * c₃' : V)⁻¹ := by
              simp only [a₁, a₂, a₃, mul_inv]; ac_rfl
          _ = 1 := by rw [h', mul_inv_cancel]
      have e₁ : a₁ = 1 := by
        have := avgThree_prod_of_mem_cU hV2 h3 h9 β hy1 ha₁
          (l := [(d * y, a₂), (d * y ^ 2, a₃)]) (by
            intro p hp
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
            rcases hp with rfl | rfl
            · exact ⟨h5, ha₂⟩
            · exact ⟨h6, ha₃⟩)
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at this
        rw [← mul_assoc, hprod, map_one] at this
        exact this.symm
      have e₂ : a₂ = 1 := by
        have := avgThree_prod_of_mem_cU hV2 h3 h9 β hdy1 ha₂
          (l := [(y, a₁), (d * y ^ 2, a₃)]) (by
            intro p hp
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
            rcases hp with rfl | rfl
            · exact ⟨h8, ha₁⟩
            · exact ⟨h9', ha₃⟩)
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at this
        rw [show a₂ * (a₁ * a₃) = a₁ * a₂ * a₃ by ac_rfl, hprod, map_one] at this
        exact this.symm
      have e₃ : a₃ = 1 := by rw [e₁, e₂, one_mul, one_mul] at hprod; exact hprod
      have k₁ : c₁ = c₁' := Subtype.ext (mul_inv_eq_one.mp e₁)
      have k₂ : c₂ = c₂' := Subtype.ext (mul_inv_eq_one.mp e₂)
      have k₃ : c₃ = c₃' := Subtype.ext (mul_inv_eq_one.mp e₃)
      rw [k₁, k₂, k₃]
    have hle := Nat.card_le_card_of_injective F hF
    rw [Nat.card_prod, Nat.card_prod] at hle
    have c₁ := four_le_card_cU hV2 h3 h9 β hβ htr hy1
    have c₂ := four_le_card_cU hV2 h3 h9 β hβ htr hdy1
    have c₃ := four_le_card_cU hV2 h3 h9 β hβ htr (ne_one_of_not_mem_zpowers h3')
    calc 64 = 4 * (4 * 4) := by norm_num
      _ ≤ _ := Nat.mul_le_mul c₁ (Nat.mul_le_mul c₂ c₃)
      _ ≤ _ := hle
  have hS3 := card_fixed_sq_le (W := W) (δ := β d) (τ := τ)
    (fun w hw => by
      rw [hWdef, MonoidHom.mem_ker, avgThree_beta_self h3]
      exact (MonoidHom.mem_ker).mp hw)
    (fun w => by
      rw [beta_apply_beta, beta_apply_beta, ← pow_two, ← pow_succ, h3, map_one,
        MulAut.one_apply])
    (fun w hw hfix => by
      rw [← avgThree_eq_self hV2 β hfix]
      exact (MonoidHom.mem_ker).mp hw)
    (fun w => by rw [hτd, map_inv])
  have hmap := card_le_card_map_sq hS3
  have hle : Nat.card ↥(W.map (commHom τ)) ≤ Nat.card (commHom τ).range :=
    Subgroup.card_le_of_le (Subgroup.map_le_range _ _)
  nlinarith

theorem sixteen_le_card_range_commHom (hβ : ∃ b v, β b v ≠ v)
    (htr : ∀ d d' : B, d ≠ 1 → d' ≠ 1 → ∃ (ν : MulAut V) (σ : MulAut B),
      σ d = d' ∧ ∀ b, ν * β b * ν⁻¹ = β (σ b))
    {τ : MulAut V} (hτ : ∀ b v, τ (β b v) = β b⁻¹ (τ v)) :
    16 ≤ Nat.card (commHom τ).range := by
  obtain ⟨x, hx'⟩ := exists_not_mem_zpowers h3 h9 (1 : B)
  have hx : x ≠ 1 := ne_one_of_not_mem_zpowers hx'
  obtain ⟨y, hy⟩ := exists_not_mem_zpowers h3 h9 x
  obtain ⟨_, h2, h3', h4, h5, h6, h7, h8, h9', h10, h11, h12⟩ :=
    not_mem_zpowers_of_basis h3 h9 hx hy
  have hy1 := ne_one_of_not_mem_zpowers hy
  have hxy1 := ne_one_of_not_mem_zpowers h2
  have hxy21 := ne_one_of_not_mem_zpowers h3'
  have hτcU : ∀ a : B, ∀ c ∈ cU β a, τ c ∈ cU β a := by
    intro a c hc
    obtain ⟨hca, hcU⟩ := (mem_cU β).mp hc
    have hca' : β a⁻¹ c = c := by
      conv_lhs => rw [← hca]
      rw [beta_apply_beta, inv_mul_cancel, map_one, MulAut.one_apply]
    refine (mem_cU β).mpr ⟨?_, ?_⟩
    · have := hτ a⁻¹ c
      rw [inv_inv, hca'] at this
      exact this.symm
    · rw [avgAll_apply]
      have : ∏ b : B, β b (τ c) = τ (∏ b : B, β b c) := by
        rw [map_prod]
        exact (Fintype.prod_equiv (Equiv.inv B) (fun a => τ (β a c)) (fun b => β b (τ c))
          (fun a => by rw [hτ a c]; rfl)).symm
      rw [this, ← avgAll_apply, hcU, map_one]
  have himg : ∀ a : B, ∀ w ∈ (cU β a).map (commHom τ), w ∈ cU β a := by
    intro a w hw
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hw
    exact (cU β a).mul_mem ((cU β a).inv_mem hc) (hτcU a c hc)
  have hline : ∀ a a' : B, a ≠ 1 → a' ∉ Subgroup.zpowers a →
      2 ≤ Nat.card ↥((cU β a).map (commHom τ)) := by
    intro a a' ha ha'
    have hS3 := card_fixed_sq_le (W := cU β a) (δ := β a') (τ := τ)
      (fun w hw => beta_mem_cU β hw a')
      (fun w => by
        rw [beta_apply_beta, beta_apply_beta, ← pow_two, ← pow_succ, h3, map_one,
          MulAut.one_apply])
      (fun w hw hfix => eq_one_of_mem_cU_of_fixed hV2 h3 h9 β ha ha' hw hfix)
      (fun w => by rw [hτ, map_inv])
    have hmap := card_le_card_map_sq hS3
    have h4 := four_le_card_cU hV2 h3 h9 β hβ htr ha
    nlinarith
  set M₁ := (cU β x).map (commHom τ)
  set M₂ := (cU β y).map (commHom τ)
  set M₃ := (cU β (x * y)).map (commHom τ)
  set M₄ := (cU β (x * y ^ 2)).map (commHom τ)
  have hR : ∀ {a : B}, (cU β a).map (commHom τ) ≤ (commHom τ).range := fun {a} =>
    Subgroup.map_le_range _ _
  let F : M₁ × M₂ × M₃ × M₄ → (commHom τ).range := fun p =>
    ⟨p.1 * p.2.1 * p.2.2.1 * p.2.2.2, ((commHom τ).range).mul_mem
      (((commHom τ).range).mul_mem (((commHom τ).range).mul_mem (hR p.1.2) (hR p.2.1.2))
        (hR p.2.2.1.2)) (hR p.2.2.2.2)⟩
  have hF : Function.Injective F := by
    rintro ⟨c₁, c₂, c₃, c₄⟩ ⟨c₁', c₂', c₃', c₄'⟩ h
    have h' : (c₁ : V) * c₂ * c₃ * c₄ = c₁' * c₂' * c₃' * c₄' := congrArg Subtype.val h
    set a₁ := (c₁ : V) * (c₁' : V)⁻¹
    set a₂ := (c₂ : V) * (c₂' : V)⁻¹
    set a₃ := (c₃ : V) * (c₃' : V)⁻¹
    set a₄ := (c₄ : V) * (c₄' : V)⁻¹
    have ha₁ : a₁ ∈ cU β x := (cU β x).mul_mem (himg x _ c₁.2) ((cU β x).inv_mem (himg x _ c₁'.2))
    have ha₂ : a₂ ∈ cU β y := (cU β y).mul_mem (himg y _ c₂.2) ((cU β y).inv_mem (himg y _ c₂'.2))
    have ha₃ : a₃ ∈ cU β (x * y) :=
      (cU β _).mul_mem (himg _ _ c₃.2) ((cU β _).inv_mem (himg _ _ c₃'.2))
    have ha₄ : a₄ ∈ cU β (x * y ^ 2) :=
      (cU β _).mul_mem (himg _ _ c₄.2) ((cU β _).inv_mem (himg _ _ c₄'.2))
    have hprod : a₁ * a₂ * a₃ * a₄ = 1 := by
      calc a₁ * a₂ * a₃ * a₄ = (c₁ * c₂ * c₃ * c₄ : V) * (c₁' * c₂' * c₃' * c₄' : V)⁻¹ := by
            simp only [a₁, a₂, a₃, a₄, mul_inv]; ac_rfl
        _ = 1 := by rw [h', mul_inv_cancel]
    have hsimp : ∀ (a b c e : V), a * (b * (c * e)) = a * b * c * e := fun a b c e => by
      ac_rfl
    have e₁ : a₁ = 1 := by
      have := avgThree_prod_of_mem_cU hV2 h3 h9 β hx ha₁
        (l := [(y, a₂), (x * y, a₃), (x * y ^ 2, a₄)]) (by
          intro p hp
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
          rcases hp with rfl | rfl | rfl
          · exact ⟨hy, ha₂⟩
          · exact ⟨h2, ha₃⟩
          · exact ⟨h3', ha₄⟩)
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at this
      rw [hsimp, hprod, map_one] at this
      exact this.symm
    have e₂ : a₂ = 1 := by
      have := avgThree_prod_of_mem_cU hV2 h3 h9 β hy1 ha₂
        (l := [(x, a₁), (x * y, a₃), (x * y ^ 2, a₄)]) (by
          intro p hp
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
          rcases hp with rfl | rfl | rfl
          · exact ⟨h4, ha₁⟩
          · exact ⟨h5, ha₃⟩
          · exact ⟨h6, ha₄⟩)
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at this
      rw [show a₂ * (a₁ * (a₃ * a₄)) = a₁ * a₂ * a₃ * a₄ by ac_rfl, hprod, map_one] at this
      exact this.symm
    have e₃ : a₃ = 1 := by
      have := avgThree_prod_of_mem_cU hV2 h3 h9 β hxy1 ha₃
        (l := [(x, a₁), (y, a₂), (x * y ^ 2, a₄)]) (by
          intro p hp
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
          rcases hp with rfl | rfl | rfl
          · exact ⟨h7, ha₁⟩
          · exact ⟨h8, ha₂⟩
          · exact ⟨h9', ha₄⟩)
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at this
      rw [show a₃ * (a₁ * (a₂ * a₄)) = a₁ * a₂ * a₃ * a₄ by ac_rfl, hprod, map_one] at this
      exact this.symm
    have e₄ : a₄ = 1 := by rw [e₁, e₂, e₃, one_mul, one_mul, one_mul] at hprod; exact hprod
    have k₁ : c₁ = c₁' := Subtype.ext (mul_inv_eq_one.mp e₁)
    have k₂ : c₂ = c₂' := Subtype.ext (mul_inv_eq_one.mp e₂)
    have k₃ : c₃ = c₃' := Subtype.ext (mul_inv_eq_one.mp e₃)
    have k₄ : c₄ = c₄' := Subtype.ext (mul_inv_eq_one.mp e₄)
    rw [k₁, k₂, k₃, k₄]
  have hle := Nat.card_le_card_of_injective F hF
  rw [Nat.card_prod, Nat.card_prod, Nat.card_prod] at hle
  have l₁ := hline x y hx hy
  have l₂ := hline y x hy1 h4
  have l₃ := hline (x * y) x hxy1 h7
  have l₄ := hline (x * y ^ 2) x hxy21 h10
  calc 16 = 2 * (2 * (2 * 2)) := by norm_num
    _ ≤ _ := Nat.mul_le_mul l₁ (Nat.mul_le_mul l₂ (Nat.mul_le_mul l₃ l₄))
    _ ≤ _ := hle

end Bounds

end CFSG.RankThree.PartTwo.Sec3
