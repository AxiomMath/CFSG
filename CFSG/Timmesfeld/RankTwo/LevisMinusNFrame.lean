module

public import CFSG.Timmesfeld.RankTwo.LevisMinusN
public import CFSG.Timmesfeld.ARS.CaseMFrame

public section

namespace CFSG.Timmesfeld.RankTwo

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
open CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.Steinberg CFSG.Timmesfeld.GradedPresentation
open scoped commutatorElement

section Roots

variable {n : ℕ}

theorem toStdB_apply_of_mem_roots {γ : Fin (n - 1) → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanB (n - 1)) ∅) (a : Fin (n - 1)) :
    toStdB (n - 1) γ a = 0 ∨ toStdB (n - 1) γ a = 1 ∨ toStdB (n - 1) γ a = -1 := by
  rcases exists_toStdB_eq_of_mem_roots n hγ with ⟨i, j, hij, s, t, h⟩ | ⟨i, s, h⟩
  · rw [h, Pi.add_apply]
    by_cases ha : a = i
    · subst ha
      rw [Pi.single_eq_same, Pi.single_apply, ite_eq_right hij, add_zero]
      rcases boolSign_eq_one_or_eq_neg_one s with hs | hs <;> simp [hs]
    · rw [Pi.single_apply, ite_eq_right ha, zero_add]
      by_cases hb : a = j
      · subst hb
        rw [Pi.single_eq_same]
        rcases boolSign_eq_one_or_eq_neg_one t with ht | ht <;> simp [ht]
      · simp [hb]
  · rw [h, Pi.single_apply]
    split_ifs
    · rcases boolSign_eq_one_or_eq_neg_one s with hs | hs <;> simp [hs]
    · simp

theorem toStdB_eq_zero_of_mem_roots {γ : Fin (n - 1) → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanB (n - 1)) ∅) {a a' a'' : Fin (n - 1)}
    (h1 : a ≠ a') (h2 : a ≠ a'') (h3 : a' ≠ a'') (ha : toStdB (n - 1) γ a ≠ 0)
    (ha' : toStdB (n - 1) γ a' ≠ 0) : toStdB (n - 1) γ a'' = 0 := by
  rcases exists_toStdB_eq_of_mem_roots n hγ with ⟨i, j, hij, s, t, h⟩ | ⟨i, s, h⟩
  · rw [h] at ha ha' ⊢
    have key : ∀ x, (Pi.single i (boolSign s) + Pi.single j (boolSign t) : Fin (n - 1) → ℤ) x ≠ 0 →
        x = i ∨ x = j := fun x hx => by
      by_contra hc
      push Not at hc
      exact hx (by simp [hc.1, hc.2])
    by_contra h''
    rcases key a ha with rfl | rfl <;> rcases key a' ha' with rfl | rfl <;>
      rcases key a'' h'' with rfl | rfl <;> simp_all
  · rw [h] at ha ha'
    have e1 : a = i := by
      by_contra hc
      exact ha (by simp [hc])
    have e2 : a' = i := by
      by_contra hc
      exact ha' (by simp [hc])
    exact absurd (e1.trans e2.symm) h1

theorem eq_smul_add_smul {m : ℕ} {γ : Fin m → ℤ} {i j : Fin m} (hij : i ≠ j)
    (h : ∀ l, l ≠ i → l ≠ j → γ l = 0) : γ = γ i • Pi.single i 1 + γ j • Pi.single j 1 := by
  funext l
  by_cases hi : l = i
  · subst hi
    simp [hij]
  · by_cases hj : l = j
    · subst hj
      simp [hi]
    · simp [hi, hj, h l hi hj]

theorem ht_smul_add_smul {m : ℕ} (i j : Fin m) (p q : ℤ) :
    Steinberg.ht (p • Pi.single i 1 + q • Pi.single j 1 : Fin m → ℤ) = p + q := by
  rw [ht_add]
  simp only [Steinberg.ht, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  rw [show ∑ l, (Pi.single i 1 : Fin m → ℤ) l = 1 from ht_single i,
    show ∑ l, (Pi.single j 1 : Fin m → ℤ) l = 1 from ht_single j]
  ring

theorem toStdB_smul_add_smul_apply {i j : Fin (n - 1)} (p q : ℤ) (a : Fin (n - 1)) :
    toStdB (n - 1) (p • Pi.single i 1 + q • Pi.single j 1) a =
      (if a.val = i.val then p else 0) + (if a.val = j.val then q else 0) -
        ((if a.val = i.val + 1 then p else 0) + (if a.val = j.val + 1 then q else 0)) := by
  simp only [toStdB, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, Fin.ext_iff]
  split_ifs <;> omega

theorem toStdB_pair_apply_fst {i j : Fin (n - 1)} (hij : i.val < j.val) (p q : ℤ) :
    toStdB (n - 1) (p • Pi.single i 1 + q • Pi.single j 1) i = p := by
  rw [toStdB_smul_add_smul_apply]
  split_ifs <;> omega

theorem toStdB_adj_apply_snd {i j : Fin (n - 1)} (hj : j.val = i.val + 1) (p q : ℤ) :
    toStdB (n - 1) (p • Pi.single i 1 + q • Pi.single j 1) j = q - p := by
  rw [toStdB_smul_add_smul_apply]
  split_ifs <;> omega

theorem toStdB_A2_apply_thd {i j k : Fin (n - 1)} (hj : j.val = i.val + 1)
    (hk : k.val = i.val + 2) (p q : ℤ) :
    toStdB (n - 1) (p • Pi.single i 1 + q • Pi.single j 1) k = -q := by
  rw [toStdB_smul_add_smul_apply]
  split_ifs <;> omega

theorem toStdB_A1A1_apply_succ {i j : Fin (n - 1)} (hij : i.val + 2 ≤ j.val) (p q : ℤ) :
    toStdB (n - 1) (p • Pi.single i 1 + q • Pi.single j 1) ⟨i.val + 1, by omega⟩ = -p := by
  rw [toStdB_smul_add_smul_apply]
  dsimp only
  split_ifs <;> omega

theorem toStdB_A1A1_apply_snd {i j : Fin (n - 1)} (hij : i.val + 2 ≤ j.val) (p q : ℤ) :
    toStdB (n - 1) (p • Pi.single i 1 + q • Pi.single j 1) j = q := by
  rw [toStdB_smul_add_smul_apply]
  split_ifs <;> omega

theorem minus_pos_roots_A2 {i j : Fin (n - 1)} (hi : i.val + 3 < n) (hj : j.val = i.val + 1)
    {γ : Fin (n - 1) → ℤ} (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanB (n - 1)) ∅)
    (hs : ∀ l, l ≠ i → l ≠ j → γ l = 0) (hp : 0 < Steinberg.ht γ) :
    γ = Pi.single i 1 ∨ γ = Pi.single i 1 + Pi.single j 1 ∨ γ = Pi.single j 1 := by
  have hij : i ≠ j := Fin.ne_of_val_ne (by omega)
  have e := eq_smul_add_smul hij hs
  generalize γ i = p at e
  generalize γ j = q at e
  rw [e] at hγ hp ⊢
  have h1 := toStdB_apply_of_mem_roots hγ i
  have h2 := toStdB_apply_of_mem_roots hγ ⟨i.val + 2, by omega⟩
  rw [toStdB_pair_apply_fst (by omega) p q] at h1
  rw [toStdB_A2_apply_thd hj rfl p q] at h2
  rw [ht_smul_add_smul] at hp
  have hq' : q = 0 ∨ q = 1 ∨ q = -1 := by omega
  rcases h1 with rfl | rfl | rfl <;> rcases hq' with rfl | rfl | rfl <;>
    first
    | omega
    | simp

theorem minus_pos_roots_B2 {i j : Fin (n - 1)} (hj : j.val = i.val + 1) {γ : Fin (n - 1) → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanB (n - 1)) ∅)
    (hs : ∀ l, l ≠ i → l ≠ j → γ l = 0) (hp : 0 < Steinberg.ht γ) :
    γ = Pi.single i 1 ∨ γ = Pi.single j 1 ∨ γ = Pi.single i 1 + Pi.single j 1 ∨
      γ = Pi.single i 1 + 2 • Pi.single j 1 := by
  have hij : i ≠ j := Fin.ne_of_val_ne (by omega)
  have e := eq_smul_add_smul hij hs
  generalize γ i = p at e
  generalize γ j = q at e
  rw [e] at hγ hp ⊢
  have h1 := toStdB_apply_of_mem_roots hγ i
  have h2 := toStdB_apply_of_mem_roots hγ j
  rw [toStdB_pair_apply_fst (by omega) p q] at h1
  rw [toStdB_adj_apply_snd hj p q] at h2
  rw [ht_smul_add_smul] at hp
  have hp' := h1
  have hq' := h2
  have e2 : (2 : ℤ) • (Pi.single j 1 : Fin (n - 1) → ℤ) = 2 • Pi.single j 1 := by
    rw [two_zsmul, two_nsmul]
  rcases hp' with rfl | rfl | rfl
  · obtain rfl | rfl | rfl : q = 0 ∨ q = 1 ∨ q = -1 := by omega
    · omega
    · right; left; simp
    · omega
  · obtain rfl | rfl | rfl : q = 1 ∨ q = 2 ∨ q = 0 := by omega
    · right; right; left; simp
    · right; right; right; rw [one_smul, e2]
    · left; simp
  · omega

theorem minus_pos_roots_A1A1 {i j : Fin (n - 1)} (hij : i.val + 2 ≤ j.val) {γ : Fin (n - 1) → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanB (n - 1)) ∅)
    (hs : ∀ l, l ≠ i → l ≠ j → γ l = 0) (hp : 0 < Steinberg.ht γ) :
    γ = Pi.single i 1 ∨ γ = Pi.single j 1 := by
  have hne : i ≠ j := Fin.ne_of_val_ne (by omega)
  have e := eq_smul_add_smul hne hs
  generalize γ i = p at e
  generalize γ j = q at e
  rw [e] at hγ hp ⊢
  have h1 := toStdB_apply_of_mem_roots hγ i
  have h3 := toStdB_apply_of_mem_roots hγ j
  have hz := toStdB_eq_zero_of_mem_roots hγ (a := i) (a' := j)
    (a'' := ⟨i.val + 1, by omega⟩) hne (Fin.ne_of_val_ne (by simp))
    (Fin.ne_of_val_ne (by simp; omega))
  rw [toStdB_pair_apply_fst (by omega) p q] at h1 hz
  rw [toStdB_A1A1_apply_snd hij p q] at h3 hz
  rw [toStdB_A1A1_apply_succ hij p q] at hz
  rw [ht_smul_add_smul] at hp
  have hpq : p = 0 ∨ q = 0 := by
    by_contra hc
    push Not at hc
    exact hc.1 (neg_eq_zero.1 (hz hc.1 hc.2))
  rcases h1 with rfl | rfl | rfl <;> rcases h3 with rfl | rfl | rfl <;>
    first
    | omega
    | simp

theorem minus_roots_self {k : Fin (n - 1)} {γ : Fin (n - 1) → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanB (n - 1)) ∅) (hs : ∀ l, l ≠ k → γ l = 0) :
    γ = Pi.single k 1 ∨ γ = -Pi.single k 1 := by
  have e : γ = γ k • Pi.single k 1 := funext fun l => by
    by_cases hl : l = k
    · subst hl
      simp
    · simp [hs l hl, hl]
  generalize γ k = p at e
  rw [e] at hγ ⊢
  have h1 := toStdB_apply_of_mem_roots hγ k
  have h0 := RootSystem.ne_zero_of_mem_roots _ ∅ hγ
  have v : toStdB (n - 1) (p • Pi.single k 1) k = p := by
    simp only [toStdB, Pi.smul_apply, smul_eq_mul, Pi.single_apply, Fin.ext_iff]
    split_ifs <;> omega
  rw [v] at h1
  rcases h1 with rfl | rfl | rfl
  · exact absurd (zero_smul ℤ _) h0
  · left; simp
  · right; simp

end Roots

section Prod

variable {n : ℕ} {F : Type} [Field F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

theorem ne_of_apply_ne' {m : ℕ} {v w : Fin m → ℤ} (k : Fin m) (h : v k ≠ w k) : v ≠ w :=
  fun e => h (congrFun e k)

theorem minus_prod_A2 {i : Fin (n - 1)} (hi : i.val + 3 < n) :
    ProdInjectiveFor (minusRootGroup n hirr) ([Pi.single i 1,
      Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1,
      Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1] :
        List (Fin (n - 1) → ℤ)) := by
  have hne : i ≠ (⟨i.val + 1, by omega⟩ : Fin (n - 1)) := Fin.ne_of_val_ne (by simp)
  refine minusDatum_prodInjective n hirr 1 _ ?_ ?_ ?_ ?_
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true]
    refine ⟨⟨ne_of_apply_ne' i ?_, ne_of_apply_ne' (⟨i.val + 1, by omega⟩ : Fin (n - 1)) ?_⟩,
      ne_of_apply_ne' i ?_⟩ <;> simp [hne, Ne.symm hne]
  · intro γ hγ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
    rcases hγ with rfl | rfl | rfl
    · exact (minusLong_single (by omega)).mem_roots
    · exact (minusLong_single (k := ⟨i.val + 1, by omega⟩) (by simp; omega)).mem_roots
    · exact (minusLong_A2sum hi).mem_roots
  · intro γ hγ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
    rcases hγ with rfl | rfl | rfl <;> simp [ht_add, ht_single]
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, ht_add, ht_single]
    norm_num

theorem minus_prod_B2 {i : Fin (n - 1)} (hi : i.val + 3 = n) :
    ProdInjectiveFor (minusRootGroup n hirr) ([Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1,
      Pi.single i 1, Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1,
      Pi.single i 1 + 2 • Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1] :
        List (Fin (n - 1) → ℤ)) := by
  have hne : i ≠ (⟨i.val + 1, by omega⟩ : Fin (n - 1)) := Fin.ne_of_val_ne (by simp)
  refine minusDatum_prodInjective n hirr 1 _ ?_ ?_ ?_ ?_
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true]
    refine ⟨⟨ne_of_apply_ne' i ?_, ne_of_apply_ne' i ?_, ne_of_apply_ne' i ?_⟩,
      ⟨ne_of_apply_ne' (⟨i.val + 1, by omega⟩ : Fin (n - 1)) ?_,
        ne_of_apply_ne' (⟨i.val + 1, by omega⟩ : Fin (n - 1)) ?_⟩,
      ne_of_apply_ne' (⟨i.val + 1, by omega⟩ : Fin (n - 1)) ?_⟩ <;> simp [hne, Ne.symm hne]
  · intro γ hγ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
    rcases hγ with rfl | rfl | rfl | rfl
    · exact (minusShort_single (k := ⟨i.val + 1, by omega⟩) (by simp; omega)).mem_roots
    · exact (minusLong_single (by omega)).mem_roots
    · exact (minusShort_B2sum hi).mem_roots
    · exact (minusLong_B2long hi).mem_roots
  · intro γ hγ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
    rcases hγ with rfl | rfl | rfl | rfl <;> simp only [ht_add, ht_nsmul, ht_single] <;> norm_num
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, ht_add, ht_nsmul, ht_single]
    norm_num

theorem minus_prod_A1A1 {i j : Fin (n - 1)} (hij : i.val + 2 ≤ j.val)
    (hi : MinusLong n (Pi.single i 1))
    (hj : MinusLong n (Pi.single j 1) ∨ MinusShort n (Pi.single j 1)) :
    ProdInjectiveFor (minusRootGroup n hirr) ([Pi.single i 1, Pi.single j 1] :
      List (Fin (n - 1) → ℤ)) := by
  have hne : i ≠ j := Fin.ne_of_val_ne (by omega)
  refine minusDatum_prodInjective n hirr 1 _ ?_ ?_ ?_ ?_
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      List.nodup_nil, and_true, not_false_eq_true]
    exact ne_of_apply_ne' i (by simp [hne])
  · intro γ hγ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
    rcases hγ with rfl | rfl
    · exact hi.mem_roots
    · rcases hj with hj | hj
      · exact hj.mem_roots
      · exact hj.mem_roots
  · intro γ hγ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
    rcases hγ with rfl | rfl <;> simp [ht_single]
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, ht_single]
    norm_num

end Prod

section PairMaps

variable {n : ℕ} {F : Type} [Field F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

@[expose] def minusA2r (i : Fin (n - 1)) (h : i.val + 3 < n) : Fin 3 → Fin (n - 1) → ℤ :=
  ![Pi.single i 1, Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1,
    Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1]

@[expose] def minusB2r (i : Fin (n - 1)) (h : i.val + 3 = n) : Fin 4 → Fin (n - 1) → ℤ :=
  ![Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1,
    Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1,
    Pi.single i 1 + 2 • Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1, Pi.single i 1]

@[expose] noncomputable def minusB2x (i : Fin (n - 1)) (h : i.val + 3 = n) :
    ∀ k, tb2Par F k → spinGroup (quadMinus n F b c)
  | 0 => minusXS n hirr (minusB2r i h 0)
  | 1 => minusXS n hirr (minusB2r i h 1)
  | 2 => minusXL n b c (minusB2r i h 2)
  | 3 => minusXL n b c (minusB2r i h 3)

@[expose] def minusB2psi {G : Type*} (ψL : (Fin (n - 1) → ℤ) → F → G)
    (ψS : (Fin (n - 1) → ℤ) → (Fin 2 → F) → G) (i : Fin (n - 1)) (h : i.val + 3 = n) :
    (Σ k, tb2Par F k) → G
  | ⟨0, p⟩ => ψS (minusB2r i h 0) p
  | ⟨1, p⟩ => ψS (minusB2r i h 1) p
  | ⟨2, x⟩ => ψL (minusB2r i h 2) x
  | ⟨3, x⟩ => ψL (minusB2r i h 3) x

@[expose] def minusA1r (i k : Fin (n - 1)) : Fin 2 → Fin (n - 1) → ℤ :=
  ![Pi.single i 1, Pi.single k 1]

@[expose] noncomputable def minusA1x (i k : Fin (n - 1)) :
    ∀ l, ma1Par F l → spinGroup (quadMinus n F b c)
  | 0 => minusXL n b c (minusA1r i k 0)
  | 1 => minusXS n hirr (minusA1r i k 1)

@[expose] def minusA1psi {G : Type*} (ψL : (Fin (n - 1) → ℤ) → F → G)
    (ψS : (Fin (n - 1) → ℤ) → (Fin 2 → F) → G) (i k : Fin (n - 1)) : (Σ l, ma1Par F l) → G
  | ⟨0, x⟩ => ψL (minusA1r i k 0) x
  | ⟨1, p⟩ => ψS (minusA1r i k 1) p

end PairMaps

section Frame

variable {n : ℕ} {F : Type} [Field F] {b c : F} {G : Type*} [Group G]

noncomputable abbrev ΦMinus (n : ℕ) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    Steinberg.RootSystem (Fin (n - 1)) :=
  Steinberg.RootSystem.ofCartan (minusDatum n hirr).isFiniteType (minusDatum n hirr).divisible

structure IsMinusFrame (n : ℕ) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] (ψL : (Fin (n - 1) → ℤ) → F → G)
    (ψS : (Fin (n - 1) → ℤ) → (Fin 2 → F) → G) : Prop where
  addL : ∀ i j : Fin (n - 1), ∀ γ ∈ pairRoots (minusDatum n hirr) i j, MinusLong n γ →
    ∀ x y, ψL γ (x + y) = ψL γ x * ψL γ y
  addS : ∀ i j : Fin (n - 1), ∀ γ ∈ pairRoots (minusDatum n hirr) i j, MinusShort n γ →
    ∀ p q, ψS γ (p + q) = ψS γ p * ψS γ q
  commA2 : ∀ (i : Fin (n - 1)) (h : i.val + 3 < n) (s t : F),
    ⁅ψL (Pi.single i 1) s, ψL (Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) t⁆ =
      ψL (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) (s * t)
  commuteA2l : ∀ (i : Fin (n - 1)) (h : i.val + 3 < n) (s t : F),
    Commute (ψL (Pi.single i 1) s)
      (ψL (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) t)
  commuteA2r : ∀ (i : Fin (n - 1)) (h : i.val + 3 < n) (s t : F),
    Commute (ψL (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) s)
      (ψL (Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) t)
  commB2 : ∀ (i : Fin (n - 1)) (h : i.val + 3 = n) (p : Fin 2 → F) (s : F),
    ⁅ψS (Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) p, ψL (Pi.single i 1) s⁆ =
      ψS (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) (s • p) *
        ψL (Pi.single i 1 + 2 • Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1)
          (s * planeNorm b c p)
  commB2' : ∀ (i : Fin (n - 1)) (h : i.val + 3 = n) (p q : Fin 2 → F),
    ⁅ψS (Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) p,
        ψS (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) q⁆ =
      ψL (Pi.single i 1 + 2 • Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1)
        (polarPlane b c p q)
  commuteB2_b_2ab : ∀ (i : Fin (n - 1)) (h : i.val + 3 = n) (p : Fin 2 → F) (s : F),
    Commute (ψS (Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) p)
      (ψL (Pi.single i 1 + 2 • Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) s)
  commuteB2_ab_2ab : ∀ (i : Fin (n - 1)) (h : i.val + 3 = n) (p : Fin 2 → F) (s : F),
    Commute (ψS (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) p)
      (ψL (Pi.single i 1 + 2 • Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) s)
  commuteB2_ab_a : ∀ (i : Fin (n - 1)) (h : i.val + 3 = n) (p : Fin 2 → F) (s : F),
    Commute (ψS (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) p)
      (ψL (Pi.single i 1) s)
  commuteB2_2ab_a : ∀ (i : Fin (n - 1)) (h : i.val + 3 = n) (s t : F),
    Commute (ψL (Pi.single i 1 + 2 • Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) s)
      (ψL (Pi.single i 1) t)
  commuteA1A1L : ∀ i j : Fin (n - 1), i.val + 2 ≤ j.val → j.val + 2 < n → ∀ s t : F,
    Commute (ψL (Pi.single i 1) s) (ψL (Pi.single j 1) t)
  commuteA1A1S : ∀ i k : Fin (n - 1), i.val + 2 ≤ k.val → k.val + 2 = n →
    ∀ (s : F) (p : Fin 2 → F), Commute (ψL (Pi.single i 1) s) (ψS (Pi.single k 1) p)
  weyl : ∀ i j : Fin (n - 1), i.val < j.val → ∃ ñ : Fin (n - 1) → G, ∀ k, (k = i ∨ k = j) →
    ∀ γ ∈ pairRoots (minusDatum n hirr) i j,
      (MinusLong n γ → ∀ a, ñ k * ψL γ a * (ñ k)⁻¹ = ψL ((ΦMinus n hirr).refl k γ) a) ∧
      (MinusShort n γ → ∀ p, ñ k * ψS γ p * (ñ k)⁻¹ =
        ψS ((ΦMinus n hirr).refl k γ) (if k.val + 2 = n then planeRefl b c planeOne p else p))
  rankL : ∀ k : Fin (n - 1), k.val + 2 < n → ∃ Θ : Matrix.SpecialLinearGroup (Fin 2) F →* G,
    (∀ x, Θ (sl2Upper x) = ψL (Pi.single k 1) x) ∧ ∀ x, Θ (sl2Lower x) = ψL (-Pi.single k 1) x
  rankS : ∀ k : Fin (n - 1), k.val + 2 = n → ∃ Θ : SL2E b c →* G,
    (∀ t, Θ (sl2Upper t) = ψS (Pi.single k 1) (fieldCoord t)) ∧
      ∀ t, Θ (sl2Lower t) = ψS (-Pi.single k 1) (starCoord t)
  gen : Subgroup.closure (⋃ k : Fin (n - 1), if k.val + 2 < n then
      Set.range (ψL (Pi.single k 1)) ∪ Set.range (ψL (-Pi.single k 1))
    else Set.range (ψS (Pi.single k 1)) ∪ Set.range (ψS (-Pi.single k 1))) = ⊤
  nt : ∃ k : Fin (n - 1), k.val + 2 < n ∧ ∃ x, ψL (Pi.single k 1) x ≠ 1

variable (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

theorem minusWeyl_conj_mem [CharP F 2] (k : Fin (n - 1)) {γ : Fin (n - 1) → ℤ}
    (hγ : γ ∈ (minusDatum n hirr).roots) {x : spinGroup (quadMinus n F b c)}
    (hx : x ∈ (minusDatum n hirr).rootGroup γ) :
    minusWeyl n hirr k * x * (minusWeyl n hirr k)⁻¹ ∈
      (minusDatum n hirr).rootGroup ((ΦMinus n hirr).refl k γ) := by
  rcases minusLong_or_minusShort hγ with hL | hS
  · obtain ⟨a, rfl⟩ := exists_minusXL_eq hirr hL hx
    rw [minusWeyl_conj_minusXL hirr k hL a]
    exact minusXL_mem hirr (hL.reflection k) a
  · obtain ⟨p, rfl⟩ := exists_minusXS_eq hirr hS hx
    rw [minusWeyl_conj_minusXS hirr k hS p]
    exact minusXS_mem hirr (hS.reflection k) _

theorem pairRoots_comm_minusN {i j : Fin (minusDatum n hirr).rank} :
    pairRoots (minusDatum n hirr) i j = pairRoots (minusDatum n hirr) j i := by
  ext γ
  exact ⟨fun h => ⟨h.1, fun k hj hi => h.2 k hi hj⟩, fun h => ⟨h.1, fun k hi hj => h.2 k hj hi⟩⟩

namespace IsMinusFrame

variable {hirr} [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] {ψL : (Fin (n - 1) → ℤ) → F → G}
  {ψS : (Fin (n - 1) → ℤ) → (Fin 2 → F) → G} (h : IsMinusFrame n hirr ψL ψS)
include h

omit [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] h in
theorem compat [CharP F 2] {i j : Fin (n - 1)} {ñ : Fin (n - 1) → G}
    (hñ : ∀ k, (k = i ∨ k = j) → ∀ γ ∈ pairRoots (minusDatum n hirr) i j,
      (MinusLong n γ → ∀ a, ñ k * ψL γ a * (ñ k)⁻¹ = ψL ((ΦMinus n hirr).refl k γ) a) ∧
      (MinusShort n γ → ∀ p, ñ k * ψS γ p * (ñ k)⁻¹ =
        ψS ((ΦMinus n hirr).refl k γ) (if k.val + 2 = n then planeRefl b c planeOne p else p))) :
    ∀ k, (k = i ∨ k = j) → ∀ γ ∈ pairRoots (minusDatum n hirr) i j,
      ∀ (x : (minusDatum n hirr).rootGroup γ)
        (y : (minusDatum n hirr).rootGroup ((ΦMinus n hirr).refl k γ)),
        (y : spinGroup (quadMinus n F b c)) = minusWeyl n hirr k * x * (minusWeyl n hirr k)⁻¹ →
          ñ k * minusPhiOf hirr ψL ψS γ x * (ñ k)⁻¹ =
            minusPhiOf hirr ψL ψS ((ΦMinus n hirr).refl k γ) y := by
  intro k hk γ hγ x y hy
  obtain ⟨x, hx⟩ := x
  rcases minusLong_or_minusShort hγ.1 with hL | hS
  · obtain ⟨a, rfl⟩ := exists_minusXL_eq hirr hL hx
    have hL' : MinusLong n ((ΦMinus n hirr).refl k γ) := hL.reflection k
    have e : y = ⟨minusXL n b c ((ΦMinus n hirr).refl k γ) a, minusXL_mem hirr hL' a⟩ :=
      Subtype.ext (hy.trans (minusWeyl_conj_minusXL hirr k hL a))
    rw [e, minusPhiOf_long hirr ψL ψS hL a, minusPhiOf_long hirr ψL ψS hL' a]
    exact (hñ k hk γ hγ).1 hL a
  · obtain ⟨p, rfl⟩ := exists_minusXS_eq hirr hS hx
    have hS' : MinusShort n ((ΦMinus n hirr).refl k γ) := hS.reflection k
    have e : y = ⟨minusXS n hirr ((ΦMinus n hirr).refl k γ)
        (if k.val + 2 = n then planeRefl b c planeOne p else p), minusXS_mem hirr hS' _⟩ :=
      Subtype.ext (hy.trans (minusWeyl_conj_minusXS hirr k hS p))
    rw [e, minusPhiOf_short hirr ψL ψS hS p, minusPhiOf_short hirr ψL ψS hS' _]
    exact (hñ k hk γ hγ).2 hS p

theorem hrank [CharP F 2] [Finite F] (k : Fin (n - 1)) :
    ExtendsToHom (minusDatum n hirr).rootGroup {Pi.single k 1, -Pi.single k 1}
      (minusPhiOf hirr ψL ψS) := by
  by_cases hk : k.val + 2 < n
  · obtain ⟨φK, hinj, hU, hLo⟩ := exists_sl2_minusXL (b := b) (c := c) hk
    obtain ⟨Θ, hΘU, hΘL⟩ := h.rankL k hk
    refine extendsToHom_pair_of_hom hinj Θ (fun z => ?_) (fun z => ?_)
    · obtain ⟨z, hz⟩ := z
      obtain ⟨x, rfl⟩ := exists_minusXL_eq hirr (minusLong_single hk) hz
      exact ⟨x, hU x, (minusPhiOf_long hirr ψL ψS (minusLong_single hk) x hz).trans (hΘU x).symm⟩
    · obtain ⟨z, hz⟩ := z
      obtain ⟨x, rfl⟩ := exists_minusXL_eq hirr (minusLong_neg_single hk) hz
      exact ⟨x, hLo x,
        (minusPhiOf_long hirr ψL ψS (minusLong_neg_single hk) x hz).trans (hΘL x).symm⟩
  · have hk' : k.val + 2 = n := by have := k.isLt; omega
    obtain ⟨φK, hinj, hU, hLo⟩ := exists_sl2_minusXS hirr hk'
    obtain ⟨Θ, hΘU, hΘL⟩ := h.rankS k hk'
    refine extendsToHom_pair_of_hom hinj Θ (fun z => ?_) (fun z => ?_)
    · obtain ⟨z, hz⟩ := z
      obtain ⟨p, rfl⟩ := exists_minusXS_eq hirr (minusShort_single hk') hz
      obtain ⟨t, rfl⟩ := exists_fieldCoord_eq (b := b) (c := c) p
      exact ⟨t, hU t,
        (minusPhiOf_short hirr ψL ψS (minusShort_single hk') _ hz).trans (hΘU t).symm⟩
    · obtain ⟨z, hz⟩ := z
      obtain ⟨p, rfl⟩ := exists_minusXS_eq hirr (minusShort_neg_single hk') hz
      obtain ⟨t, rfl⟩ := exists_starCoord_eq (b := b) (c := c) p
      exact ⟨t, hLo t,
        (minusPhiOf_short hirr ψL ψS (minusShort_neg_single hk') _ hz).trans (hΘL t).symm⟩

theorem hgen : Subgroup.closure (⋃ k : Fin (minusDatum n hirr).rank,
    Set.range (minusPhiOf hirr ψL ψS (Pi.single k 1)) ∪
      Set.range (minusPhiOf hirr ψL ψS (-Pi.single k 1))) = ⊤ := by
  have e : ∀ k : Fin (n - 1),
      Set.range (minusPhiOf hirr ψL ψS (Pi.single k 1)) ∪
        Set.range (minusPhiOf hirr ψL ψS (-Pi.single k 1)) =
      if k.val + 2 < n then Set.range (ψL (Pi.single k 1)) ∪ Set.range (ψL (-Pi.single k 1))
      else Set.range (ψS (Pi.single k 1)) ∪ Set.range (ψS (-Pi.single k 1)) := by
    intro k
    split_ifs with hk
    · exact congrArg₂ (· ∪ ·) (range_minusPhiOf_long hirr ψL ψS (minusLong_single hk))
        (range_minusPhiOf_long hirr ψL ψS (minusLong_neg_single hk))
    · have hk' : k.val + 2 = n := by have := k.isLt; omega
      exact congrArg₂ (· ∪ ·) (range_minusPhiOf_short hirr ψL ψS (minusShort_single hk'))
        (range_minusPhiOf_short hirr ψL ψS (minusShort_neg_single hk'))
  have hg := h.gen
  rw [← Set.iUnion_congr e] at hg
  exact hg

theorem hnt : ∃ k : Fin (minusDatum n hirr).rank, ∃ x,
    minusPhiOf hirr ψL ψS (Pi.single k 1) x ≠ 1 := by
  obtain ⟨k, hk, y, hy⟩ := h.nt
  exact ⟨k, ⟨minusXL n b c (Pi.single k 1) y, minusXL_mem hirr (minusLong_single hk) y⟩,
    fun h1 => hy ((minusPhiOf_long hirr ψL ψS (minusLong_single hk) y _).symm.trans h1)⟩

theorem pos_A2 [CharP F 2] [Finite F] {i : Fin (n - 1)} (hi : i.val + 3 < n) :
    ExtendsToHom (minusDatum n hirr).rootGroup
      (pairRoots (minusDatum n hirr) i (⟨i.val + 1, by omega⟩ : Fin (n - 1)) ∩
        (ΦMinus n hirr).pos)
      (minusPhiOf hirr ψL ψS) := by
  have := Fintype.ofFinite F
  have hne : i ≠ (⟨i.val + 1, by omega⟩ : Fin (n - 1)) := Fin.ne_of_val_ne (by simp)
  have hL : ∀ a, MinusLong n (minusA2r i hi a) := by
    intro a
    fin_cases a
    · exact minusLong_single (by omega)
    · exact minusLong_A2sum hi
    · exact minusLong_single (k := ⟨i.val + 1, by omega⟩) (by simp; omega)
  have hP : ∀ a, minusA2r i hi a ∈
      pairRoots (minusDatum n hirr) i (⟨i.val + 1, by omega⟩ : Fin (n - 1)) := fun a =>
    ⟨(hL a).mem_roots, fun (l : Fin (n - 1)) hli hlj => by
      have hli' : ¬ l = i := hli
      have hlj' : ¬ l = ⟨i.val + 1, by omega⟩ := hlj
      fin_cases a <;> simp [minusA2r, hli', hlj']⟩
  have hrinj : Function.Injective (minusA2r i hi) := by
    intro a a' haa
    have h1 := congrFun haa i
    have h2 := congrFun haa ⟨i.val + 1, by omega⟩
    fin_cases a <;> fin_cases a' <;> simp [minusA2r, hne, Ne.symm hne] at h1 h2 ⊢
  refine extendsToHom_of_rels (F := fun _ => F) (cm := a2Cm (K := F)) (ht := a2Ht)
    (fun α s β t => a2Cm_mem_above α s β t) (minusA2r i hi)
    (fun a c' => minusXL n b c (minusA2r i hi a) c') (fun a c' => minusXL_mem hirr (hL a) c') ?_
    [0, 2, 1] ?_ (fun γ hγ => ?_) (fun a y hy => exists_minusXL_eq hirr (hL a) hy)
    (fun g => ψL (minusA2r i hi g.1) g.2) ?_
    (fun a c' => minusPhiOf_long hirr ψL ψS (hL a) c' _)
  · exact rels_a2Cm_of (fun a c' d => minusXL_add _ c' d) (fun s t => minus_comm_A2 hi s t)
      (fun s t => minus_commute_A2_left hi s t) (fun s t => minus_commute_A2_right hi s t)
  · exact injective_prod_of_prodInjectiveFor (F := fun _ => F)
      (X := (minusDatum n hirr).rootGroup) (minusA2r i hi) hrinj _
      (fun a c' => minusXL_mem hirr (hL a) c') (fun a => minusXL_injective (hL a)) _
      (by decide) (minus_prod_A2 hirr hi)
  · obtain ⟨hγ, hpos⟩ := hγ
    rcases minus_pos_roots_A2 hi rfl hγ.1 hγ.2 hpos.2 with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  · exact rels_a2Cm_of (fun a c' d => h.addL _ _ _ (hP a) (hL a) c' d) (h.commA2 i hi)
      (h.commuteA2l i hi) (h.commuteA2r i hi)

theorem pos_B2 [CharP F 2] [Finite F] {i : Fin (n - 1)} (hi : i.val + 3 = n) :
    ExtendsToHom (minusDatum n hirr).rootGroup
      (pairRoots (minusDatum n hirr) i (⟨i.val + 1, by omega⟩ : Fin (n - 1)) ∩
        (ΦMinus n hirr).pos)
      (minusPhiOf hirr ψL ψS) := by
  have := Fintype.ofFinite F
  have hfin : ∀ k, Fintype (tb2Par F k) := fun k =>
    match k with
    | 0 => (inferInstance : Fintype (Fin 2 → F))
    | 1 => (inferInstance : Fintype (Fin 2 → F))
    | 2 => (inferInstance : Fintype F)
    | 3 => (inferInstance : Fintype F)
  have hne : i ≠ (⟨i.val + 1, by omega⟩ : Fin (n - 1)) := Fin.ne_of_val_ne (by simp)
  have hS0 : MinusShort n (minusB2r i hi 0) :=
    minusShort_single (k := ⟨i.val + 1, by omega⟩) (by simp; omega)
  have hS1 : MinusShort n (minusB2r i hi 1) := minusShort_B2sum hi
  have hL2 : MinusLong n (minusB2r i hi 2) := minusLong_B2long hi
  have hL3 : MinusLong n (minusB2r i hi 3) := minusLong_single (by omega)
  have hmem : ∀ k (c' : tb2Par F k),
      minusB2x hirr i hi k c' ∈ (minusDatum n hirr).rootGroup (minusB2r i hi k) := fun k c' =>
    match k, c' with
    | 0, p => minusXS_mem hirr hS0 p
    | 1, p => minusXS_mem hirr hS1 p
    | 2, x => minusXL_mem hirr hL2 x
    | 3, x => minusXL_mem hirr hL3 x
  have hroots : ∀ k, minusB2r i hi k ∈ RootSystem.roots (isFiniteType_cartanB (n - 1)) ∅ := by
    intro k
    fin_cases k
    exacts [hS0.mem_roots, hS1.mem_roots, hL2.mem_roots, hL3.mem_roots]
  have hP : ∀ k, minusB2r i hi k ∈
      pairRoots (minusDatum n hirr) i (⟨i.val + 1, by omega⟩ : Fin (n - 1)) := fun k =>
    ⟨hroots k, fun (l : Fin (n - 1)) hli hlj => by
      have hli' : ¬ l = i := hli
      have hlj' : ¬ l = ⟨i.val + 1, by omega⟩ := hlj
      fin_cases k <;> simp [minusB2r, hli', hlj']⟩
  have hrinj : Function.Injective (minusB2r i hi) := by
    intro a a' haa
    have h1 := congrFun haa i
    have h2 := congrFun haa ⟨i.val + 1, by omega⟩
    fin_cases a <;> fin_cases a' <;> simp [minusB2r, hne, Ne.symm hne] at h1 h2 ⊢
  refine extendsToHom_of_rels (F := tb2Par F) (cm := tb2Cm (planeNorm b c) (polarPlane b c))
    (ht := b2Ht) (fun α s β t => tb2Cm_mem_above _ _ α s β t) (minusB2r i hi)
    (minusB2x hirr i hi) hmem ?_ [0, 3, 1, 2] ?_ (fun γ hγ => ?_) (fun k y hy => ?_)
    (minusB2psi ψL ψS i hi) ?_ (fun k c' => ?_)
  · exact rels_tb2Cm_of (φ := fun g => minusB2x hirr i hi g.1 g.2) _ _
      (tb2_add_of (φ := fun g => minusB2x hirr i hi g.1 g.2) (fun p q => minusXS_add hirr _ p q)
        (fun p q => minusXS_add hirr _ p q) (fun x y => minusXL_add _ x y)
        (fun x y => minusXL_add _ x y))
      (fun p q => minus_comm_B2' hirr hi p q) (fun p s => minus_comm_B2 hirr hi p s)
      (fun p s => minus_commute_B2_b_2ab hirr hi p s)
      (fun p s => minus_commute_B2_ab_2ab hirr hi p s)
      (fun p s => minus_commute_B2_ab_a hirr hi p s) (fun s t => minus_commute_B2_2ab_a hi s t)
  · refine injective_prod_of_prodInjectiveFor (F := tb2Par F)
      (X := (minusDatum n hirr).rootGroup) (minusB2r i hi) hrinj (minusB2x hirr i hi) hmem
      (fun k => ?_) _ (by decide) (minus_prod_B2 hirr hi)
    match k with
    | 0 => exact minusXS_injective hirr hS0
    | 1 => exact minusXS_injective hirr hS1
    | 2 => exact minusXL_injective (F := F) hL2
    | 3 => exact minusXL_injective (F := F) hL3
  · obtain ⟨hγ, hpos⟩ := hγ
    rcases minus_pos_roots_B2 rfl hγ.1 hγ.2 hpos.2 with rfl | rfl | rfl | rfl
    · exact ⟨3, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  · match k, y, hy with
    | 0, y, hy => exact exists_minusXS_eq hirr hS0 hy
    | 1, y, hy => exact exists_minusXS_eq hirr hS1 hy
    | 2, y, hy => exact exists_minusXL_eq hirr hL2 hy
    | 3, y, hy => exact exists_minusXL_eq hirr hL3 hy
  · exact rels_tb2Cm_of (φ := minusB2psi ψL ψS i hi) _ _
      (tb2_add_of (φ := minusB2psi ψL ψS i hi) (h.addS _ _ _ (hP 0) hS0)
        (h.addS _ _ _ (hP 1) hS1) (h.addL _ _ _ (hP 2) hL2) (h.addL _ _ _ (hP 3) hL3))
      (h.commB2' i hi) (h.commB2 i hi) (h.commuteB2_b_2ab i hi) (h.commuteB2_ab_2ab i hi)
      (h.commuteB2_ab_a i hi) (h.commuteB2_2ab_a i hi)
  · match k, c' with
    | 0, p => exact minusPhiOf_short hirr ψL ψS hS0 p _
    | 1, p => exact minusPhiOf_short hirr ψL ψS hS1 p _
    | 2, x => exact minusPhiOf_long hirr ψL ψS hL2 x _
    | 3, x => exact minusPhiOf_long hirr ψL ψS hL3 x _

theorem pos_A1A1_long [CharP F 2] [Finite F] {i j : Fin (n - 1)} (hij : i.val + 2 ≤ j.val)
    (hj : j.val + 2 < n) :
    ExtendsToHom (minusDatum n hirr).rootGroup
      (pairRoots (minusDatum n hirr) i j ∩ (ΦMinus n hirr).pos) (minusPhiOf hirr ψL ψS) := by
  have := Fintype.ofFinite F
  have hne : i ≠ j := Fin.ne_of_val_ne (by omega)
  have hL : ∀ a, MinusLong n (minusA1r i j a) := by
    intro a
    fin_cases a
    · exact minusLong_single (by omega)
    · exact minusLong_single hj
  have hP : ∀ a, minusA1r i j a ∈ pairRoots (minusDatum n hirr) i j := fun a =>
    ⟨(hL a).mem_roots, fun (l : Fin (n - 1)) hli hlj => by
      have hli' : ¬ l = i := hli
      have hlj' : ¬ l = j := hlj
      fin_cases a <;> simp [minusA1r, hli', hlj']⟩
  have hrinj : Function.Injective (minusA1r i j) := by
    intro a a' haa
    have h1 := congrFun haa i
    fin_cases a <;> fin_cases a' <;> simp [minusA1r, hne] at h1 ⊢
  refine extendsToHom_of_rels (F := fun _ => F) (cm := a1a1Cm (K := F)) (ht := a1a1Ht)
    (fun α s β t => a1a1Cm_mem_above α s β t) (minusA1r i j)
    (fun a c' => minusXL n b c (minusA1r i j a) c') (fun a c' => minusXL_mem hirr (hL a) c') ?_
    [0, 1] ?_ (fun γ hγ => ?_) (fun a y hy => exists_minusXL_eq hirr (hL a) hy)
    (fun g => ψL (minusA1r i j g.1) g.2) ?_
    (fun a c' => minusPhiOf_long hirr ψL ψS (hL a) c' _)
  · exact rels_a1a1Cm_of (fun a c' d => minusXL_add _ c' d)
      (fun s t => minus_commute_A1A1_long hij hj s t)
  · exact injective_prod_of_prodInjectiveFor (F := fun _ => F)
      (X := (minusDatum n hirr).rootGroup) (minusA1r i j) hrinj _
      (fun a c' => minusXL_mem hirr (hL a) c') (fun a => minusXL_injective (hL a)) _
      (by decide) (minus_prod_A1A1 hirr hij (hL 0) (Or.inl (hL 1)))
  · obtain ⟨hγ, hpos⟩ := hγ
    rcases minus_pos_roots_A1A1 hij hγ.1 hγ.2 hpos.2 with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · exact rels_a1a1Cm_of (fun a c' d => h.addL _ _ _ (hP a) (hL a) c' d)
      (h.commuteA1A1L i j hij hj)

theorem pos_A1A1_short [CharP F 2] [Finite F] {i k : Fin (n - 1)} (hik : i.val + 2 ≤ k.val)
    (hk : k.val + 2 = n) :
    ExtendsToHom (minusDatum n hirr).rootGroup
      (pairRoots (minusDatum n hirr) i k ∩ (ΦMinus n hirr).pos) (minusPhiOf hirr ψL ψS) := by
  have := Fintype.ofFinite F
  have hfin : ∀ l, Fintype (ma1Par F l) := fun l =>
    match l with
    | 0 => (inferInstance : Fintype F)
    | 1 => (inferInstance : Fintype (Fin 2 → F))
  have hne : i ≠ k := Fin.ne_of_val_ne (by omega)
  have hL0 : MinusLong n (minusA1r i k 0) := minusLong_single (by omega)
  have hS1 : MinusShort n (minusA1r i k 1) := minusShort_single hk
  have hmem : ∀ l (c' : ma1Par F l),
      minusA1x hirr i k l c' ∈ (minusDatum n hirr).rootGroup (minusA1r i k l) := fun l c' =>
    match l, c' with
    | 0, x => minusXL_mem hirr hL0 x
    | 1, p => minusXS_mem hirr hS1 p
  have hP0 : minusA1r i k 0 ∈ pairRoots (minusDatum n hirr) i k :=
    ⟨hL0.mem_roots, fun (l : Fin (n - 1)) hli hlk => by
      have hli' : ¬ l = i := hli
      simp [minusA1r, Pi.single_apply, hli']⟩
  have hP1 : minusA1r i k 1 ∈ pairRoots (minusDatum n hirr) i k :=
    ⟨hS1.mem_roots, fun (l : Fin (n - 1)) hli hlk => by
      have hlk' : ¬ l = k := hlk
      simp [minusA1r, Pi.single_apply, hlk']⟩
  have hrinj : Function.Injective (minusA1r i k) := by
    intro a a' haa
    have h1 := congrFun haa i
    fin_cases a <;> fin_cases a' <;> simp [minusA1r, hne] at h1 ⊢
  refine extendsToHom_of_rels (F := ma1Par F) (cm := ma1Cm F) (ht := a1a1Ht)
    (fun α s β t => ma1Cm_mem_above α s β t) (minusA1r i k) (minusA1x hirr i k) hmem ?_ [0, 1]
    ?_ (fun γ hγ => ?_) (fun l y hy => ?_) (minusA1psi ψL ψS i k) ?_ (fun l c' => ?_)
  · exact rels_ma1Cm_of (φ := fun g => minusA1x hirr i k g.1 g.2) (fun x y => minusXL_add _ x y)
      (fun p q => minusXS_add hirr _ p q) (fun s p => minus_commute_A1A1_short hirr hik hk s p)
  · refine injective_prod_of_prodInjectiveFor (F := ma1Par F)
      (X := (minusDatum n hirr).rootGroup) (minusA1r i k) hrinj (minusA1x hirr i k) hmem
      (fun l => ?_) _ (by decide) (minus_prod_A1A1 hirr hik hL0 (Or.inr hS1))
    match l with
    | 0 => exact minusXL_injective (F := F) hL0
    | 1 => exact minusXS_injective hirr hS1
  · obtain ⟨hγ, hpos⟩ := hγ
    rcases minus_pos_roots_A1A1 hik hγ.1 hγ.2 hpos.2 with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · match l, y, hy with
    | 0, y, hy => exact exists_minusXL_eq hirr hL0 hy
    | 1, y, hy => exact exists_minusXS_eq hirr hS1 hy
  · exact rels_ma1Cm_of (φ := minusA1psi ψL ψS i k) (h.addL _ _ _ hP0 hL0)
      (h.addS _ _ _ hP1 hS1) (h.commuteA1A1S i k hik hk)
  · match l, c' with
    | 0, x => exact minusPhiOf_long hirr ψL ψS hL0 x _
    | 1, p => exact minusPhiOf_short hirr ψL ψS hS1 p _

theorem cone_lt [CharP F 2] [Finite F] {i j : Fin (n - 1)} (hij : i.val < j.val) :
    ∀ α ∈ pairRoots (minusDatum n hirr) i j, ∀ β ∈ pairRoots (minusDatum n hirr) i j,
      ¬ Universal.IsNegMultiple α β →
        ExtendsToHom (minusDatum n hirr).rootGroup
          ((minusDatum n hirr).cone α β ∩ pairRoots (minusDatum n hirr) i j)
          (minusPhiOf hirr ψL ψS) := by
  obtain ⟨ñ, hñ⟩ := h.weyl i j hij
  have hpos : ExtendsToHom (minusDatum n hirr).rootGroup
      (pairRoots (minusDatum n hirr) i j ∩ (ΦMinus n hirr).pos) (minusPhiOf hirr ψL ψS) := by
    have hjn := j.isLt
    by_cases hadj : j.val = i.val + 1
    · have e : j = (⟨i.val + 1, by omega⟩ : Fin (n - 1)) := Fin.ext hadj
      rw [e]
      by_cases hN : i.val + 3 < n
      · exact h.pos_A2 hN
      · exact h.pos_B2 (by omega)
    · by_cases hj : j.val + 2 < n
      · exact h.pos_A1A1_long (by omega) hj
      · exact h.pos_A1A1_short (by omega) (by omega)
  exact extendsToHom_cone_pairRoots (D := minusDatum n hirr) (i := i) (j := j) (minusWeyl n hirr)
    (fun k _ γ hγ x hx => minusWeyl_conj_mem hirr k hγ.1 hx) ñ (compat hñ) hpos
    (fun k _ => h.hrank k)

theorem cone_self [CharP F 2] [Finite F] (k : Fin (n - 1)) :
    ∀ α ∈ pairRoots (minusDatum n hirr) k k, ∀ β ∈ pairRoots (minusDatum n hirr) k k,
      ¬ Universal.IsNegMultiple α β →
        ExtendsToHom (minusDatum n hirr).rootGroup
          ((minusDatum n hirr).cone α β ∩ pairRoots (minusDatum n hirr) k k)
          (minusPhiOf hirr ψL ψS) := by
  intro α _ β _ _
  refine (h.hrank k).mono fun γ hγ => ?_
  rcases minus_roots_self hγ.2.1 (fun l hl => hγ.2.2 l hl hl) with e | e
  · exact Or.inl e
  · exact Or.inr e

end IsMinusFrame

variable {hirr} in
theorem IsMinusFrame.isCTFrame [CharP F 2] [Finite F] [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)]
    {G : Type} [Group G] {ψL : (Fin (n - 1) → ℤ) → F → G}
    {ψS : (Fin (n - 1) → ℤ) → (Fin 2 → F) → G} (h : IsMinusFrame n hirr ψL ψS) :
    ARS.IsCTFrame (minusDatum n hirr) G (minusPhiOf hirr ψL ψS) := by
  refine ⟨fun i j => ?_, h.hrank, h.hgen, h.hnt⟩
  rcases lt_trichotomy i.val j.val with hlt | heq | hgt
  · exact h.cone_lt hlt
  · have e : i = j := Fin.ext heq
    subst e
    exact h.cone_self i
  · rw [pairRoots_comm_minusN hirr]
    exact h.cone_lt hgt

end Frame

end CFSG.Timmesfeld.RankTwo
