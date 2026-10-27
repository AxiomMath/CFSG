module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallModelsBDAuxA

public section

namespace CFSG.StandardType.HdRo7SU.Small

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

lemma hdRo7SmBDAux_smDual_apply {m : ℕ} (w v : SMV m) : smDual w v = smDot w v := by
  simp [smDual, smDot, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul]

lemma hdRo7SmBDAux_smDual_add {m : ℕ} (w w' v : SMV m) :
    smDual (w + w') v = smDual w v + smDual w' v := by
  rw [hdRo7SmBDAux_smDual_apply, hdRo7SmBDAux_smDual_apply, hdRo7SmBDAux_smDual_apply]
  simp only [smDot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma hdRo7SmBDAux_smDual_smul {m : ℕ} (c : ZMod 3) (w v : SMV m) :
    smDual (c • w) v = c * smDual w v := by
  simp only [hdRo7SmBDAux_smDual_apply, smDot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma hdRo7SmBDAux_smDual_basis {m : ℕ}
    (b : Module.Basis (Fin m) (ZMod 3) (SMV m)) (hb : ∀ k, b k = Pi.single k (1 : ZMod 3))
    (k i : Fin m) : smDual (b k) (b i) = (if i = k then 1 else 0) := by
  rw [hdRo7SmBDAux_smDual_apply, hb k, hb i, smDot, Finset.sum_eq_single i]
  · by_cases h : i = k <;> simp [h]
  · intro j _ hj
    simp [Pi.single_apply, hj]
  · intro hi; exact absurd (Finset.mem_univ i) hi

lemma hdRo7SmBDAux_smDual_smul_basis {m : ℕ}
    (b : Module.Basis (Fin m) (ZMod 3) (SMV m)) (hb : ∀ k, b k = Pi.single k (1 : ZMod 3))
    (γ : ZMod 3) (k i : Fin m) :
    smDual (γ • b k) (b i) = γ * (if i = k then 1 else 0) := by
  rw [hdRo7SmBDAux_smDual_smul, hdRo7SmBDAux_smDual_basis b hb]

lemma hdRo7SmBDAux_reflB_fullPred {m : ℕ}
    (b : Module.Basis (Fin m) (ZMod 3) (SMV m)) (hb : ∀ k, b k = Pi.single k (1 : ZMod 3))
    {k : Fin m} {β γ : ZMod 3} (hβγ : γ * β = 2)
    {r : SMGL m} (hr : SMRefl r (β • b k) (smDual (γ • b k))) :
    hdRo7SmBDAux_fullPred b r := by
  obtain ⟨hφ, hform⟩ := hr
  refine ⟨1, fun i => if i = k then -1 else 1, ?_, ?_⟩
  · intro i; by_cases h : i = k <;> simp [h]
  · intro i
    rw [hform, hdRo7SmBDAux_smDual_smul_basis b hb]
    by_cases h : i = k
    · subst h
      simp only [if_true, Equiv.Perm.one_apply, mul_one]
      rw [smul_smul, hβγ]
      module
    · simp [h]

lemma hdRo7SmBDAux_reflD_fullPred {m : ℕ}
    (b : Module.Basis (Fin m) (ZMod 3) (SMV m)) (hb : ∀ k, b k = Pi.single k (1 : ZMod 3))
    {j1 j2 : Fin m} (hne : j1 ≠ j2) {β γ : ZMod 3} (hβγ : γ * β = 1)
    {r : SMGL m} (hr : SMRefl r (β • (b j1 + b j2)) (smDual (γ • (b j1 + b j2)))) :
    hdRo7SmBDAux_fullPred b r := by
  obtain ⟨hφ, hform⟩ := hr
  refine ⟨Equiv.swap j1 j2,
    fun i => if i = j1 ∨ i = j2 then -1 else 1, ?_, ?_⟩
  · intro i; by_cases h : i = j1 ∨ i = j2 <;> simp [h]
  · intro i
    rw [hform, hdRo7SmBDAux_smDual_smul, hdRo7SmBDAux_smDual_add,
      hdRo7SmBDAux_smDual_basis b hb, hdRo7SmBDAux_smDual_basis b hb]
    by_cases hi1 : i = j1
    · subst hi1
      simp only [true_or, if_true, Equiv.swap_apply_left]
      rw [if_neg hne, add_zero, mul_one, smul_smul, hβγ]
      module
    · by_cases hi2 : i = j2
      · subst hi2
        simp only [or_true, if_true, Equiv.swap_apply_right]
        rw [if_neg (Ne.symm hne), zero_add, mul_one, smul_smul, hβγ]
        module
      · simp [hi1, hi2, Equiv.swap_apply_of_ne_of_ne hi1 hi2]

lemma hdRo7SmBDAux_reflD_prod {m : ℕ}
    (b : Module.Basis (Fin m) (ZMod 3) (SMV m)) (hb : ∀ k, b k = Pi.single k (1 : ZMod 3))
    {j1 j2 : Fin m} (hne : j1 ≠ j2) {β γ : ZMod 3} (hβγ : γ * β = 1)
    {r : SMGL m} (hr : SMRefl r (β • (b j1 + b j2)) (smDual (γ • (b j1 + b j2)))) :
    r * ZS.permMap 3 b (Equiv.swap j1 j2) =
      hdRo7SmBDAux_sgn b j1 * hdRo7SmBDAux_sgn b j2 := by
  obtain ⟨hφ, hform⟩ := hr
  apply hdRo7SmBDAux_ext b
  intro k
  rw [LinearEquiv.mul_apply, hdRo7SmBDAux_permMap_apply, hform, hdRo7SmBDAux_smDual_smul,
    hdRo7SmBDAux_smDual_add, hdRo7SmBDAux_smDual_basis b hb, hdRo7SmBDAux_smDual_basis b hb,
    LinearEquiv.mul_apply, hdRo7SmBDAux_sgn_apply, map_smul, hdRo7SmBDAux_sgn_apply]
  by_cases hk1 : k = j1
  · rw [hk1]
    simp only [Equiv.swap_apply_left, if_neg (Ne.symm hne), if_pos rfl, zero_add, mul_one]
    simp only [smul_smul, if_true, mul_one, hβγ, if_neg hne, if_neg (Ne.symm hne)]
    module
  · by_cases hk2 : k = j2
    · rw [hk2]
      simp only [Equiv.swap_apply_right, if_neg hne, if_pos rfl, add_zero, mul_one]
      simp only [smul_smul, if_true, mul_one, hβγ, if_neg hne, if_neg (Ne.symm hne)]
      module
    · simp [hk1, hk2, Equiv.swap_apply_of_ne_of_ne hk1 hk2]

@[expose]
def hdRo7SmBDAux_evenPred {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) (SMV m))
    (a : SMGL m) : Prop :=
  ∃ (σ : Equiv.Perm (Fin m)) (c : Fin m → ZMod 3),
    (∀ i, c i = 1 ∨ c i = -1) ∧ (∏ i, c i = 1) ∧ ∀ i, a (b i) = c i • b (σ i)

lemma hdRo7SmBDAux_even_card_of_prod {m : ℕ} (c : Fin m → ZMod 3)
    (hc : ∀ i, c i = 1 ∨ c i = -1) (hprod : ∏ i, c i = 1) :
    Even (Finset.univ.filter (fun i => c i = -1)).card := by
  let s := Finset.univ.filter (fun i => c i = -1)
  have h1 : (∏ i, c i) = (-1 : ZMod 3) ^ s.card := by
    have hc' : (∏ i, c i) = ∏ i, (if c i = -1 then (-1 : ZMod 3) else 1) := by
      apply Finset.prod_congr rfl
      intro i _
      rcases hc i with h | h <;> simp [h]
    rw [hc']
    rw [← Finset.prod_filter (s := Finset.univ) (f := fun _ => (-1 : ZMod 3))
      (p := fun i => c i = -1), Finset.prod_const]
  have h2 : (-1 : ZMod 3) ^ s.card = 1 := by rw [← h1, hprod]
  rcases Nat.even_or_odd s.card with he | ho
  · exact he
  · exfalso
    rw [Odd.neg_one_pow ho] at h2
    exact (by decide : (-1 : ZMod 3) ≠ 1) h2

lemma hdRo7SmBDAux_list_prod_signPair_apply {m : ℕ}
    (b : Module.Basis (Fin m) (ZMod 3) (SMV m)) (hb : ∀ k, b k = Pi.single k (1 : ZMod 3))
    (l : List (Fin m)) (i0 k : Fin m) :
    (l.map (fun j => hdRo7SmBDAux_sgn b i0 * hdRo7SmBDAux_sgn b j)).prod (b k) =
      (l.map (fun j => (if k = i0 then -1 else 1 : ZMod 3) *
        (if k = j then -1 else 1))).prod • b k := by
  induction l with
  | nil => simp
  | cons j l ih =>
    simp only [List.map_cons, List.prod_cons, LinearEquiv.mul_apply, ih, map_smul,
      hdRo7SmBDAux_sgn_apply, smul_smul]
    congr 1
    ring

lemma hdRo7SmBDAux_list_prod_signPair_scalar_aux {m : ℕ} (l : List (Fin m)) (i0 k : Fin m) :
    (l.map (fun j => (if k = i0 then -1 else 1 : ZMod 3) * (if k = j then -1 else 1))).prod =
      (if k = i0 then -1 else 1 : ZMod 3) ^ l.length *
        (l.map (fun j => (if k = j then -1 else 1 : ZMod 3))).prod := by
  induction l with
  | nil => simp
  | cons j l ih =>
    simp only [List.map_cons, List.prod_cons, ih, List.length_cons, pow_succ]
    ring

lemma hdRo7SmBDAux_list_prod_signPair_scalar {m : ℕ} (l : List (Fin m)) (i0 k : Fin m)
    (hnd : l.Nodup) (hi0 : i0 ∉ l) :
    (l.map (fun j => (if k = i0 then -1 else 1 : ZMod 3) * (if k = j then -1 else 1))).prod =
      (if k = i0 then (-1 : ZMod 3) ^ l.length else (if k ∈ l then -1 else 1)) := by
  rw [hdRo7SmBDAux_list_prod_signPair_scalar_aux, hdRo7SmBDAux_list_prod_sign l hnd k]
  by_cases hk : k = i0
  · rw [hk]; simp [hi0]
  · simp [hk]

@[expose]
noncomputable def hdRo7SmBDAux_evenSubgroup {m : ℕ}
    (b : Module.Basis (Fin m) (ZMod 3) (SMV m)) : Subgroup (SMGL m) where
  carrier := {a | hdRo7SmBDAux_evenPred b a}
  one_mem' := by
    refine ⟨1, fun _ => 1, ?_, ?_, ?_⟩
    · intro i; left; rfl
    · simp
    · intro i; simp
  mul_mem' := by
    rintro a a' ⟨σ, c, hc, hcprod, ha⟩ ⟨σ', c', hc', hc'prod, ha'⟩
    refine ⟨σ * σ', fun i => c' i * c (σ' i), ?_, ?_, ?_⟩
    · intro i
      change c' i * c (σ' i) = 1 ∨ c' i * c (σ' i) = -1
      rcases hc' i with h | h <;> rcases hc (σ' i) with h2 | h2
      · left; rw [h, h2]; ring
      · right; rw [h, h2]; ring
      · right; rw [h, h2]; ring
      · left; rw [h, h2]; ring
    · rw [Finset.prod_mul_distrib, hc'prod]
      have hre : (∏ i, c (σ' i)) = ∏ i, c i := by
        refine Finset.prod_bij (fun i _ => σ' i) ?_ ?_ ?_ ?_
        · intro i _; exact Finset.mem_univ _
        · intro i _ j _ hij; exact σ'.injective hij
        · intro b _; exact ⟨σ'.symm b, Finset.mem_univ _, by simp⟩
        · intro i _; rfl
      rw [hre, hcprod, mul_one]
    · intro i
      rw [LinearEquiv.mul_apply, ha', map_smul, ha, Equiv.Perm.mul_apply, smul_smul]
  inv_mem' := by
    rintro a ⟨σ, c, hc, hcprod, ha⟩
    refine ⟨σ.symm, fun j => c (σ.symm j), ?_, ?_, ?_⟩
    · intro j; exact hc (σ.symm j)
    · have hre : (∏ j, c (σ.symm j)) = ∏ j, c j := by
        refine Finset.prod_bij (fun j _ => σ.symm j) ?_ ?_ ?_ ?_
        · intro j _; exact Finset.mem_univ _
        · intro i _ j _ hij; exact σ.symm.injective hij
        · intro b _; exact ⟨σ b, Finset.mem_univ _, by simp⟩
        · intro j _; rfl
      rw [hre, hcprod]
    · intro j
      change a.symm (b j) = c (σ.symm j) • b (σ.symm j)
      rw [LinearEquiv.symm_apply_eq, map_smul, ha, Equiv.apply_symm_apply, smul_smul]
      have hcc : c (σ.symm j) * c (σ.symm j) = 1 := by
        rcases hc (σ.symm j) with h | h <;> rw [h] <;> ring
      rw [hcc, one_smul]

lemma hdRo7SmBDAux_list_prod_signPair_mem {m : ℕ}
    (b : Module.Basis (Fin m) (ZMod 3) (SMV m)) (G : Subgroup (SMGL m))
    (l : List (Fin m)) (i0 : Fin m) (hi0 : i0 ∉ l)
    (hpair : ∀ j, j ≠ i0 → hdRo7SmBDAux_sgn b i0 * hdRo7SmBDAux_sgn b j ∈ G) :
    (l.map (fun j => hdRo7SmBDAux_sgn b i0 * hdRo7SmBDAux_sgn b j)).prod ∈ G := by
  induction l with
  | nil => simp
  | cons j l ih =>
    rw [List.map_cons, List.prod_cons]
    have hji : j ≠ i0 := fun h => hi0 (h ▸ List.mem_cons.mpr (Or.inl rfl))
    exact Subgroup.mul_mem _ (hpair j hji) (ih (fun h => hi0 (List.mem_cons_of_mem j h)))

lemma hdRo7SmBDAux_evenPred_mem {m : ℕ}
    (b : Module.Basis (Fin m) (ZMod 3) (SMV m)) (hb : ∀ k, b k = Pi.single k (1 : ZMod 3))
    (G : Subgroup (SMGL m))
    (hperm : ∀ σ, ZS.permMap 3 b σ ∈ G)
    (i0 : Fin m) (hpair : ∀ j, j ≠ i0 → hdRo7SmBDAux_sgn b i0 * hdRo7SmBDAux_sgn b j ∈ G)
    {a : SMGL m} (ha : hdRo7SmBDAux_evenPred b a) : a ∈ G := by
  obtain ⟨σ, c, hc, hcprod, ha'⟩ := ha
  let s := Finset.univ.filter (fun k => c k = -1)
  have heven : Even s.card := hdRo7SmBDAux_even_card_of_prod c hc hcprod
  have hmem : ∀ i, i ∈ s ↔ c i = -1 := by
    intro i; simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
  let l := (s.erase i0).toList
  have hnd : l.Nodup := Finset.nodup_toList _
  have hi0l : i0 ∉ l := by
    rw [show l = (s.erase i0).toList from rfl, Finset.mem_toList]
    exact Finset.notMem_erase i0 s
  have hmeml : ∀ k, k ∈ l ↔ c k = -1 ∧ k ≠ i0 := by
    intro k
    rw [show l = (s.erase i0).toList from rfl, Finset.mem_toList, Finset.mem_erase, hmem k]
    constructor
    · exact fun h => ⟨h.2, h.1⟩
    · exact fun h => ⟨h.2, h.1⟩
  have hDmem : (l.map (fun j => hdRo7SmBDAux_sgn b i0 * hdRo7SmBDAux_sgn b j)).prod ∈ G :=
    hdRo7SmBDAux_list_prod_signPair_mem b G l i0 hi0l hpair
  have happly : ∀ k, (l.map (fun j => hdRo7SmBDAux_sgn b i0 * hdRo7SmBDAux_sgn b j)).prod (b k) =
      c k • b k := by
    intro k
    rw [hdRo7SmBDAux_list_prod_signPair_apply b hb l i0 k,
      hdRo7SmBDAux_list_prod_signPair_scalar l i0 k hnd hi0l]
    by_cases hk : k = i0
    · rw [hk]
      rw [if_pos rfl]
      congr 1
      show (-1 : ZMod 3) ^ l.length = c i0
      rw [show l.length = (s.erase i0).card from Finset.length_toList _]
      by_cases his : i0 ∈ s
      · rw [Finset.card_erase_of_mem his]
        have hodd : Odd (s.card - 1) := by
          obtain ⟨n, hn⟩ := heven
          have hpos : 0 < s.card := Finset.card_pos.mpr ⟨i0, his⟩
          exact ⟨n - 1, by omega⟩
        rw [Odd.neg_one_pow hodd, (hmem i0).mp his]
      · rw [show (s.erase i0).card = s.card from by
            rw [Finset.erase_eq_of_notMem his], Even.neg_one_pow heven]
        rcases hc i0 with h | h
        · exact h.symm
        · exfalso; exact his ((hmem i0).mpr h)
    · rw [if_neg hk]
      congr 1
      by_cases hkl : k ∈ l
      · rw [if_pos hkl, ((hmeml k).mp hkl).1]
      · rw [if_neg hkl]
        have hck : c k = 1 := by
          rcases hc k with h | h
          · exact h
          · exfalso; exact hkl ((hmeml k).mpr ⟨h, hk⟩)
        rw [hck]
  have hdecomp : a = ZS.permMap 3 b σ *
      (l.map (fun j => hdRo7SmBDAux_sgn b i0 * hdRo7SmBDAux_sgn b j)).prod := by
    apply hdRo7SmBDAux_ext b
    intro k
    rw [LinearEquiv.mul_apply, ha' k, happly k, map_smul, hdRo7SmBDAux_permMap_apply]
  rw [hdecomp]
  exact Subgroup.mul_mem _ (hperm σ) hDmem


lemma hdRo7SmBDAux_reflD_evenPred {m : ℕ}
    (b : Module.Basis (Fin m) (ZMod 3) (SMV m)) (hb : ∀ k, b k = Pi.single k (1 : ZMod 3))
    {j1 j2 : Fin m} (hne : j1 ≠ j2) {β γ : ZMod 3} (hβγ : γ * β = 1)
    {r : SMGL m} (hr : SMRefl r (β • (b j1 + b j2)) (smDual (γ • (b j1 + b j2)))) :
    hdRo7SmBDAux_evenPred b r := by
  obtain ⟨hφ, hform⟩ := hr
  refine ⟨Equiv.swap j1 j2,
    fun i => if i = j1 ∨ i = j2 then -1 else 1, ?_, ?_, ?_⟩
  · intro i; by_cases h : i = j1 ∨ i = j2 <;> simp [h]
  · rw [← Finset.prod_filter (s := Finset.univ) (f := fun _ => (-1 : ZMod 3))
      (p := fun i => i = j1 ∨ i = j2)]
    have h : (Finset.univ.filter (fun i => i = j1 ∨ i = j2)) = {j1, j2} := by
      ext i; simp [hne]
    rw [h, Finset.prod_const, Finset.card_pair hne]
    ring
  · intro i
    rw [hform, hdRo7SmBDAux_smDual_smul, hdRo7SmBDAux_smDual_add,
      hdRo7SmBDAux_smDual_basis b hb, hdRo7SmBDAux_smDual_basis b hb]
    by_cases hi1 : i = j1
    · subst hi1
      simp only [true_or, if_true, Equiv.swap_apply_left]
      rw [if_neg hne, add_zero, mul_one, smul_smul, hβγ]
      module
    · by_cases hi2 : i = j2
      · subst hi2
        simp only [or_true, if_true, Equiv.swap_apply_right]
        rw [if_neg (Ne.symm hne), zero_add, mul_one, smul_smul, hβγ]
        module
      · simp [hi1, hi2, Equiv.swap_apply_of_ne_of_ne hi1 hi2]

end CFSG.StandardType.HdRo7SU.Small
