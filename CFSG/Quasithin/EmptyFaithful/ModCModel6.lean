module

public import CFSG.Quasithin.EmptyFaithful.ModCBase

public section

namespace CFSG.Quasithin.ModC

open Equiv Equiv.Perm CFSG.Quasithin.G6

namespace M6

set_option maxRecDepth 100000

@[expose] def a : PermMod 6 := ev 6 [0, 1, 2, 3]
@[expose] def b : PermMod 6 := ev 6 [4, 5]
@[expose] def w : PermMod 6 := ev 6 [0, 1, 4, 5]
@[expose] def x : PermMod 6 := a * b

@[expose] def gens : List (Perm (Fin 6)) := [swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 1 * swap 4 5]

@[expose] def D0 : Subgroup (Perm (Fin 6)) := Subgroup.closure {s | s ∈ gens}

def elts : List (Perm (Fin 6)) :=
  [1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, (swap 0 1 * swap 2 3) * (swap 0 2 * swap 1 3),
   swap 0 1 * swap 4 5, (swap 0 1 * swap 2 3) * (swap 0 1 * swap 4 5),
   (swap 0 2 * swap 1 3) * (swap 0 1 * swap 4 5),
   ((swap 0 1 * swap 2 3) * (swap 0 2 * swap 1 3)) * (swap 0 1 * swap 4 5)]

theorem elts_nodup : elts.Nodup := by decide +kernel

theorem elts_length : elts.length = 8 := by decide +kernel

theorem gens_inv : ∀ s ∈ gens, s⁻¹ = s := by decide +kernel

theorem elts_closed : ∀ s ∈ gens, ∀ y ∈ elts, s * y ∈ elts := by decide +kernel

theorem gens_even : ∀ s ∈ gens, sign s = 1 := by decide +kernel

theorem D0_even : ∀ s ∈ D0, sign s = 1 := by
  have h : D0 ≤ (sign : Perm (Fin 6) →* ℤˣ).ker := by
    refine Subgroup.closure_le _ |>.mpr fun s hs => ?_
    exact gens_even s hs
  intro s hs
  exact h hs

theorem mem_D0_iff (s : Perm (Fin 6)) : s ∈ D0 ↔ s ∈ elts := by
  constructor
  · intro hs
    induction hs using Subgroup.closure_induction_left with
    | one => simp [elts]
    | mul_left y hy z _ ih => exact elts_closed y hy z ih
    | inv_mul_cancel y hy z _ ih =>
      have := gens_inv y hy
      rw [this]
      exact elts_closed y hy z ih
  · intro hs
    have h1 : swap (0 : Fin 6) 1 * swap 2 3 ∈ D0 := Subgroup.subset_closure (by simp [gens])
    have h2 : swap (0 : Fin 6) 2 * swap 1 3 ∈ D0 := Subgroup.subset_closure (by simp [gens])
    have h3 : swap (0 : Fin 6) 1 * swap 4 5 ∈ D0 := Subgroup.subset_closure (by simp [gens])
    simp only [elts, List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact D0.one_mem
    · exact h1
    · exact h2
    · exact D0.mul_mem h1 h2
    · exact h3
    · exact D0.mul_mem h1 h3
    · exact D0.mul_mem h2 h3
    · exact D0.mul_mem (D0.mul_mem h1 h2) h3

theorem D0_card : Nat.card D0 = 8 := by
  have e : ↥D0 ≃ ↥(elts.toFinset) := Equiv.subtypeEquivRight (fun s => by
    rw [mem_D0_iff, List.mem_toFinset])
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup elts_nodup, elts_length]

@[expose] def CondZ (z : PermMod 6) : Prop :=
  (∑ i, Multiplicative.toAdd z i = 0) ∧ z ≠ 1 ∧ (∀ s ∈ gens, permAct 6 s z = z)

instance (z : PermMod 6) : Decidable (CondZ z) := by unfold CondZ; infer_instance

@[expose] def CondV (z v : PermMod 6) : Prop :=
  (∑ i, Multiplicative.toAdd v i = 0) ∧ v ≠ 1 ∧ v ≠ z ∧
    (∀ s ∈ gens, permAct 6 s v = v ∨ permAct 6 s v = z * v) ∧
    (wt v = wt z ∨ wt (z * v) = wt z)

instance (z v : PermMod 6) : Decidable (CondV z v) := by unfold CondV; infer_instance

@[expose] def Concl (z v : PermMod 6) : Prop := z = a ∧ (v = w ∨ v = a * w)

instance (z v : PermMod 6) : Decidable (Concl z v) := by unfold Concl; infer_instance

theorem classify : ∀ z : PermMod 6, CondZ z → ∀ v : PermMod 6, CondV z v → Concl z v := by
  decide +kernel

theorem g_analysis : ∀ g : Perm (Fin 6), permAct 6 g a = a → g ^ 3 = 1 → ∀ v ∈ [w, a * w],
    permAct 6 g v ≠ v → permAct 6 g v ≠ a * v → (join3F a v g).card = 8 ∨ x ∈ join3F a v g := by
  decide +kernel

theorem fixed_vectors : ∀ y : PermMod 6, (∑ i, Multiplicative.toAdd y i = 0) →
    (∀ s ∈ gens, permAct 6 s y = y) → y = 1 ∨ y = a ∨ y = b ∨ y = x := by
  decide +kernel

theorem ab_eq : a * x = b := by decide +kernel

theorem x_core : ∑ i, Multiplicative.toAdd x i = 0 := by decide +kernel

theorem x_ne_one : x ≠ 1 := by decide +kernel

theorem x_ne_a : x ≠ a := by decide +kernel

theorem x_fix : ∀ s ∈ gens, permAct 6 s x = x := by decide +kernel

theorem wt_count : (Finset.univ.filter fun u : PermMod 6 =>
    (∑ i, Multiplicative.toAdd u i = 0) ∧ wt u = wt x).card ≤ 7 := by decide +kernel

theorem pigeon_list : ∃ L : List (Perm (Fin 6)), L.length = 8 ∧ (∀ σ ∈ L, sign σ = 1) ∧
    (L.map (fun σ => permAct 6 σ b)).Nodup :=
  ⟨[1, swap 4 0 * swap 5 1, swap 4 0 * swap 5 2, swap 4 0 * swap 5 3, swap 4 1 * swap 5 2,
    swap 4 1 * swap 5 3, swap 4 2 * swap 5 3, swap 4 0 * swap 5 4],
    by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem exists_jj : ∃ j j' : Perm (Fin 6), sign j = 1 ∧ sign j' = 1 ∧ permAct 6 j x = x ∧
    permAct 6 j a ≠ a ∧ permAct 6 j' x = x ∧ ∀ v ∈ [w, a * w],
      permAct 6 j' v ≠ v ∧ permAct 6 j' v ≠ a * v ∧ permAct 6 j' v ≠ a :=
  ⟨swap 3 4 * swap 4 5, swap 1 2 * swap 2 4, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩


theorem modelOut (D : Subgroup (Perm (Fin 6))) (hDe : ∀ d ∈ D, sign d = 1) (hD8 : Nat.card D = 8)
    (z v : PermMod 6) (hz : ∑ i, Multiplicative.toAdd z i = 0) (hz1 : z ≠ 1)
    (hv : ∑ i, Multiplicative.toAdd v i = 0) (hv1 : v ≠ 1) (hvz : v ≠ z)
    (hDV : ∀ d ∈ D, permAct 6 d z = z ∧ (permAct 6 d v = v ∨ permAct 6 d v = z * v))
    (hwt : wt v = wt z ∨ wt (z * v) = wt z)
    (g : Perm (Fin 6)) (hg3 : g ^ 3 = 1) (hgz : permAct 6 g z = z)
    (hgv1 : permAct 6 g v ≠ v) (hgv2 : permAct 6 g v ≠ z * v)
    (hne : (join3F z v g).card ≠ 8)
    (_h5 : ¬ 5 ∣ Nat.card ↥(Subgroup.closure ((D : Set (Perm (Fin 6))) ∪ {g}))) :
    ∃ y : PermMod 6, y ∈ join3F z v g ∧ (∑ i, Multiplicative.toAdd y i = 0) ∧ y ≠ 1 ∧ y ≠ z ∧
      (∀ d ∈ D, permAct 6 d y = y) ∧
      (∀ u : PermMod 6, (∑ i, Multiplicative.toAdd u i = 0) → (∀ d ∈ D, permAct 6 d u = u) →
        u = 1 ∨ u = z ∨ u = y ∨ u = z * y) ∧
      (∃ j : Perm (Fin 6), sign j = 1 ∧ permAct 6 j y = y ∧ permAct 6 j z ≠ z) ∧
      (∃ j' : Perm (Fin 6), sign j' = 1 ∧ permAct 6 j' y = y ∧ permAct 6 j' v ≠ v ∧
        permAct 6 j' v ≠ z * v ∧ permAct 6 j' v ≠ z) ∧
      (∃ L : List (Perm (Fin 6)), L.length = 8 ∧ (∀ σ ∈ L, sign σ = 1) ∧
        (L.map (fun σ => permAct 6 σ (z * y))).Nodup) ∧
      ((Finset.univ.filter fun u : PermMod 6 =>
        (∑ i, Multiplicative.toAdd u i = 0) ∧ wt u = wt y).card ≤ 7) := by
  have hD0le : D0 ≤ alternatingGroup (Fin 6) := fun s hs => Perm.mem_alternatingGroup.mpr (D0_even s hs)
  have hDle : D ≤ alternatingGroup (Fin 6) := fun d hd => Perm.mem_alternatingGroup.mpr (hDe d hd)
  obtain ⟨τ, hτ⟩ := exists_conj_sylow fac_alt6 hDle hD0le hD8 D0_card
  have hgens : ∀ s ∈ gens, τ⁻¹ * s * τ ∈ D := fun s hs => (hτ s).1 (Subgroup.subset_closure hs)
  have hconj : ∀ (s : Perm (Fin 6)) (y : PermMod 6),
      permAct 6 s (permAct 6 τ y) = permAct 6 τ (permAct 6 (τ⁻¹ * s * τ) y) := by
    intro s y
    rw [permAct_conj_inv_apply, permAct_inv_apply_self']
  have hinj := (permAct 6 τ).injective
  have hz' : CondZ (permAct 6 τ z) := by
    refine ⟨by rw [sum_permAct]; exact hz, fun h => hz1 (hinj (by rw [h, map_one])), fun s hs => ?_⟩
    rw [hconj, (hDV _ (hgens s hs)).1]
  have hv' : CondV (permAct 6 τ z) (permAct 6 τ v) := by
    refine ⟨by rw [sum_permAct]; exact hv, fun h => hv1 (hinj (by rw [h, map_one])),
      fun h => hvz (hinj h), fun s hs => ?_, ?_⟩
    · rw [hconj, ← map_mul]
      rcases (hDV _ (hgens s hs)).2 with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr (by rw [h])
    · rw [wt_permAct, wt_permAct, ← map_mul, wt_permAct]
      exact hwt
  have hcl := classify _ hz' _ hv'
  have hΛ : permAct 6 τ z = a ∧ (permAct 6 τ v = w ∨ permAct 6 τ v = a * w) := hcl
  obtain ⟨hza, hvw⟩ := hΛ
  have hg'z : permAct 6 (τ * g * τ⁻¹) a = a := by
    rw [← hza, permAct_conj_apply, hgz]
  have hg'3 : (τ * g * τ⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hg3]; group
  have hgv1' : permAct 6 (τ * g * τ⁻¹) (permAct 6 τ v) ≠ permAct 6 τ v := by
    rw [permAct_conj_apply]; exact fun h => hgv1 (hinj h)
  have hgv2' : permAct 6 (τ * g * τ⁻¹) (permAct 6 τ v) ≠ a * permAct 6 τ v := by
    rw [permAct_conj_apply, ← hza, ← map_mul]; exact fun h => hgv2 (hinj h)
  have hvmem : permAct 6 τ v ∈ [w, a * w] := by
    rcases hvw with h | h
    · simp [h]
    · simp [h]
  have hga := g_analysis _ hg'z hg'3 _ hvmem hgv1' hgv2'
  have hcard := card_join3F_conj τ g z v
  rw [hza] at hcard
  have hxmem : x ∈ join3F a (permAct 6 τ v) (τ * g * τ⁻¹) := by
    rcases hga with h | h
    · exact (hne (hcard.symm.trans h)).elim
    · exact h
  rw [← hza, join3F_conj] at hxmem
  obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hxmem
  have hyx' : permAct 6 τ y = x := hyx
  have hDfix : ∀ (u : PermMod 6), (∀ s ∈ D0, permAct 6 s (permAct 6 τ u) = permAct 6 τ u) →
      ∀ d ∈ D, permAct 6 d u = u := by
    intro u hu d hd
    have hs : τ * d * τ⁻¹ ∈ D0 := (hτ _).2 (by
      have : τ⁻¹ * (τ * d * τ⁻¹) * τ = d := by group
      rw [this]; exact hd)
    have h := hu _ hs
    rw [hconj, show τ⁻¹ * (τ * d * τ⁻¹) * τ = d by group] at h
    exact hinj h
  have hxD0 : ∀ s ∈ D0, permAct 6 s x = x :=
    fix_of_closure (S := {s | s ∈ gens}) x_fix
  refine ⟨y, hy, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← sum_permAct τ y, hyx']; exact x_core
  · intro h; rw [h, map_one] at hyx'; exact x_ne_one hyx'.symm
  · intro h; apply x_ne_a; rw [← hyx', h]; exact hza
  · exact hDfix y (fun s hs => by rw [hyx']; exact hxD0 s hs)
  · intro u hu hDu
    have hfix : ∀ s ∈ gens, permAct 6 s (permAct 6 τ u) = permAct 6 τ u := by
      intro s hs
      rw [hconj, hDu _ (hgens s hs)]
    rcases fixed_vectors _ (by rw [sum_permAct]; exact hu) hfix with h | h | h | h
    · left; exact hinj (by rw [h, map_one])
    · right; left; exact hinj (by rw [h, hza])
    · right; right; right
      apply hinj
      rw [map_mul, hza, hyx', ab_eq, h]
    · right; right; left; exact hinj (by rw [h, hyx'])
  · obtain ⟨j₀, j₀', hj₀s, hj₀s', hj₀x, hj₀a, hj₀'x, hj₀'v⟩ := exists_jj
    have hτy : permAct 6 τ⁻¹ x = y := by rw [← hyx']; exact permAct_inv_apply_self τ y
    refine ⟨τ⁻¹ * j₀ * τ, by rw [sign_conj]; exact hj₀s, ?_, ?_⟩
    · rw [permAct_conj_inv_apply, hyx', hj₀x, hτy]
    · intro h
      apply hj₀a
      rw [permAct_conj_inv_apply, hza] at h
      have := congrArg (permAct 6 τ) h
      rw [permAct_inv_apply_self', hza] at this
      exact this
  · obtain ⟨j₀, j₀', hj₀s, hj₀s', hj₀x, hj₀a, hj₀'x, hj₀'v⟩ := exists_jj
    have hτy : permAct 6 τ⁻¹ x = y := by rw [← hyx']; exact permAct_inv_apply_self τ y
    refine ⟨τ⁻¹ * j₀' * τ, by rw [sign_conj]; exact hj₀s', ?_, ?_, ?_, ?_⟩
    · rw [permAct_conj_inv_apply, hyx', hj₀'x, hτy]
    · intro h
      apply (hj₀'v _ hvmem).1
      rw [permAct_conj_inv_apply] at h
      have := congrArg (permAct 6 τ) h
      rw [permAct_inv_apply_self'] at this
      exact this
    · intro h
      apply (hj₀'v _ hvmem).2.1
      rw [permAct_conj_inv_apply] at h
      have := congrArg (permAct 6 τ) h
      rw [permAct_inv_apply_self', map_mul, hza] at this
      exact this
    · intro h
      apply (hj₀'v _ hvmem).2.2
      rw [permAct_conj_inv_apply] at h
      have := congrArg (permAct 6 τ) h
      rw [permAct_inv_apply_self', hza] at this
      exact this
  · obtain ⟨L, hL8, hLs, hLn⟩ := pigeon_list
    refine ⟨L.map (fun σ => τ⁻¹ * σ * τ), by simpa using hL8, ?_, ?_⟩
    · intro σ hσ
      rw [List.mem_map] at hσ
      obtain ⟨σ', hσ', rfl⟩ := hσ
      rw [sign_conj]
      exact hLs σ' hσ'
    · have hzy : permAct 6 τ (z * y) = b := by rw [map_mul, hza, hyx', ab_eq]
      have : (List.map (fun σ => permAct 6 σ (z * y)) (L.map fun σ => τ⁻¹ * σ * τ)) =
          (L.map (fun σ => permAct 6 σ b)).map (permAct 6 τ⁻¹) := by
        rw [List.map_map, List.map_map]
        refine List.map_congr_left fun σ _ => ?_
        simp only [Function.comp]
        rw [permAct_conj_inv_apply, hzy]
      rw [this]
      exact hLn.map (permAct 6 τ⁻¹).injective
  · have hwy : wt y = wt x := by rw [← hyx', wt_permAct]
    rw [hwy]
    exact wt_count

end M6

theorem modelOut6 : ModelOut 6 := M6.modelOut

end CFSG.Quasithin.ModC
