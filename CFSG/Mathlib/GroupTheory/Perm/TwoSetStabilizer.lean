module

public import Mathlib.GroupTheory.Perm.MaximalSubgroups

public section

open scoped Pointwise

namespace CFSG

open Equiv

abbrev TwoSetC2 : Type := Multiplicative (ZMod 2)

abbrev twoSetC2neg : TwoSetC2 := Multiplicative.ofAdd 1

lemma twoSetC2neg_ne_one : twoSetC2neg ≠ 1 := by decide

lemma TwoSetC2.eq_one_or_eq_neg (x : TwoSetC2) : x = 1 ∨ x = twoSetC2neg := by
  revert x
  decide

lemma TwoSetC2.inv_eq_self (x : TwoSetC2) : x⁻¹ = x := by
  revert x
  decide

lemma TwoSetC2.mul_self_eq_one (x : TwoSetC2) : x * x = 1 := by
  revert x
  decide

def twoSet {n : ℕ} (a b : Fin n) : Set (Fin n) := {a, b}

def twoSetStabilizerPerm {n : ℕ} (a b : Fin n) : Subgroup (Equiv.Perm (Fin n)) :=
  MulAction.stabilizer (Equiv.Perm (Fin n)) (twoSet a b)

def twoSetSign {n : ℕ} (a b : Fin n) (σ : Equiv.Perm (Fin n)) : TwoSetC2 :=
  if σ a = b then twoSetC2neg else 1

lemma mem_twoSetStabilizerPerm_apply_a {n : ℕ} {a b : Fin n} {σ : Equiv.Perm (Fin n)}
    (hσ : σ ∈ twoSetStabilizerPerm a b) : σ a = a ∨ σ a = b := by
  have h := (MulAction.mem_stabilizer_set.mp hσ) a
  have ha : a ∈ twoSet a b := by simp [twoSet]
  simpa [twoSet, Set.mem_insert_iff, Set.mem_singleton_iff] using h.mpr ha

lemma mem_twoSetStabilizerPerm_apply_b {n : ℕ} {a b : Fin n} {σ : Equiv.Perm (Fin n)}
    (hσ : σ ∈ twoSetStabilizerPerm a b) : σ b = a ∨ σ b = b := by
  have h := (MulAction.mem_stabilizer_set.mp hσ) b
  have hb : b ∈ twoSet a b := by simp [twoSet]
  simpa [twoSet, Set.mem_insert_iff, Set.mem_singleton_iff] using h.mpr hb

lemma mem_twoSetStabilizerPerm_fixes_b_of_fixes_a {n : ℕ} {a b : Fin n} (hab : a ≠ b)
    {σ : Equiv.Perm (Fin n)} (hσ : σ ∈ twoSetStabilizerPerm a b) (ha : σ a = a) :
    σ b = b := by
  rcases mem_twoSetStabilizerPerm_apply_b hσ with h | h
  · exfalso
    have h' : σ a = σ b := by rw [ha, h]
    exact hab (σ.injective h')
  · exact h

lemma mem_twoSetStabilizerPerm_maps_b_of_maps_a {n : ℕ} {a b : Fin n} (hab : a ≠ b)
    {σ : Equiv.Perm (Fin n)} (hσ : σ ∈ twoSetStabilizerPerm a b) (ha : σ a = b) :
    σ b = a := by
  rcases mem_twoSetStabilizerPerm_apply_b hσ with h | h
  · exact h
  · exfalso
    have h' : σ a = σ b := by rw [ha, h]
    exact hab (σ.injective h')

lemma twoSetSign_mul {n : ℕ} {a b : Fin n} (hab : a ≠ b) {σ τ : Equiv.Perm (Fin n)}
    (hσ : σ ∈ twoSetStabilizerPerm a b) (hτ : τ ∈ twoSetStabilizerPerm a b) :
    twoSetSign a b (σ * τ) = twoSetSign a b σ * twoSetSign a b τ := by
  by_cases hsa : σ a = b
  · have hsb : σ b = a := mem_twoSetStabilizerPerm_maps_b_of_maps_a hab hσ hsa
    by_cases hta : τ a = b
    · have htb : τ b = a := mem_twoSetStabilizerPerm_maps_b_of_maps_a hab hτ hta
      have hpta : (σ * τ) a = a := by
        change σ (τ a) = a
        rw [hta, hsb]
      simp [twoSetSign, hab, hsa, hta, hpta, TwoSetC2.mul_self_eq_one]
    · have hta' : τ a = a := (mem_twoSetStabilizerPerm_apply_a hτ).resolve_right hta
      have htb : τ b = b := mem_twoSetStabilizerPerm_fixes_b_of_fixes_a hab hτ hta'
      have hpta : (σ * τ) a = b := by
        change σ (τ a) = b
        rw [hta', hsa]
      simp [twoSetSign, hab, hsa, hta', hpta]
  · have hsa' : σ a = a := (mem_twoSetStabilizerPerm_apply_a hσ).resolve_right hsa
    have hsb : σ b = b := mem_twoSetStabilizerPerm_fixes_b_of_fixes_a hab hσ hsa'
    by_cases hta : τ a = b
    · have htb : τ b = a := mem_twoSetStabilizerPerm_maps_b_of_maps_a hab hτ hta
      have hpta : (σ * τ) a = b := by
        change σ (τ a) = b
        rw [hta, hsb]
      simp [twoSetSign, hsa, hta, hpta]
    · have hta' : τ a = a := (mem_twoSetStabilizerPerm_apply_a hτ).resolve_right hta
      have htb : τ b = b := mem_twoSetStabilizerPerm_fixes_b_of_fixes_a hab hτ hta'
      have hpta : (σ * τ) a = a := by
        change σ (τ a) = a
        rw [hta', hsa']
      simp [twoSetSign, hab, hsa, hta', hpta]

lemma twoSetSign_inv {n : ℕ} {a b : Fin n} (hab : a ≠ b) {σ : Equiv.Perm (Fin n)}
    (hσ : σ ∈ twoSetStabilizerPerm a b) :
    twoSetSign a b σ⁻¹ = twoSetSign a b σ := by
  by_cases hsa : σ a = b
  · have hsb : σ b = a := mem_twoSetStabilizerPerm_maps_b_of_maps_a hab hσ hsa
    have hinv : σ⁻¹ a = b := (Equiv.Perm.inv_eq_iff_eq).mpr hsb.symm
    simp [twoSetSign, hsa, hinv]
  · have hsa' : σ a = a := (mem_twoSetStabilizerPerm_apply_a hσ).resolve_right hsa
    have hinv : σ⁻¹ a = a := (Equiv.Perm.inv_eq_iff_eq).mpr hsa'.symm
    simp [twoSetSign, hab, hsa, hinv]

def twoSetStabilizer {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    Subgroup (TwoSetC2 × Equiv.Perm (Fin n)) where
  carrier := {p | p.2 ∈ twoSetStabilizerPerm a b ∧ p.1 = twoSetSign a b p.2}
  one_mem' := by
    refine ⟨(twoSetStabilizerPerm a b).one_mem, ?_⟩
    simp [twoSetSign, hab]
  mul_mem' := by
    intro p q hp hq
    refine ⟨(twoSetStabilizerPerm a b).mul_mem hp.1 hq.1, ?_⟩
    change p.1 * q.1 = twoSetSign a b (p.2 * q.2)
    rw [hp.2, hq.2, twoSetSign_mul hab hp.1 hq.1]
  inv_mem' := by
    intro p hp
    refine ⟨(twoSetStabilizerPerm a b).inv_mem hp.1, ?_⟩
    change p.1⁻¹ = twoSetSign a b p.2⁻¹
    rw [hp.2, twoSetSign_inv hab hp.1, TwoSetC2.inv_eq_self]

lemma map_snd_twoSetStabilizer {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    (twoSetStabilizer a b hab).map
        (MonoidHom.snd TwoSetC2 (Equiv.Perm (Fin n))) = twoSetStabilizerPerm a b := by
  apply le_antisymm
  · rintro σ ⟨p, hp, rfl⟩
    exact hp.1
  · intro σ hσ
    exact ⟨(twoSetSign a b σ, σ), ⟨hσ, rfl⟩, rfl⟩

lemma twoSetStabilizer_fst_eq_neg_iff {n : ℕ} {a b : Fin n} (hab : a ≠ b)
    {p : TwoSetC2 × Equiv.Perm (Fin n)} (hp : p ∈ twoSetStabilizer a b hab) :
    p.1 = twoSetC2neg ↔ p.2 a = b := by
  have hsign : p.1 = twoSetSign a b p.2 := hp.2
  rw [hsign]
  by_cases h : p.2 a = b
  · simp [twoSetSign, h]
  · simp [twoSetSign, h, Ne.symm twoSetC2neg_ne_one]

lemma neg_swap_mem_twoSetStabilizer {n : ℕ} {a b : Fin n} (hab : a ≠ b) :
    (twoSetC2neg, Equiv.swap a b) ∈ twoSetStabilizer a b hab := by
  refine ⟨?_, ?_⟩
  · rw [twoSetStabilizerPerm, Equiv.swap_mem_stabilizer]
    simp [twoSet]
  · simp [twoSetSign]

lemma one_swap_compl_mem_twoSetStabilizer {n : ℕ} {a b u v : Fin n} (hab : a ≠ b)
    (hu : u ∉ twoSet a b) (hv : v ∉ twoSet a b) :
    (1, Equiv.swap u v) ∈ twoSetStabilizer a b hab := by
  have hua : u ≠ a := by
    intro h
    exact hu (by simp [twoSet, h])
  have hub : u ≠ b := by
    intro h
    exact hu (by simp [twoSet, h])
  have hva : v ≠ a := by
    intro h
    exact hv (by simp [twoSet, h])
  have hvb : v ≠ b := by
    intro h
    exact hv (by simp [twoSet, h])
  refine ⟨?_, ?_⟩
  · rw [twoSetStabilizerPerm, Equiv.swap_mem_stabilizer]
    simp [twoSet, hua, hub, hva, hvb]
  · have hfix : Equiv.swap u v a = a :=
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hua) (Ne.symm hva)
    simp [twoSetSign, hfix, hab]

lemma eq_top_of_twoSetStabilizerPerm_le_of_moved {n : ℕ} {a b : Fin n}
    (hs : (twoSet a b).Nonempty) (hsc : (twoSet a b)ᶜ.Nonempty)
    (hcard : Nat.card (Fin n) ≠ 2 * (twoSet a b).ncard)
    {K : Subgroup (Equiv.Perm (Fin n))}
    (hPK : twoSetStabilizerPerm a b ≤ K)
    {σ : Equiv.Perm (Fin n)} (hσK : σ ∈ K)
    (hσP : σ ∉ twoSetStabilizerPerm a b) : K = ⊤ := by
  have hmax := Equiv.Perm.isCoatom_stabilizer hs hsc hcard
  have hlt : twoSetStabilizerPerm a b < K :=
    lt_of_le_of_ne hPK (by
      intro h
      exact hσP (h ▸ hσK))
  exact hmax.2 K hlt

lemma eq_top_of_twoSetStabilizerPerm_six_le_of_moved
    {K : Subgroup (Equiv.Perm (Fin 6))}
    (hPK : twoSetStabilizerPerm (0 : Fin 6) 1 ≤ K)
    {σ : Equiv.Perm (Fin 6)} (hσK : σ ∈ K)
    (hσP : σ ∉ twoSetStabilizerPerm (0 : Fin 6) 1) : K = ⊤ := by
  apply eq_top_of_twoSetStabilizerPerm_le_of_moved (a := (0 : Fin 6)) (b := 1) (σ := σ)
  · exact hPK
  · exact hσK
  · exact hσP
  · exact ⟨0, by simp [twoSet]⟩
  · exact ⟨2, by simp [twoSet]⟩
  · norm_num [twoSet]

theorem twoSetStabilizer_le_of_moved_eq_top
    {H : Subgroup (TwoSetC2 × Equiv.Perm (Fin 6))}
    (hS : twoSetStabilizer (0 : Fin 6) 1 (by decide) ≤ H)
    (hmove : ∃ g ∈ H, g.2 ∉ twoSetStabilizerPerm (0 : Fin 6) 1) :
    H = ⊤ := by
  let P : Subgroup (Equiv.Perm (Fin 6)) := twoSetStabilizerPerm (0 : Fin 6) 1
  let K : Subgroup (Equiv.Perm (Fin 6)) :=
    H.map (MonoidHom.snd TwoSetC2 (Equiv.Perm (Fin 6)))
  have hPK : P ≤ K := by
    change twoSetStabilizerPerm (0 : Fin 6) 1 ≤ K
    rw [← map_snd_twoSetStabilizer (0 : Fin 6) 1 (by decide)]
    exact Subgroup.map_mono hS
  obtain ⟨g, hgH, hgP⟩ := hmove
  have hgK : g.2 ∈ K := ⟨g, hgH, rfl⟩
  have hKtop : K = ⊤ :=
    eq_top_of_twoSetStabilizerPerm_six_le_of_moved hPK hgK hgP
  have hsurj : ∀ σ : Equiv.Perm (Fin 6),
      ∃ h : TwoSetC2 × Equiv.Perm (Fin 6), h ∈ H ∧ h.2 = σ := by
    intro σ
    have hσK : σ ∈ K := by
      rw [hKtop]
      exact Subgroup.mem_top σ
    rcases hσK with ⟨h, hhH, hhσ⟩
    exact ⟨h, hhH, hhσ⟩
  have hab6 : (0 : Fin 6) ≠ 1 := by decide
  have hnegswap : (twoSetC2neg, Equiv.swap (0 : Fin 6) 1) ∈ H :=
    hS (neg_swap_mem_twoSetStabilizer (a := (0 : Fin 6)) (b := 1) hab6)
  have honeswap23 : (1, Equiv.swap (2 : Fin 6) 3) ∈ H := by
    refine hS (one_swap_compl_mem_twoSetStabilizer hab6 ?_ ?_)
    · simp [twoSet]
    · simp [twoSet]
  let c : Equiv.Perm (Fin 6) :=
    Equiv.swap (0 : Fin 6) 2 * Equiv.swap (1 : Fin 6) 3
  have hc0 : c 0 = 2 := by decide
  have hc1 : c 1 = 3 := by decide
  obtain ⟨h, hhH, hhσ⟩ := hsurj c
  have hconj : h * (twoSetC2neg, Equiv.swap (0 : Fin 6) 1) * h⁻¹ =
      (twoSetC2neg, Equiv.swap (2 : Fin 6) 3) := by
    apply Prod.ext
    · simp [mul_assoc, mul_comm]
    · simpa [hhσ, hc0, hc1] using
        (Equiv.swap_apply_apply c (0 : Fin 6) 1).symm
  have hneg23 : (twoSetC2neg, Equiv.swap (2 : Fin 6) 3) ∈ H := by
    rw [← hconj]
    exact H.mul_mem (H.mul_mem hhH hnegswap) (H.inv_mem hhH)
  have hneg : (twoSetC2neg, 1) ∈ H := by
    have hmem := H.mul_mem hneg23 (H.inv_mem honeswap23)
    simpa [Equiv.swap_mul_self] using hmem
  rw [eq_top_iff]
  intro x _
  obtain ⟨hx, hxH, hxσ⟩ := hsurj x.2
  have hxdecomp : x = (x.1 * hx.1⁻¹, 1) * hx := by
    ext <;> simp [hxσ, mul_assoc]
  rw [hxdecomp]
  by_cases hx1 : x.1 * hx.1⁻¹ = 1
  · have hmem1 : (x.1 * hx.1⁻¹, 1) ∈ H := by
      rw [hx1]
      exact H.one_mem
    exact H.mul_mem hmem1 hxH
  · have hxc : x.1 * hx.1⁻¹ = twoSetC2neg := by
      rcases TwoSetC2.eq_one_or_eq_neg (x.1 * hx.1⁻¹) with h' | h'
      · exact (hx1 h').elim
      · exact h'
    have hmem2 : (x.1 * hx.1⁻¹, 1) ∈ H := by
      rw [hxc]
      exact hneg
    exact H.mul_mem hmem2 hxH

end CFSG
