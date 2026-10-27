module

public import CFSG.Assembly.Defs

public section

namespace CFSG.Quasithin.E6.Alt.A7

open Equiv Equiv.Perm

@[expose] def toT (σ : Perm (Fin 7)) : List ℕ := (List.finRange 7).map fun i => (σ i).val

@[expose] def compT (a b : List ℕ) : List ℕ := b.map fun i => a.getD i 0

theorem getD_toT (σ : Perm (Fin 7)) (i : Fin 7) : (toT σ).getD i.val 0 = (σ i).val := by
  simp [toT, List.getD_eq_getElem?_getD]

theorem toT_mul (σ τ : Perm (Fin 7)) : toT (σ * τ) = compT (toT σ) (toT τ) := by
  unfold compT toT
  rw [List.map_map]
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply, Perm.mul_apply]
  exact (getD_toT σ (τ i)).symm

theorem toT_injective : Function.Injective toT := by
  intro σ τ h
  refine Equiv.ext fun i => Fin.ext ?_
  rw [← getD_toT σ i, ← getD_toT τ i, h]

theorem toT_one : toT 1 = [0, 1, 2, 3, 4, 5, 6] := by decide +kernel

@[expose] def mk7 (f g : Fin 7 → Fin 7) (h1 : ∀ x, g (f x) = x) (h2 : ∀ x, f (g x) = x) :
    Perm (Fin 7) := ⟨f, g, h1, h2⟩

@[expose] def g1 : Perm (Fin 7) :=
  mk7 ![1, 2, 3, 0, 5, 4, 6] ![3, 0, 1, 2, 5, 4, 6] (by decide) (by decide)

@[expose] def g2 : Perm (Fin 7) :=
  mk7 ![1, 0, 3, 2, 4, 5, 6] ![1, 0, 3, 2, 4, 5, 6] (by decide) (by decide)

@[expose] def pa : Perm (Fin 7) :=
  mk7 ![2, 3, 0, 1, 4, 5, 6] ![2, 3, 0, 1, 4, 5, 6] (by decide) (by decide)

@[expose] def pb : Perm (Fin 7) :=
  mk7 ![0, 1, 2, 3, 5, 4, 6] ![0, 1, 2, 3, 5, 4, 6] (by decide) (by decide)

@[expose] def dp : Fin 8 → Perm (Fin 7) := ![1, g1, pa,
  mk7 ![3, 0, 1, 2, 5, 4, 6] ![1, 2, 3, 0, 5, 4, 6] (by decide) (by decide), g2,
  mk7 ![0, 3, 2, 1, 5, 4, 6] ![0, 3, 2, 1, 5, 4, 6] (by decide) (by decide),
  mk7 ![3, 2, 1, 0, 4, 5, 6] ![3, 2, 1, 0, 4, 5, 6] (by decide) (by decide),
  mk7 ![2, 1, 0, 3, 5, 4, 6] ![2, 1, 0, 3, 5, 4, 6] (by decide) (by decide)]

@[expose] def dtabs : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6], [1, 2, 3, 0, 5, 4, 6], [2, 3, 0, 1, 4, 5, 6], [3, 0, 1, 2, 5, 4, 6],
   [1, 0, 3, 2, 4, 5, 6], [0, 3, 2, 1, 5, 4, 6], [3, 2, 1, 0, 4, 5, 6], [2, 1, 0, 3, 5, 4, 6]]

theorem dtabs_mul : ∀ a ∈ dtabs, ∀ b ∈ dtabs, compT a b ∈ dtabs := by decide +kernel

theorem dtabs_pow4 : ∀ a ∈ dtabs, compT a (compT a (compT a a)) = [0, 1, 2, 3, 4, 5, 6] := by
  decide +kernel

theorem dtabs_nodup : dtabs.Nodup := by decide +kernel

theorem toT_dp : ∀ i : Fin 8, toT (dp i) = dtabs.getD i.val [] := by decide +kernel

theorem sign_dp : ∀ i : Fin 8, Perm.sign (dp i) = 1 := by decide +kernel

@[expose] def D7 : Subgroup (Perm (Fin 7)) where
  carrier := {σ | toT σ ∈ dtabs}
  mul_mem' := fun {a b} ha hb => by
    show toT (a * b) ∈ dtabs
    rw [toT_mul]
    exact dtabs_mul _ ha _ hb
  one_mem' := by
    show toT 1 ∈ dtabs
    rw [toT_one]
    decide +kernel
  inv_mem' := fun {a} ha => by
    have h4 : a * (a * (a * a)) = 1 :=
      toT_injective (by rw [toT_mul, toT_mul, toT_mul, toT_one]; exact dtabs_pow4 _ ha)
    have hinv : a⁻¹ = a * (a * a) := inv_eq_of_mul_eq_one_right h4
    show toT a⁻¹ ∈ dtabs
    rw [hinv, toT_mul, toT_mul]
    exact dtabs_mul _ ha _ (dtabs_mul _ ha _ ha)

theorem mem_D7 {σ : Perm (Fin 7)} : σ ∈ D7 ↔ toT σ ∈ dtabs := Iff.rfl

theorem D7_eq_range : (D7 : Set (Perm (Fin 7))) = Set.range dp := by
  ext σ
  constructor
  · intro h
    obtain ⟨i, hi, hiσ⟩ := List.mem_iff_getElem.1 (mem_D7.1 h)
    refine ⟨⟨i, by simp [dtabs] at hi; omega⟩, toT_injective ?_⟩
    rw [toT_dp]
    simpa [List.getD_eq_getElem?_getD, hi] using hiσ
  · rintro ⟨i, rfl⟩
    show toT (dp i) ∈ dtabs
    rw [toT_dp]
    have : i.val < dtabs.length := by simp [dtabs]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]

theorem dp_injective : Function.Injective dp := by
  intro i j h
  have h1 : toT (dp i) = toT (dp j) := by rw [h]
  rw [toT_dp, toT_dp] at h1
  have hi : i.val < dtabs.length := by simp [dtabs]
  have hj : j.val < dtabs.length := by simp [dtabs]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hj, Option.getD_some] at h1
  exact Fin.ext ((List.Nodup.getElem_inj_iff dtabs_nodup).1 h1)

theorem card_D7 : Nat.card D7 = 8 := by
  have : Nat.card (Set.range dp) = 8 := by
    rw [← Nat.card_congr (Equiv.ofInjective dp dp_injective)]
    simp
  rw [← D7_eq_range] at this
  exact this

theorem D7_le_alt : D7 ≤ alternatingGroup (Fin 7) := fun σ hσ => by
  rw [mem_alternatingGroup]
  have : σ ∈ Set.range dp := D7_eq_range ▸ hσ
  obtain ⟨i, rfl⟩ := this
  exact sign_dp i

theorem card_alt7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 7)
  rw [Nat.card_eq_fintype_card (α := Equiv.Perm (Fin 7)), Fintype.card_perm,
    Fintype.card_fin] at h
  have h5040 : Nat.factorial 7 = 5040 := by decide
  omega

@[expose] def D7q : Subgroup (alternatingGroup (Fin 7)) := D7.subgroupOf (alternatingGroup (Fin 7))

theorem card_D7q : Nat.card D7q = 8 :=
  (Nat.card_congr (Subgroup.subgroupOfEquivOfLe D7_le_alt).toEquiv).trans card_D7

end CFSG.Quasithin.E6.Alt.A7
