module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcRaw

public section

namespace CFSG.StandardType.GGQ2Frame.ExcRaw

structure SatWitness (m : Fin 6) (c : Finset (Root m)) where
  r : ℕ
  b : Fin r → Root m
  k : Fin r → Root m
  e : ℤ
  n : Root m → Fin r → ℤ
  A : Fin r → Fin r → ℤ
  D : ℤ
  b_mem : ∀ a, b a ∈ c
  pairing_eq : ∀ i ∈ c, ∀ j, e * pairing m j i = ∑ a, n i a * pairing m j (b a)
  mul_eq : ∀ a a', ∑ a'', A a a'' * pairing m (k a'') (b a') = if a = a' then D else 0
  not_three_dvd_e : ¬ (3 : ℤ) ∣ e
  not_three_dvd_D : ¬ (3 : ℤ) ∣ D

structure A8Witness (m : Fin 6) (c : Finset (Root m)) where
  b : Fin 8 → Root m
  cz : V m
  b_mem : ∀ a, b a ∈ c
  gram : ∀ a a' : Fin 8, pairing m (b a) (b a') =
    if a = a' then 2 else if (a : ℕ) + 1 = a' ∨ (a' : ℕ) + 1 = a then -1 else 0
  span : ∀ i ∈ c, ∃ a a' : ℕ, a < a' ∧ a' ≤ 8 ∧ ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ j,
    pairing m i j =
      ε * ∑ s ∈ Finset.univ.filter (fun s : Fin 8 => a ≤ (s : ℕ) ∧ (s : ℕ) < a'), pairing m (b s) j
  root_cz : ∀ k, ∃ ℓ : ℤ, ∑ a : Fin 8, ((a : ℕ) + 1 : ℤ) * pairing m k (b a) = 3 * ℓ ∧
    (ℓ : ZMod 3) = root m k cz
  hyper : ∀ v : V m, ∃ x : ZMod 3, v - x • cz ∈ inside m c

@[expose] def InsideFlag (m : Fin 6) (c : Finset (Root m)) : Prop :=
  ((m.val = 2 ∨ m.val = 3) ∧ (c = Finset.univ ∨
      ∃ k, c = Finset.univ.filter fun i => pairing m k i = 0 ∧ pairing m i k = 0)) ∨
    (m.val = 5 ∧ Nonempty (A8Witness m c))

@[expose] def InsideCensus (m : Fin 6) : Prop :=
  ∀ (U : Submodule (ZMod 3) (V m)) (c : Finset (Root m)), occurs m U c →
    Nonempty (SatWitness m c) ∨ InsideFlag m c

end CFSG.StandardType.GGQ2Frame.ExcRaw
