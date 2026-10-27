module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# First-case involution count data

The count at the end of Section 3 of Bender's dihedral-Sylow paper is
packaged as `FirstCaseCountData`.  The numerical fields are

* `k` = `|K|`, where `K` is the Hall subgroup of `F(U)` inverted by every
  involution of `Ĥ ∖ V`;
* `b₀, ..., b₄`, the numbers of non-base cosets of `Ĥ` containing exactly
  `0, ..., 4` involutions.

The nine displayed identities (1)--(9) of
`refs/bender-dihedral-sylow.tex` (pp. 223--224) appear as `h1_Jn`,
`h1_H`, `h1_Hhat`, `h2_index`, `h2_total`, `h3`, `h4`, `h5`, `h6`, `h7`,
`h8`, `h9`.  Identities (5)--(7) are group-theoretic conditions; the
consumer below only uses the arithmetic consequences, which are recorded as
the derived fields `hK`, `h4ne`, `h4dvd`, `h3zero`, `h1dvd`, and `hH_card`.
-/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-- The number of involutions in the coset `Ĥ * x`. -/
public def firstCaseCosetInvolutions
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (x : G) : ℕ :=
  Nat.card {z : G // IsInvolution z ∧ z ∈ (c.Hhat : Set G) * ({x} : Set G)}

/-- Bender's `J_n`: involutions outside `Ĥ` whose `Ĥ`-coset contains
exactly `n` involutions. -/
@[expose] public def firstCaseJ
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (n : ℕ) : Set G :=
  {x : G | IsInvolution x ∧ x ∉ c.Hhat ∧ firstCaseCosetInvolutions c x = n}

/-- The `b_n` counting function, with `b_n = 0` for `n ≥ 5` (the source
proves `b_n` vanishes there). -/
@[expose] public def firstCaseBn (b0 b1 b2 b3 b4 : ℕ) : ℕ → ℕ
  | 0 => b0
  | 1 => b1
  | 2 => b2
  | 3 => b3
  | 4 => b4
  | _ => 0

/-- The Section-3 first-case counting package: the nine displayed source
identities together with the derived numerical facts needed for the final
index and order calculation. -/
public structure FirstCaseCountData
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) where
  k : ℕ
  b0 : ℕ
  b1 : ℕ
  b2 : ℕ
  b3 : ℕ
  b4 : ℕ
  -- Identity (1): `|J_n| = n * b_n`.
  h1_Jn : ∀ n : ℕ, n ≤ 4 →
    Nat.card {x : G // x ∈ firstCaseJ c n} =
      n * firstCaseBn b0 b1 b2 b3 b4 n
  -- Identity (1): `|H ∩ J| = 3 + 2k`.
  h1_H : Nat.card {x : G // IsInvolution x ∧ x ∈ c.H} = 3 + 2 * k
  -- Identity (1): `|Ĥ ∩ J| = 3 + 6k`.
  h1_Hhat : Nat.card {x : G // IsInvolution x ∧ x ∈ c.Hhat} = 3 + 6 * k
  -- Identity (2): `|G : H| = 3 * |G : Ĥ|`.
  h2_index : c.H.index = 3 * c.Hhat.index
  -- Identity (2): the total involution count.
  h2_total : Nat.card {x : G // IsInvolution x} =
    3 + 6 * k + b1 + 2 * b2 + 3 * b3 + 4 * b4
  -- Identity (3): `|G : Ĥ| = 1 + Σ b_n`.
  h3 : c.Hhat.index = 1 + b0 + b1 + b2 + b3 + b4
  -- Identity (4): `6k + Σ (n-3) b_n = 0` (with `b_n = 0` for `n ≥ 5`).
  h4 : 6 * k + b4 = 3 * b0 + 2 * b1 + b2
  -- Identity (5): `I_{VU}(y) = 1` for every involution `y ∉ Ĥ`.
  h5 : ∀ y : G, IsInvolution y → y ∉ c.Hhat →
    Nat.card {x : G // x ∈ invertedElements (twoCoreOf c.Hhat ⊔ c.U) y} = 1
  -- Identity (6): for `n ≥ 4`, `I_{O(D)}(y) ≠ 1` or `I_{O(D)}(sy) ≠ 1`
  -- for an involution `s ∈ C_D(y)`, where `D = Ĥ ∩ Ĥ^y`.
  h6 : ∀ y : G, IsInvolution y → y ∉ c.Hhat →
    4 ≤ firstCaseCosetInvolutions c y →
      ∃ s : G, IsInvolution s ∧
        s ∈ (c.Hhat ⊓ conjugateSubgroup c.Hhat y) ∧ s * y = y * s ∧
          (Nat.card {x : G // x ∈
              invertedElements (oddCoreOf (c.Hhat ⊓ conjugateSubgroup c.Hhat y : Subgroup G)) y} ≠ 1 ∨
            Nat.card {x : G // x ∈
              invertedElements (oddCoreOf (c.Hhat ⊓ conjugateSubgroup c.Hhat y : Subgroup G)) (s * y)} ≠ 1)
  -- Identity (7): for `n ≥ 4`, an inverted nontrivial `2'`-subgroup forces
  -- `|U| = k = 3`, `n = 4`, and the index-six intersection
  -- `D/(D ∩ VU)` with `D = Ĥ ∩ Ĥ^y`.  The printed full `D₆` isomorphism is
  -- incompatible with the order-nine sentence that follows it; the retained
  -- endpoint is the index-six quotient used by the proof.
  h7 : ∀ (n : ℕ) (y : G) (X : Subgroup G),
    4 ≤ n → y ∈ firstCaseJ c n → X ≠ ⊥ → X ≤ c.Hhat →
    Nat.Coprime 2 (Nat.card X) →
      (∀ x : G, x ∈ X → x ∈ invertedElements c.Hhat y) →
        Even (Nat.card (Subgroup.centralizer (X : Set G))) →
          Even (Nat.card ((Subgroup.normalizer (X : Set G) ⊓ c.Hhat : Subgroup G))) →
            Nat.card c.U = k ∧ k = 3 ∧ n = 4 ∧
              (let D := c.Hhat ⊓ conjugateSubgroup c.Hhat y
               let N := D ⊓ (twoCoreOf c.Hhat ⊔ c.U)
               (N.subgroupOf D).index = 6)
  -- Identity (8): `3 b₄ + b₂ = 6k²`.
  h8 : 3 * b4 + b2 = 6 * k ^ 2
  -- Identity (9): `6k + b₄ - b₂ - 2b₁ - 3b₀ = 0` (division-free form).
  h9 : 6 * k + b4 = 3 * b0 + 2 * b1 + b2
  -- Derived from (7): `k = 3`.
  hK : k = 3
  -- Derived from the `b₄ = 0` contradiction: `b₄ ≠ 0`.
  h4ne : b4 ≠ 0
  -- Derived from the fixed-point-free `KV` action: `12 ∣ b₄`.
  h4dvd : 12 ∣ b4
  -- The source's separate `b₃ = 0` argument.
  h3zero : b3 = 0
  -- `|S| = 8` divides `b₁`.
  h1dvd : 8 ∣ b1
  -- The Klein-four-branch order fact `|H| = |S| * |U| = 8k`, needed to turn
  -- the index computation into `|G| = 2520`.
  hH_card : Nat.card c.H = 8 * k

/-- The arithmetic consumer of `FirstCaseCountData`: the nine identities
together with the derived numerical facts give `|G : Ĥ| = 35` and
`|G| = 2³ · 3² · 5 · 7`. -/
public theorem firstCase_index_card_of_countData
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (d : FirstCaseCountData c) :
    c.Hhat.index = 35 ∧ Nat.card G = 2 ^ 3 * 3 ^ 2 * 5 * 7 := by
  classical
  obtain ⟨m, hm⟩ := d.h4dvd
  have h8' : 3 * d.b4 + d.b2 = 54 := by
    have h8'' := d.h8
    rw [d.hK] at h8''
    norm_num at h8''
    exact h8''
  have hb4le : d.b4 ≤ 18 := by omega
  have hm1 : m = 1 := by
    have hb4m : d.b4 = 12 * m := hm
    have hmle : m ≤ 1 := by omega
    have hmne : m ≠ 0 := by
      intro hm0
      apply d.h4ne
      omega
    omega
  have hb4 : d.b4 = 12 := by omega
  have hb2 : d.b2 = 18 := by omega
  have h9' : 6 * d.k + d.b4 = 3 * d.b0 + 2 * d.b1 + d.b2 := d.h9
  have h9'' : 3 * d.b0 + 2 * d.b1 = 12 := by
    rw [d.hK, hb4, hb2] at h9'
    omega
  obtain ⟨n, hn⟩ := d.h1dvd
  have hn0 : n = 0 := by
    have hb1n : d.b1 = 8 * n := hn
    omega
  have hb1 : d.b1 = 0 := by omega
  have hb0 : d.b0 = 4 := by omega
  have hindex : c.Hhat.index = 35 := by
    rw [d.h3, d.h3zero]
    omega
  have hHindex : c.H.index = 105 := by
    rw [d.h2_index, hindex]
  have hGcard : Nat.card G = 2 ^ 3 * 3 ^ 2 * 5 * 7 := by
    calc
      Nat.card G = Nat.card c.H * c.H.index := (c.H.card_mul_index).symm
      _ = (8 * d.k) * c.H.index := by rw [d.hH_card]
      _ = (8 * 3) * 105 := by rw [d.hK, hHindex]
      _ = 2 ^ 3 * 3 ^ 2 * 5 * 7 := by norm_num
  exact ⟨hindex, hGcard⟩

end CFSG.GorensteinWalter
