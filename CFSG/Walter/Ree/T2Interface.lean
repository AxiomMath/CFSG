module

public import CFSG.Walter.Ree.Defs
public import CFSG.Walter.Ree.ThompsonN
public import CFSG.Walter.ReeOrder.Ward.Defs

public section

namespace CFSG.Walter.Ree.T2

open CFSG.Walter.Ward

@[expose] def gf8Add (a b : Fin 8) : Fin 8 := ⟨(a.val ^^^ b.val) % 8, Nat.mod_lt _ (by norm_num)⟩

@[expose] def gf8Mul (a b : Fin 8) : Fin 8 :=
  let p := (if b.val.testBit 0 then a.val else 0) ^^^ (if b.val.testBit 1 then 2 * a.val else 0)
    ^^^ (if b.val.testBit 2 then 4 * a.val else 0)
  let p := if p.testBit 4 then p ^^^ 22 else p
  let p := if p.testBit 3 then p ^^^ 11 else p
  ⟨p % 8, Nat.mod_lt _ (by norm_num)⟩

@[expose] def gf8Inv (a : Fin 8) : Fin 8 :=
  gf8Mul (gf8Mul a a) (gf8Mul (gf8Mul a a) (gf8Mul a a))

@[expose] def mobius (a b c d : Fin 8) (x : Fin 9) : Fin 9 :=
  if hx : x.val < 8 then
    if gf8Add (gf8Mul c ⟨x.val, hx⟩) d = 0 then 8
    else (gf8Mul (gf8Add (gf8Mul a ⟨x.val, hx⟩) b)
      (gf8Inv (gf8Add (gf8Mul c ⟨x.val, hx⟩) d))).castSucc
  else if c = 0 then 8 else (gf8Mul a (gf8Inv c)).castSucc

@[expose] def frobPow (e : ℕ) (x : Fin 9) : Fin 9 :=
  if hx : x.val < 8 then
    (((List.replicate e (⟨x.val, hx⟩ : Fin 8)).foldr gf8Mul 1 : Fin 8)).castSucc
  else 8

@[expose] def pglJ : Equiv.Perm (Fin 9) := ⟨mobius 1 1 0 1, mobius 1 1 0 1, by decide, by decide⟩

@[expose] def pglK : Equiv.Perm (Fin 9) := ⟨mobius 1 2 0 1, mobius 1 2 0 1, by decide, by decide⟩

@[expose] def pglT : Equiv.Perm (Fin 9) := ⟨frobPow 4, frobPow 2, by decide, by decide⟩

@[expose] def pglY : Equiv.Perm (Fin 9) := ⟨mobius 4 2 2 6, mobius 6 2 2 4, by decide, by decide⟩

@[expose] def PGammaL28 : Subgroup (Equiv.Perm (Fin 9)) :=
  Subgroup.closure {pglJ, pglK, pglT, pglY}

@[expose] def PGammaL28.j : PGammaL28 := ⟨pglJ, Subgroup.subset_closure (by simp)⟩

@[expose] def PGammaL28.k : PGammaL28 := ⟨pglK, Subgroup.subset_closure (by simp)⟩

@[expose] def PGammaL28.t : PGammaL28 := ⟨pglT, Subgroup.subset_closure (by simp)⟩

@[expose] def PGammaL28.y : PGammaL28 := ⟨pglY, Subgroup.subset_closure (by simp)⟩

theorem pglY_pow_nine : pglY ^ 9 = 1 ∧ pglY ^ 3 ≠ 1 := by decide

theorem pglT_conj : pglT⁻¹ * pglJ * pglT = pglJ ∧
    (∀ x, (pglT⁻¹ * pglK * pglT) x = mobius 1 4 0 1 x) ∧
    ∀ x, (pglT⁻¹ * pglY * pglT) x = mobius 6 4 4 2 x := by decide

variable {k : Type} [Field k] [CharP k 3]

@[expose] def pp (σ : k ≃+* k) (x y z : k) : ThompsonN k σ := ⟨1, x, y, z⟩

@[expose] def tT (σ : k ≃+* k) : ThompsonN k σ := pp σ 0 1 0

@[expose] def tY (σ : k ≃+* k) (d : k) : ThompsonN k σ := pp σ 1 0 d

@[expose] def incl {G : Type} [Group G] {N : Subgroup G} {σ : k ≃+* k} (e : N ≃* ThompsonN k σ) :
    ThompsonN k σ →* G :=
  N.subtype.comp e.symm.toMonoidHom

structure RType (G : Type) [Group G] [Finite G] (k : Type) [Field k] [CharP k 3]
    (σ : k ≃+* k) (d : k) where
  hyp : ReeTypeHyp G
  P : Sylow 3 G
  e : Subgroup.normalizer ((P : Subgroup G) : Set G) ≃* ThompsonN k σ
  K : G
  K_not_mem : K ∉ Subgroup.normalizer ((P : Subgroup G) : Set G)
  K_inv : ∀ t : kˣ, K⁻¹ * incl e (ThompsonN.torus σ t) * K = incl e (ThompsonN.torus σ t⁻¹)
  base : PGammaL28 →* G
  base_injective : Function.Injective base
  base_j : base PGammaL28.j = incl e (ThompsonN.J σ)
  base_k : base PGammaL28.k = K
  base_t : base PGammaL28.t = incl e (tT σ)
  base_y : base PGammaL28.y = incl e (tY σ d)

namespace RType

variable {G : Type} [Group G] [Finite G] {σ : k ≃+* k} {d : k}

@[expose] def N (R : RType G k σ d) : Subgroup G :=
  Subgroup.normalizer ((R.P : Subgroup G) : Set G)

@[expose] def ι (R : RType G k σ d) : ThompsonN k σ →* G := incl R.e

end RType

@[expose] def ThompsonPresentation {G : Type} [Group G] {σ : k ≃+* k}
    (ι : ThompsonN k σ →* G) (N : Subgroup G) (K : G) : Prop :=
  (∀ g : G, g ∉ N → ∃ (ν : ThompsonN k σ) (x y z : k), g = ι ν * K * ι (pp σ x y z)) ∧
  ∀ (ν ν' : ThompsonN k σ) (x y z x' y' z' : k),
    ι ν * K * ι (pp σ x y z) = ι ν' * K * ι (pp σ x' y' z') → ν = ν' ∧ x = x' ∧ y = y' ∧ z = z'

section Facts

variable {G : Type} [Group G] [Finite G] {σ : k ≃+* k} {d : k}

@[expose] def IsS (R : RType G k σ d) (S : k → k × k × k) : Prop :=
  ∀ x : k, ∃ ν : ThompsonN k σ,
    R.K * R.ι (pp σ 0 x 1) * R.K = R.ι ν * R.K * R.ι (pp σ (S x).1 (S x).2.1 (S x).2.2)

@[expose] def Eq69 (R : RType G k σ d) : Prop :=
  ∀ a : ℕ, Even a → (∀ x : k, (σ x * x) ^ a = x ^ 2) → ∀ (x : k) (hx : x ≠ 0),
    R.ι (pp σ 0 x 0) * R.ι (ThompsonN.torus σ ((Units.mk0 x hx)⁻¹ ^ a)) * R.K *
      R.ι (pp σ 0 x 0) = R.K * R.ι (pp σ 0 (-x⁻¹) 0) * R.K

@[expose] def hopkinsE (σ : k ≃+* k) : Set (k × k × k) :=
  {p | σ p.1 * p.1 ^ 2 - σ p.2.1 * p.2.1 ^ 2 = -1 ∧ σ p.1 * p.1 - σ p.2.1 * p.2.1 = p.2.2}

@[expose] def ThompsonIdentity (_R : RType G k σ d) : Prop :=
  ∀ a : ℕ, Even a → (∀ x : k, (σ x * x) ^ a = x ^ 2) →
    ∀ p ∈ ESigma k σ, thompsonT a p.1 p.2.1 p.2.2 = 0

@[expose] def coef211 (σ : k ≃+* k) (a : ℕ) (z y u : k) : k :=
  σ y * y ^ 2 * ((u + 1) ^ (2 + a) - u ^ (2 + a)) / (u ^ (2 + a) - (u ^ 2 - 1) ^ (2 + a)) -
    σ z * z ^ 2 * ((u - 1) ^ (2 + a) - u ^ (2 + a)) / (u ^ (2 + a) - (u ^ 2 - 1) ^ (2 + a)) + 1

@[expose] def Eq211 (_R : RType G k σ d) (a : ℕ) (c : k → k → k → k) : Prop :=
  ∀ z y u : k, (z, y, u) ∈ hopkinsE σ → z * y * u ≠ 0 →
    u ^ (2 + a) - (u ^ 2 - 1) ^ (2 + a) ≠ 0 → coef211 σ a z y u * d = c z y u

end Facts

@[expose] def BaseExists : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] [CharP k 3] (G : Type) [Group G] [Finite G]
    (_h : ReeTypeHyp G) (σ : k ≃+* k), (∃ P : Sylow 3 G,
      Nonempty (Subgroup.normalizer ((P : Subgroup G) : Set G) ≃* ThompsonN k σ)) →
    ∃ d : k, Nonempty (RType G k σ d)

structure Thompson2 : Prop where
  base : BaseExists
  thompsonIdentity : ∀ (k : Type) [Field k] [Fintype k] [CharP k 3] (σ : k ≃+* k) (d : k)
    (G : Type) [Group G] [Finite G] (R : RType G k σ d), ThompsonIdentity R
  sExplicit : ∀ (k : Type) [Field k] [Fintype k] [CharP k 3] (σ : k ≃+* k),
    (∀ x, σ (σ x) = x ^ 3) → ∀ d : k,
      ∃ S : k → k × k × k, ∀ (G : Type) [Group G] [Finite G] (R : RType G k σ d), IsS R S
  eq211 : ∀ (k : Type) [Field k] [Fintype k] [CharP k 3] (σ : k ≃+* k),
    (∀ x, σ (σ x) = x ^ 3) → ∀ a : ℕ, Even a → (∀ x : k, (σ x * x) ^ a = x ^ 2) →
      a < Fintype.card k - 1 → ∃ c : k → k → k → k,
        ∀ (d : k) (G : Type) [Group G] [Finite G] (R : RType G k σ d), Eq211 R a c

end CFSG.Walter.Ree.T2
