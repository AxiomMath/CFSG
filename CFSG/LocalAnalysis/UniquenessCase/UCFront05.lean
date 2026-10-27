module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.FFModules.Offenders

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F05

open CFSG.Open CFSG.RankThree.FFModules Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

@[expose] noncomputable def mGV (ρ : Representation (ZMod 2) G V) : ℕ :=
  if Even (Nat.card G) then
    sInf {n | ∃ t : G, orderOf t = 2 ∧
      n = Module.finrank (ZMod 2) (V ⧸ fixSub ρ (Subgroup.zpowers t))}
  else Module.finrank (ZMod 2) V

@[expose] def InvertedIn (H B : Subgroup G) : Prop :=
  ∃ g ∈ H, ∀ b ∈ B, g * b * g⁻¹ = b⁻¹

@[expose] noncomputable def numConj (L : Subgroup G) : ℕ :=
  {K : Subgroup G | ∃ g : G, K = L.map (MulAut.conj g).toMonoidHom}.ncard

structure Hyp51 (p : ℕ) (P T B : Subgroup G) (e : ℕ) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  pGroup : IsPGroup p P
  exponent : ∀ x ∈ P, x ^ p = 1
  classTwo : ⁅⁅P, P⁆, P⁆ = ⊥
  twoGroup : IsPGroup 2 T
  abelian : IsMulCommutative B
  oddOrder : Odd (Nat.card B)
  permutes : Permutes B T
  acts : B ⊔ T ≤ normalizer (P : Set G)
  cyclic : ∀ b ∈ B, b ≠ 1 → IsCyclic ↥(P ⊓ centralizer ({b} : Set G))
  eGt : 2 < e
  piB : ∀ r : ℕ, r.Prime → (r ∣ Nat.card B ↔ r ∣ 2 ^ e - 1)
  expB : ∀ r : ℕ, r.Prime → r ∣ Nat.card B → ∀ x ∈ pCoreOf r B, x ^ r = 1
  normT : Odd e → B ≤ normalizer (T : Set G)

structure Hyp53 (ρ : Representation (ZMod 2) G V) (p : ℕ) (P T B : Subgroup G) : Prop where
  faithful : Function.Injective ρ
  irreducible : ρ.IsIrreducible
  sylow : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤
  centralizesZ : fixSub ρ T ≤ fixSub ρ B
  normal : P.Normal
  rank : 1 < CFSG.Open.pRank p P
  minimal : ∀ Q : Subgroup G, Q ≤ P → Q.Normal → 1 < CFSG.Open.pRank p Q → Q = P

@[expose] def sOf (T B A : Subgroup G) : Subgroup G := ⁅pCoreOf 2 (B ⊔ T), A⁆

@[expose] def alphaSet (G : Type) [Group G] [Finite G] : Set ℕ :=
  {q | q.Prime ∧ 1 < CFSG.Open.pRank q (pCoreOf q (⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆))}

@[expose] def calQ (q : ℕ) : Set (Subgroup G) :=
  {Q | Q.Normal ∧ ¬ IsCyclic Q ∧ IsPGroup q Q ∧ (∀ x ∈ Q, x ^ q = 1) ∧ ⁅⁅Q, Q⁆, Q⁆ = ⊥ ∧
    Q ≤ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆}

structure Hyp515 (B : Subgroup G) : Prop where
  cyclic : ∀ q ∈ alphaSet G, ∀ Q ∈ calQ (G := G) q, ∀ b ∈ B, b ≠ 1 →
    IsCyclic ↥(Q ⊓ centralizer ({b} : Set G))
  components : ∀ L : Subgroup G, IsComponentOf L ⊤ → numConj L ≤ 2

@[expose] def K516 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) G V) (p : ℕ) (P T B : Subgroup G) (e : ℕ),
    Hyp51 p P T B e → Hyp53 ρ p P T B → Hyp515 B →
      e + 1 < mGV ρ ∨
      (∃ q ∈ alphaSet G, q ∣ Nat.card B ∧ ∃ Q ∈ calQ (G := G) q, 3 < CFSG.Open.pRank q Q) ∨
      (P ⊓ centralizer (B : Set G) ≠ ⊥ ∧ 3 < CFSG.Open.pRank p P ∧ ¬ InvertedIn ⊤ B)

end CFSG.LocalAnalysis.UniquenessCase.UC22.F05
