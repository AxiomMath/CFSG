module

public import CFSG.RankThree.PartTwo.Sec4.Item47Witness

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Fix

variable {X Y : Type*} [Group X] [Group Y]

@[expose] def autFix (α : MulAut X) : Subgroup X where
  carrier := {x | α x = x}
  mul_mem' {x y} hx hy := by
    change α (x * y) = x * y
    rw [map_mul, hx, hy]
  one_mem' := map_one α
  inv_mem' {x} hx := by
    change α x⁻¹ = x⁻¹
    rw [map_inv, hx]

theorem mem_autFix {α : MulAut X} {x : X} : x ∈ autFix α ↔ α x = x :=
  Iff.rfl

theorem autFix_congr (e : X ≃* Y) (α : MulAut X) :
    autFix (MulAut.congr e α) = (autFix α).map e.toMonoidHom := by
  ext y
  constructor
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    change α (e.symm y) = e.symm y
    have hy' : e (α (e.symm y)) = y := hy
    exact e.injective (by rw [hy', MulEquiv.apply_symm_apply])
  · rintro ⟨x, hx, rfl⟩
    have hx' : α x = x := hx
    change e (α (e.symm (e x))) = e x
    rw [MulEquiv.symm_apply_apply, hx']

@[expose] noncomputable def autFixCongrEquiv (e : X ≃* Y) (α : MulAut X) :
    autFix (MulAut.congr e α) ≃* autFix α :=
  (MulEquiv.subgroupCongr (autFix_congr e α)).trans
    (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).symm

end Fix

section Bar

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem barCentralizer_zpowers_eq_autFix {a : G} (ha : a ∈ Subgroup.normalizer (L : Set G)) :
    Sec8.barCentralizer (Subgroup.zpowers a) L =
      autFix (thetaQuotMulAut L (compAction L ⟨a, ha⟩)) := by
  ext y
  rw [mem_barCentralizer_zpowers_iff ha, mem_autFix]

end Bar

@[expose] def IsStdGraphFieldConj {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (γ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    Prop :=
  ∃ β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
    γ = β * fieldActor σ σ * β⁻¹ ∨
      γ = β * (fieldActor σ σ)⁻¹ * β⁻¹

structure Inputs47 : Prop where
  outU4p : ∀ (p : ℕ) [Fact p.Prime], 3 < p → p % 3 = 1 → ¬ 3 ∣ Nat.card (Outer (projSU 4 p 1))
  outU54 : ¬ 3 ∣ Nat.card (Outer (projSU 5 2 2))
  outG23 : ∀ (X : Type) [Group X], Blueprint.ChevalleyExceptionalModel X .G2 3 1 →
    ¬ 3 ∣ Nat.card (Outer X)
  outU43 : ¬ 3 ∣ Nat.card (Outer (projSU 4 3 1))
  outTits : ∀ (X : Type) [Group X] (f : ℕ), Blueprint.ReeTitsModel X .Tits 2 f →
    ¬ 3 ∣ Nat.card (Outer X)
  outSporadic : ∀ s : TauCeti.SporadicName, s ∈ sporadics46 ∨ s ∈ sporadicCovers46 →
    ¬ 3 ∣ Nat.card (Outer (Blueprint.NativeSporadic.Carrier s))
  centerSporadic : ∀ s ∈ sporadicCovers46,
    Subgroup.center (Blueprint.NativeSporadic.Carrier s) = ⊥
  witnessG2 : ∀ (X : Type) [Group X] (k : ℕ), Blueprint.ChevalleyExceptionalModel X .G2 2 (2 * k) →
    ∀ α : MulAut X, α ^ 3 = 1 → ¬ IsInnerAut α → HasLocalWitness α
  witnessD4 : ∀ (X : Type) [Group X] (k : ℕ),
    Blueprint.ChevalleyExceptionalModel X .trialityD4 2 (2 * k) →
    ∀ α : MulAut X, α ^ 3 = 1 → ¬ IsInnerAut α → HasLocalWitness α
  witnessU4 : ∀ n : ℕ, 1 ≤ n → ∀ α : MulAut (projSU 4 2 n), α ^ 3 = 1 → ¬ IsInnerAut α →
    HasLocalWitness α
  classesD4 : ∀ n : ℕ, Odd n → ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K),
    Nat.card K = (2 ^ n) ^ 3 → (∀ c, σ c = c ^ 2 ^ n) →
    ∀ α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      α ^ 3 = 1 → ¬ IsInnerAut α →
        IsStdGraphFieldConj σ α ∨
          ∃ (γ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
            (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
            IsStdGraphFieldConj σ γ ∧ γ y = y ∧ orderOf y = 3 ∧ α = γ * MulAut.conj y ∧
              Sec8.IsoPGUThree (autFix α) (2 ^ n)
  reeLang : ∀ (a : ℕ) (K : Type) [Field K] [Finite K] [CharP K CFSG.LieType.Ree.ReeTag.F4.prime],
    1 ≤ a → Nat.card K = 2 ^ (2 * a + 1) → LargeReeOrderThreeFieldConj a K

structure Inputs47NoD4 :
    Prop where
  outU4p : ∀ (p : ℕ) [Fact p.Prime], 3 < p → p % 3 = 1 → ¬ 3 ∣ Nat.card (Outer (projSU 4 p 1))
  outU54 : ¬ 3 ∣ Nat.card (Outer (projSU 5 2 2))
  outG23 : ∀ (X : Type) [Group X], Blueprint.ChevalleyExceptionalModel X .G2 3 1 →
    ¬ 3 ∣ Nat.card (Outer X)
  outU43 : ¬ 3 ∣ Nat.card (Outer (projSU 4 3 1))
  outTits : ∀ (X : Type) [Group X] (f : ℕ), Blueprint.ReeTitsModel X .Tits 2 f →
    ¬ 3 ∣ Nat.card (Outer X)
  outSporadic : ∀ s : TauCeti.SporadicName, s ∈ sporadics46 ∨ s ∈ sporadicCovers46 →
    ¬ 3 ∣ Nat.card (Outer (Blueprint.NativeSporadic.Carrier s))
  centerSporadic : ∀ s ∈ sporadicCovers46,
    Subgroup.center (Blueprint.NativeSporadic.Carrier s) = ⊥
  witnessG2 : ∀ (X : Type) [Group X] (k : ℕ), Blueprint.ChevalleyExceptionalModel X .G2 2 (2 * k) →
    ∀ α : MulAut X, α ^ 3 = 1 → ¬ IsInnerAut α → HasLocalWitness α
  witnessU4 : ∀ n : ℕ, 1 ≤ n → ∀ α : MulAut (projSU 4 2 n), α ^ 3 = 1 → ¬ IsInnerAut α →
    HasLocalWitness α
  reeLang : ∀ (a : ℕ) (K : Type) [Field K] [Finite K] [CharP K CFSG.LieType.Ree.ReeTag.F4.prime],
    1 ≤ a → Nat.card K = 2 ^ (2 * a + 1) → LargeReeOrderThreeFieldConj a K

theorem Inputs47.toNoD4
    (h : Inputs47) :
    Inputs47NoD4 where
  outU4p := h.outU4p
  outU54 := h.outU54
  outG23 := h.outG23
  outU43 := h.outU43
  outTits := h.outTits
  outSporadic := h.outSporadic
  centerSporadic := h.centerSporadic
  witnessG2 := h.witnessG2
  witnessU4 := h.witnessU4
  reeLang := h.reeLang

end CFSG.RankThree.PartTwo.Sec4
