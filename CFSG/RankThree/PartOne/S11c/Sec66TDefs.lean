module

public import CFSG.Blueprint.Catalog
public import CFSG.Foundations.Basic

public section

namespace CFSG.RankThree.PartOne.Sec66T

open CFSG CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

variable {T : Type} [Group T]

@[expose] def fixSub (α : MulAut T) : Subgroup T :=
  MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id T)

theorem mem_fixSub {α : MulAut T} {x : T} : x ∈ fixSub α ↔ α x = x := Iff.rfl

@[expose] def innerAut (T : Type) [Group T] : Subgroup (MulAut T) :=
  (MulAut.conj : T →* MulAut T).range

@[expose] noncomputable def fixRes (α : MulAut T) : Subgroup T :=
  inSubgroup perfectResidual (fixSub α)

@[expose] def FieldAutT (p : ℕ) (α : MulAut T) : Prop :=
  ∃ (t : StatedLieTag) (n f : ℕ), 1 ≤ f ∧ LieModel T t n 2 (p * f) ∧
    (LieModel (↥(fixRes α) ⧸ Subgroup.center ↥(fixRes α)) t n 2 f ∨
      (t = .twistedF4 ∧ n = 0 ∧ f = 1 ∧
        LieModel (↥(fixRes α) ⧸ Subgroup.center ↥(fixRes α)) .Tits 0 2 1))

@[expose] def LocalRankLeTwo (p : ℕ) (T : Type) [Group T] : Prop :=
  ∀ R : Subgroup T, IsElementaryAbelian p ↥R → Nat.card R = p ^ 3 →
    ∀ U : Subgroup T, U ≠ ⊥ → IsPGroup 2 ↥U → ¬ R ≤ Subgroup.normalizer (U : Set T)

@[expose] def LocalRankAut (p : ℕ) (T : Type) [Group T] (α : MulAut T) : Prop :=
  α ^ p = 1 → α ∉ innerAut T →
    ∀ R : Subgroup T, IsElementaryAbelian p ↥R → Nat.card R = p ^ 2 → (∀ r ∈ R, α r = r) →
      ∀ U : Subgroup T, U ≠ ⊥ → IsPGroup 2 ↥U → (∀ u ∈ U, α u ∈ U) →
        ¬ R ≤ Subgroup.normalizer (U : Set T)

@[expose] def Sec66T_K1 (t : StatedLieTag) : Prop :=
  ∀ (T : Type) [Group T] [Finite T] (p : ℕ), p.Prime → 5 ≤ p →
    (∃ n f : ℕ, StatedLieAdmissible t n 2 f ∧ LieModel T t n 2 f) → LocalRankLeTwo p T →
    ∀ (α : MulAut T) (q : T) (U : Subgroup T), orderOf α = p → α ∉ innerAut T → q ≠ 1 →
      q ^ p = 1 → α q = q → U ≠ ⊥ → IsPGroup 2 ↥U → (∀ u ∈ U, α u ∈ U) →
      (∀ u ∈ U, q * u * q⁻¹ ∈ U) → (∃ u ∈ U, α u ≠ u ∨ q * u * q⁻¹ ≠ u) →
      LocalRankAut p T α → FieldAutT p α

@[expose] def Sec66T_K2 (t : StatedLieTag) : Prop :=
  ∀ (T : Type) [Group T] [Finite T] (p : ℕ), p.Prime → 5 ≤ p →
    (∃ n f : ℕ, StatedLieAdmissible t n 2 f ∧ LieModel T t n 2 f) → LocalRankLeTwo p T →
    ∀ E : Subgroup (MulAut T), IsElementaryAbelian p ↥E → Nat.card E = p ^ 2 →
      E ⊓ innerAut T = ⊥ → (∀ α ∈ E, LocalRankAut p T α) → False

@[expose] def PlaneT (p : ℕ) (T : Type) [Group T] [Finite T] : Prop :=
  LocalRankLeTwo p T → ∀ E : Subgroup (MulAut T), IsElementaryAbelian p ↥E → Nat.card E = p ^ 2 →
    E ⊓ innerAut T = ⊥ → (∀ α ∈ E, LocalRankAut p T α) → False

end CFSG.RankThree.PartOne.Sec66T
