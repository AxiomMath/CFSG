module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329SplitRes
public import CFSG.Open.StatedDefs
public import CFSG.GroupTheory.LocalCores.Fitting

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open (StatedProj StatedScalars)

@[expose] def K329Ct {H : Type} [Group H] (Z : Subgroup H) [Z.Normal] (x : H) : Subgroup H :=
  (Subgroup.centralizer ({(QuotientGroup.mk x : H ⧸ Z)} : Set (H ⧸ Z))).comap
    (QuotientGroup.mk' Z)

@[expose] def K329CentralProduct {H : Type} [Group H] (L : Subgroup H) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (Lf : ι → Subgroup H),
    (∀ i, CFSG.Open.IsQuasisimple ↥(Lf i)) ∧ (∀ i j, i ≠ j → ⁅Lf i, Lf j⁆ = ⊥) ∧ ⨆ i, Lf i = L

@[expose] def K329Schur {H : Type} [Group H] (x : H) : Prop :=
  ∀ R : Subgroup H, R ≤ Subgroup.centralizer ({x} : Set H) → IsPGroup 3 R →
    ⁅R, K329Lres x⁆ = ⊥ → ∀ a ∈ R, ∀ b ∈ R, a * b = b * a

abbrev K329Zh {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (H : Subgroup (GL ι K)) : Subgroup H :=
  (StatedScalars ι K).subgroupOf H

theorem k329_Zh_le_center {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (H : Subgroup (GL ι K)) : K329Zh H ≤ Subgroup.center H := by
  intro a ha
  rw [Subgroup.mem_center_iff]
  intro b
  have ha' : (a : GL ι K) ∈ StatedScalars ι K := ha
  have hc : (a : GL ι K) ∈ Subgroup.center (GL ι K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ha'
  exact Subtype.ext (Subgroup.mem_center_iff.mp hc (b : GL ι K))

@[expose] def K329YMatrix {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (H : Subgroup (GL ι K)) (q : ℕ) : Prop :=
  ∀ x : H, x ∉ K329Zh H → x ^ 3 ∈ K329Zh H →
    (∃ Q : Subgroup H, Q ≤ K329Lres x ∧ (Q.subgroupOf (K329Lres x)).Normal ∧
      CFSG.Open.IsQuasisimple ↥Q ∧ Nat.card (↥Q ⧸ Subgroup.center ↥Q) = 504) → q = 8

@[expose] def K329CentralProductMatrix {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] (H : Subgroup (GL ι K)) : Prop :=
  ∀ x : H, x ∉ K329Zh H → x ^ 3 ∈ K329Zh H → K329CentralProduct (K329Lres x)

@[expose] def K329SchurMatrix {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] (H : Subgroup (GL ι K)) : Prop :=
  ∀ x : H, x ∉ K329Zh H → x ^ 3 ∈ K329Zh H → K329Schur x

@[expose] def K329TwistMatrix {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] (H : Subgroup (GL ι K)) (concl : Prop) : Prop :=
  ∀ x : H, x ∉ K329Zh H → x ^ 3 ∈ K329Zh H → ∀ g ∈ K329Ct (K329Zh H) x,
    (∀ l ∈ K329Lres x, g * l = l * g) → g ∉ Subgroup.centralizer ({x} : Set H) → concl

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
