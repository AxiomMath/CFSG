module

public import CFSG.GroupTheory.CentralCyclicDerived
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin.AppendixH.H12

variable {Y S : Type*} [Group Y] [Group S]

theorem ker_le_of_isCoatom_of_perfect [Finite Y] (hperf : Group.IsPerfect Y) {Z X : Subgroup Y}
    (hZ : Z ≤ Subgroup.center Y) (hX : IsCoatom X) : Z ≤ X := by
  haveI : Group.IsPerfect Y := hperf
  by_contra hle
  have hlt : X < X ⊔ Z := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro heq
    apply hle
    intro z hz
    have hz' : z ∈ X ⊔ Z := Subgroup.mem_sup_right hz
    rwa [← heq] at hz'
  have htop : X ⊔ Z = ⊤ := hX.lt_iff.mp hlt
  haveI : Z.Normal := Subgroup.normal_of_le_center hZ
  have hproduct : ∀ x ∈ X ⊔ Z, ∃ e ∈ X, ∃ i ∈ Z, e * i = x :=
    fun x hx => Subgroup.mem_sup_of_normal_right.mp hx
  have hcentral : ∀ e ∈ X, ∀ i ∈ Z, Commute e i :=
    fun e _ i hi => Subgroup.mem_center_iff.mp (hZ hi) e
  have habelian : ∀ i ∈ Z, ∀ j ∈ Z, Commute i j :=
    fun i hi j hj => (Subgroup.mem_center_iff.mp (hZ hi) j).symm
  have hder := CFSG.derived_sup_of_central_factor X Z hcentral habelian hproduct
  rw [htop] at hder
  have h1 : (⊤ : Subgroup Y) = ⁅X, X⁆ := by
    calc (⊤ : Subgroup Y) = ⁅⊤, ⊤⁆ := (Group.IsPerfect.commutator_eq_top).symm
      _ = ⁅X, X⁆ := hder
  exact hX.ne_top (top_le_iff.mp (h1.trans_le (Subgroup.commutator_le_self X)))

theorem isCoatom_comap_of_surjective (π : Y →* S) (hπ : Function.Surjective π) {A : Subgroup S}
    (hA : IsCoatom A) : IsCoatom (A.comap π) :=
  Subgroup.isCoatom_comap_of_surjective hπ hA

theorem card_eq_card_ker_mul_card_map [Finite Y] (π : Y →* S) {X : Subgroup Y} (hX : π.ker ≤ X) :
    Nat.card X = Nat.card π.ker * Nat.card (X.map π) := by
  let φ : ↥X →* S := π.comp X.subtype
  have h1 := Subgroup.card_ker_mul_card_range φ
  have hφk : φ.ker = π.ker.subgroupOf X := by
    ext x
    simp [φ, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have hφr : φ.range = X.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hφk, hφr] at h1
  have hc : Nat.card ↥(π.ker.subgroupOf X) = Nat.card ↥π.ker := by
    rw [← Subgroup.card_map_of_injective X.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hX]
  rw [hc] at h1
  exact h1.symm

theorem maximal_overgroups_of_central_cover [Finite Y] (π : Y →* S) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center Y) (hperf : Group.IsPerfect Y) {T : Subgroup Y}
    {A B : Subgroup S} (hTA : T.map π ≤ A) (hTB : T.map π ≤ B) (hA : A ≠ ⊤) (hB : B ≠ ⊤)
    (hAB : ¬ A ≤ B) (hBA : ¬ B ≤ A)
    (hlat : ∀ W : Subgroup S, T.map π ≤ W → W = ⊤ ∨ W ≤ A ∨ W ≤ B)
    (hAcard : ∀ W : Subgroup S, T.map π ≤ W → Nat.card W = Nat.card A → W = A)
    (hBcard : ∀ W : Subgroup S, T.map π ≤ W → Nat.card W = Nat.card B → W = B) :
    T ≤ A.comap π ∧ T ≤ B.comap π ∧ IsCoatom (A.comap π) ∧ IsCoatom (B.comap π) ∧
      A.comap π ≠ B.comap π ∧
      Nat.card (A.comap π) = Nat.card π.ker * Nat.card A ∧
      Nat.card (B.comap π) = Nat.card π.ker * Nat.card B ∧
      (∀ X : Subgroup Y, IsCoatom X → T ≤ X → X = A.comap π ∨ X = B.comap π) ∧
      (∀ X : Subgroup Y, T ≤ X → π.ker ≤ X → Nat.card X = Nat.card π.ker * Nat.card A →
        X = A.comap π) ∧
      (∀ X : Subgroup Y, T ≤ X → π.ker ≤ X → Nat.card X = Nat.card π.ker * Nat.card B →
        X = B.comap π) := by
  have hTA' : T ≤ A.comap π := Subgroup.map_le_iff_le_comap.mp hTA
  have hTB' : T ≤ B.comap π := Subgroup.map_le_iff_le_comap.mp hTB
  have hKA' : π.ker ≤ A.comap π := MonoidHom.ker_le_comap π A
  have hKB' : π.ker ≤ B.comap π := MonoidHom.ker_le_comap π B
  have hAc : IsCoatom A := by
    refine ⟨hA, fun W hW => ?_⟩
    rcases hlat W (le_trans hTA hW.le) with h | h | h
    · exact h
    · exact absurd hW (not_lt_of_ge h)
    · exact absurd (le_trans hW.le h) hAB
  have hBc : IsCoatom B := by
    refine ⟨hB, fun W hW => ?_⟩
    rcases hlat W (le_trans hTB hW.le) with h | h | h
    · exact h
    · exact absurd (le_trans hW.le h) hBA
    · exact absurd hW (not_lt_of_ge h)
  have hA'top : A.comap π ≠ ⊤ := by
    intro h
    apply hA
    have hm := congrArg (Subgroup.map π) h
    rwa [Subgroup.map_comap_eq_self_of_surjective hπ A, Subgroup.map_top_of_surjective π hπ] at hm
  have hB'top : B.comap π ≠ ⊤ := by
    intro h
    apply hB
    have hm := congrArg (Subgroup.map π) h
    rwa [Subgroup.map_comap_eq_self_of_surjective hπ B, Subgroup.map_top_of_surjective π hπ] at hm
  have hA'c : IsCoatom (A.comap π) := isCoatom_comap_of_surjective π hπ hAc
  have hB'c : IsCoatom (B.comap π) := isCoatom_comap_of_surjective π hπ hBc
  have hA'neB' : A.comap π ≠ B.comap π := by
    intro h
    exact hAB (le_of_eq (Subgroup.comap_injective hπ h))
  have hcardA' : Nat.card (A.comap π) = Nat.card π.ker * Nat.card A := by
    rw [card_eq_card_ker_mul_card_map π hKA', Subgroup.map_comap_eq_self_of_surjective hπ A]
  have hcardB' : Nat.card (B.comap π) = Nat.card π.ker * Nat.card B := by
    rw [card_eq_card_ker_mul_card_map π hKB', Subgroup.map_comap_eq_self_of_surjective hπ B]
  have hpos : 0 < Nat.card π.ker := by
    haveI : Nonempty ↥π.ker := ⟨1, (π.ker).one_mem⟩
    exact Nat.card_pos
  have hclause1 : ∀ X : Subgroup Y, IsCoatom X → T ≤ X → X = A.comap π ∨ X = B.comap π := by
    intro X hX hTX
    have hKX : π.ker ≤ X := ker_le_of_isCoatom_of_perfect hperf hker hX
    have hmaple : T.map π ≤ X.map π := Subgroup.map_mono hTX
    rcases hlat (X.map π) hmaple with h | h | h
    · exact absurd (by rw [← Subgroup.comap_map_eq_self hKX, h, Subgroup.comap_top]) hX.ne_top
    · exact Or.inl ((hX.le_iff.mp ((Subgroup.le_comap_map π X).trans
        (Subgroup.comap_mono h))).resolve_left hA'top).symm
    · exact Or.inr ((hX.le_iff.mp ((Subgroup.le_comap_map π X).trans
        (Subgroup.comap_mono h))).resolve_left hB'top).symm
  have hclause2 : ∀ X : Subgroup Y, T ≤ X → π.ker ≤ X →
      Nat.card X = Nat.card π.ker * Nat.card A → X = A.comap π := by
    intro X hTX hKX hcard
    have hmaple : T.map π ≤ X.map π := Subgroup.map_mono hTX
    have hcX : Nat.card X = Nat.card π.ker * Nat.card (X.map π) := card_eq_card_ker_mul_card_map π hKX
    have hcardmap : Nat.card (X.map π) = Nat.card A :=
      Nat.eq_of_mul_eq_mul_left hpos (by rw [← hcX, hcard])
    rw [← Subgroup.comap_map_eq_self hKX, hAcard (X.map π) hmaple hcardmap]
  have hclause3 : ∀ X : Subgroup Y, T ≤ X → π.ker ≤ X →
      Nat.card X = Nat.card π.ker * Nat.card B → X = B.comap π := by
    intro X hTX hKX hcard
    have hmaple : T.map π ≤ X.map π := Subgroup.map_mono hTX
    have hcX : Nat.card X = Nat.card π.ker * Nat.card (X.map π) := card_eq_card_ker_mul_card_map π hKX
    have hcardmap : Nat.card (X.map π) = Nat.card B :=
      Nat.eq_of_mul_eq_mul_left hpos (by rw [← hcX, hcard])
    rw [← Subgroup.comap_map_eq_self hKX, hBcard (X.map π) hmaple hcardmap]
  exact ⟨hTA', hTB', hA'c, hB'c, hA'neB', hcardA', hcardB', hclause1, hclause2, hclause3⟩

end CFSG.Quasithin.AppendixH.H12
