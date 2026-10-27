module

public import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Finite fiber counts for Bender's involution argument

This module isolates the finite combinatorics behind Bender's Case-2 coset
count.  A distinguished fiber has size nine, every other fiber has size at
most two, and twelve ordered pairs of distinct elements lie in common
non-base fibers.  Consequently exactly six non-base fibers have size two;
the remaining occupied non-base fibers are singletons.
-/

namespace CFSG.GorensteinWalter

universe u v

private abbrev fiber
    {Ω : Type u} {α : Type v} (π : α → Ω) (ω : Ω) :=
  {a : α // π a = ω}

private abbrev offDiagFiber
    {Ω : Type u} {α : Type v} (π : α → Ω) (ω : Ω) :=
  {p : fiber π ω × fiber π ω // p.1 ≠ p.2}

private theorem offDiagFiber_card
    {Ω : Type u} {α : Type v} [Finite Ω] [Finite α]
    (π : α → Ω) (ω : Ω) :
    Nat.card (offDiagFiber π ω) =
      Nat.card (fiber π ω) * (Nat.card (fiber π ω) - 1) := by
  classical
  letI : Fintype (fiber π ω) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  let e : offDiagFiber π ω ≃
      Σ x : fiber π ω, {y : fiber π ω // y ≠ x} :=
    { toFun := fun p => ⟨p.1.1, ⟨p.1.2, p.2.symm⟩⟩
      invFun := fun p => ⟨(p.1, p.2.1), p.2.2.symm⟩
      left_inv := by intro p; rfl
      right_inv := by intro p; rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp

/-- Suppose `π : α → Ω` has a distinguished fiber of cardinality nine,
all other fibers have cardinality at most two, and the total cardinality of
ordered pairs of distinct elements in a common non-base fiber is twelve.
Then, for some number `singleCosets`, the base fiber, singleton fibers, and
six double fibers occupy at most all of `Ω`, while their elements partition
`α` with cardinality `9 + singleCosets + 6 + 6`. -/
public theorem bender_coset_fiber_counts
    {Ω : Type u} {α : Type v} [Finite Ω] [Finite α]
    (π : α → Ω) (ω0 : Ω)
    (hbase : Nat.card {a : α // π a = ω0} = 9)
    (hbound : ∀ ω : Ω, ω ≠ ω0 →
      Nat.card {a : α // π a = ω} ≤ 2)
    (hpairs :
      Nat.card
        (Σ ω : {ω : Ω // ω ≠ ω0},
          {p : {a : α // π a = (ω : Ω)} ×
              {a : α // π a = (ω : Ω)} // p.1 ≠ p.2}) = 12) :
    ∃ singleCosets : ℕ,
      1 + singleCosets + 6 ≤ Nat.card Ω ∧
        Nat.card α = 9 + singleCosets + 6 + 6 := by
  classical
  letI : Fintype Ω := Fintype.ofFinite Ω
  letI : Fintype α := Fintype.ofFinite α
  let Nonbase := {ω : Ω // ω ≠ ω0}
  letI : Fintype Nonbase := Fintype.ofFinite Nonbase
  let n : Nonbase → ℕ := fun ω => Nat.card (fiber π (ω : Ω))
  let Single := {ω : Nonbase // n ω = 1}
  let Double := {ω : Nonbase // n ω = 2}
  letI : Fintype Single := Fintype.ofFinite Single
  letI : Fintype Double := Fintype.ofFinite Double
  let PairSigma := Σ ω : Nonbase, offDiagFiber π (ω : Ω)
  have hpairsSum :
      (∑ ω : Nonbase, n ω * (n ω - 1)) = 12 := by
    calc
      (∑ ω : Nonbase, n ω * (n ω - 1)) =
          ∑ ω : Nonbase, Nat.card (offDiagFiber π (ω : Ω)) := by
        apply Finset.sum_congr rfl
        intro ω _hω
        exact (offDiagFiber_card π (ω : Ω)).symm
      _ = Nat.card PairSigma := Nat.card_sigma.symm
      _ = 12 := by simpa [PairSigma, Nonbase] using hpairs
  have hnle (ω : Nonbase) : n ω ≤ 2 :=
    hbound (ω : Ω) ω.2
  have hterm (ω : Nonbase) :
      n ω * (n ω - 1) = if n ω = 2 then 2 else 0 := by
    have := hnle ω
    by_cases htwo : n ω = 2
    · simp [htwo]
    · simp [htwo]
      omega
  have hdouble : Nat.card Double = 6 := by
    have hsum :
        (∑ ω : Nonbase, if n ω = 2 then 2 else 0) = 12 := by
      simpa only [hterm] using hpairsSum
    have hsumCard :
        (∑ ω : Nonbase, if n ω = 2 then 2 else 0) =
          2 * Nat.card Double := by
      rw [Nat.card_eq_fintype_card]
      calc
        (∑ ω : Nonbase, if n ω = 2 then 2 else 0) =
            2 * (∑ ω : Nonbase, if n ω = 2 then 1 else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro ω _hω
          by_cases htwo : n ω = 2 <;> simp [htwo]
        _ = 2 *
            (Finset.univ.filter fun ω : Nonbase => n ω = 2).card := by
          rw [Finset.sum_boole]
          simp
        _ = 2 * Fintype.card Double := by
          rw [Fintype.card_subtype]
    omega
  let toOmega : Unit ⊕ (Single ⊕ Double) → Ω
    | Sum.inl _ => ω0
    | Sum.inr (Sum.inl ω) => (ω.1 : Ω)
    | Sum.inr (Sum.inr ω) => (ω.1 : Ω)
  have htoOmega : Function.Injective toOmega := by
    intro x y hxy
    rcases x with x | x
    · rcases y with y | y
      · exact congrArg Sum.inl (Subsingleton.elim x y)
      · rcases y with y | y
        · exact False.elim (y.1.2 hxy.symm)
        · exact False.elim (y.1.2 hxy.symm)
    · rcases y with y | y
      · rcases x with x | x
        · exact False.elim (x.1.2 hxy)
        · exact False.elim (x.1.2 hxy)
      · rcases x with x | x
        · rcases y with y | y
          · apply congrArg (fun z : Single => Sum.inr (Sum.inl z))
            apply Subtype.ext
            apply Subtype.ext
            exact hxy
          · exfalso
            have hcardEq : n x.1 = n y.1 := by
              congr 1
              apply Subtype.ext
              exact hxy
            rw [x.2, y.2] at hcardEq
            omega
        · rcases y with y | y
          · exfalso
            have hcardEq : n x.1 = n y.1 := by
              congr 1
              apply Subtype.ext
              exact hxy
            rw [x.2, y.2] at hcardEq
            omega
          · apply congrArg (fun z : Double => Sum.inr (Sum.inr z))
            apply Subtype.ext
            apply Subtype.ext
            exact hxy
  have hoccupied : 1 + Nat.card Single + Nat.card Double ≤ Nat.card Ω := by
    have hcard := Nat.card_le_card_of_injective toOmega htoOmega
    simpa [Nat.card_eq_fintype_card, Nat.card_sum, Nat.card_unique,
      add_assoc] using hcard
  let eAll : α ≃ Σ ω : Ω, fiber π ω :=
    { toFun := fun a => ⟨π a, ⟨a, rfl⟩⟩
      invFun := fun p => p.2.1
      left_inv := by intro a; rfl
      right_inv := by
        rintro ⟨ω, ⟨a, ha⟩⟩
        subst ω
        rfl }
  have htotal : Nat.card α = ∑ ω : Ω, Nat.card (fiber π ω) := by
    calc
      Nat.card α = Nat.card (Σ ω : Ω, fiber π ω) := Nat.card_congr eAll
      _ = ∑ ω : Ω, Nat.card (fiber π ω) := Nat.card_sigma
  have hsplit :
      (∑ ω : Ω, Nat.card (fiber π ω)) =
        Nat.card (fiber π ω0) + ∑ ω : Nonbase, n ω := by
    let s : Finset Ω := Finset.univ.erase ω0
    letI : Fintype {ω : Ω // ω ≠ ω0} := Fintype.ofFinite _
    have hsMem : ∀ ω : Ω, ω ∈ s ↔ ω ≠ ω0 := by
      intro ω
      simp [s]
    have hsSub := Finset.sum_subtype (F := inferInstance) s hsMem
      (fun ω : Ω => Nat.card (fiber π ω))
    have hErase := Finset.sum_erase_add Finset.univ
      (fun ω : Ω => Nat.card (fiber π ω)) (Finset.mem_univ ω0)
    calc
      (∑ ω : Ω, Nat.card (fiber π ω)) =
          (∑ ω ∈ s, Nat.card (fiber π ω)) +
            Nat.card (fiber π ω0) := by
        simpa [s] using hErase.symm
      _ = (∑ ω : {ω : Ω // ω ≠ ω0},
          Nat.card (fiber π (ω : Ω))) + Nat.card (fiber π ω0) := by
        rw [hsSub]
      _ = Nat.card (fiber π ω0) + ∑ ω : Nonbase, n ω := by
        rw [add_comm]
  have hnRewrite (ω : Nonbase) :
      n ω = (if n ω = 1 then 1 else 0) +
        (if n ω = 2 then 2 else 0) := by
    have := hnle ω
    by_cases hone : n ω = 1
    · simp [hone]
    · by_cases htwo : n ω = 2
      · simp [htwo]
      · simp [hone, htwo]
        omega
  have hsingleSum :
      (∑ ω : Nonbase, if n ω = 1 then 1 else 0) = Nat.card Single := by
    rw [Nat.card_eq_fintype_card]
    calc
      (∑ ω : Nonbase, if n ω = 1 then 1 else 0) =
          (Finset.univ.filter fun ω : Nonbase => n ω = 1).card := by simp
      _ = Fintype.card Single := (Fintype.card_subtype _).symm
  have hdoubleSum :
      (∑ ω : Nonbase, if n ω = 2 then 2 else 0) =
        2 * Nat.card Double := by
    rw [Nat.card_eq_fintype_card]
    calc
      (∑ ω : Nonbase, if n ω = 2 then 2 else 0) =
          2 * (∑ ω : Nonbase, if n ω = 2 then 1 else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ω _hω
        by_cases htwo : n ω = 2 <;> simp [htwo]
      _ = 2 * (Finset.univ.filter fun ω : Nonbase => n ω = 2).card := by
        rw [Finset.sum_boole]
        simp
      _ = 2 * Fintype.card Double := by rw [Fintype.card_subtype]
  have hnonbase :
      (∑ ω : Nonbase, n ω) = Nat.card Single + 2 * Nat.card Double := by
    calc
      (∑ ω : Nonbase, n ω) =
          ∑ ω : Nonbase,
            ((if n ω = 1 then 1 else 0) +
              (if n ω = 2 then 2 else 0)) := by
        apply Finset.sum_congr rfl
        intro ω _hω
        exact hnRewrite ω
      _ = (∑ ω : Nonbase, if n ω = 1 then 1 else 0) +
          (∑ ω : Nonbase, if n ω = 2 then 2 else 0) :=
        Finset.sum_add_distrib
      _ = Nat.card Single + 2 * Nat.card Double := by
        rw [hsingleSum, hdoubleSum]
  refine ⟨Nat.card Single, ?_, ?_⟩
  · rw [hdouble] at hoccupied
    exact hoccupied
  · rw [htotal, hsplit, hbase, hnonbase, hdouble]
    omega

end CFSG.GorensteinWalter
