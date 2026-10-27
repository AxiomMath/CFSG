module

public import CFSG.ThirdParty.BrauerInduction.Elementary.Span
public import CFSG.ThirdParty.BrauerInduction.Cyclotomic.IntegralCharacterRing
public import CFSG.ThirdParty.BrauerInduction.Elementary.LocalFunction
public import CFSG.ThirdParty.BrauerInduction.Background.Group.PRegularClass

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# Fixed-prime local sums

For a prime `p`, this file defines the sum of the local functions
`PElementary.f p C.repr`, with one summand for each `p`-regular conjugacy
class `C`.

On a `p`-regular element, exactly one summand is nonzero, and the resulting
value is an integer not divisible by `p`.

The extension of this nondivisibility result to arbitrary elements is proved
in `BrauerInduction.Bernstein.PrimeToP` using the fixed-coset evaluation.
-/

universe u v

open scoped BigOperators

namespace CFSG.BrauerInduction
namespace PElementary

variable {k : Type u} [Field k]
variable {G : Type u} [Group G]
variable (p : ℕ) [Fact p.Prime]

/--
The sum of the fixed-prime local functions over the `p`-regular conjugacy
classes of `G`.
-/
@[expose] noncomputable def localSum [Finite G] :
    ClassFun k G := by
  letI : Fintype G := Fintype.ofFinite G
  exact
    ∑ C : PRegularClass p G,
      PElementary.f (k := k) p C.repr


/--
A local function belongs to the cyclotomic fixed-`p` elementary span.
-/
lemma localFunction_mem_PElementarySpanLambda
    [Finite G] [CharZero k] [IsAlgClosed k]
    (a : G) (ha : IsPRegular p a) :
    PElementary.f (k := k) p a ∈
      PElementarySpanLambda (k := k) (G := G) p := by
  simpa [PElementary.f] using
    PElementarySpanLambda.ind_mem
      (k := k) (G := G) p
      (PElementary.E_subgroup p a)
      (PElementary.E_isPElementary p ha)
      (PElementary.phi_mem_Q (k := k) p a ha).1

/--
A local function is integer-valued.
-/
lemma localFunction_mem_C_Z
    [Finite G] [CharZero k] [IsAlgClosed k]
    (a : G) (ha : IsPRegular p a) :
    PElementary.f (k := k) p a ∈ ClassFun.C_Z k G := by
  intro g

  have htop :=
    ClassFun.C_Z.ind_mem_C_Z
      (k := k) (G := G)
      (PElementary.phi_mem_Q (k := k) p a ha).2

  simpa [PElementary.f] using
    htop ⟨g, Subgroup.mem_top g⟩


private lemma finset_sum_mem_C_Z
    {ι : Type*}
    (s : Finset ι)
    (F : ι → ClassFun k G)
    (hF : ∀ i ∈ s, F i ∈ ClassFun.C_Z k G) :
    s.sum F ∈ ClassFun.C_Z k G := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using
        (ClassFun.C_Z.zero_mem (k := k) (G := G))

  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      apply ClassFun.C_Z.add_mem
      · exact hF a (Finset.mem_insert_self a s)
      · apply ih
        intro i hi
        exact hF i (Finset.mem_insert_of_mem hi)

/--
The fixed-prime local sum belongs to the cyclotomic `p`-elementary span.
-/
lemma localSum_mem_PElementarySpanLambda
    [Finite G] [CharZero k] [IsAlgClosed k] :
    localSum (k := k) p ∈
      PElementarySpanLambda (k := k) (G := G) p := by
  unfold localSum
  apply Submodule.sum_mem
  intro C hC
  exact localFunction_mem_PElementarySpanLambda
    (k := k) p C.repr (PRegularClass.repr_isPRegular C)

/--
The fixed-prime local sum is integer-valued.
-/
lemma localSum_mem_C_Z
    [Finite G] [CharZero k] [IsAlgClosed k] :
    localSum (k := k) p ∈ ClassFun.C_Z k G := by
  classical
  unfold localSum
  apply finset_sum_mem_C_Z
  intro C hC
  exact localFunction_mem_C_Z
    (k := k) p C.repr
      (PRegularClass.repr_isPRegular C)

open Classical in
/--
On a `p`-regular element, the local sum equals the index attached to the
unique `p`-regular conjugacy class containing that element.
-/
lemma localFunction_apply_pRegular
    [Finite G] [CharZero k]
    (C : PRegularClass p G)
    (g : G) (hg : IsPRegular p g) :
    PElementary.f (k := k) p C.repr g =
      if IsConj C.repr g then
        (PElementary.index p C.repr : k)
      else
        0 := by
  by_cases hC : IsConj C.repr g

  · rw [if_pos hC]
    calc
      PElementary.f (k := k) p C.repr g
          =
        PElementary.f (k := k) p C.repr C.repr := by
          exact
            (PElementary.f (k := k) p C.repr).map_conj
              g C.repr hC.symm
      _ = (PElementary.index p C.repr : k) := by
          exact
            PElementary.f_apply_a_eq_index
              (k := k) p
              (PRegularClass.repr_isPRegular C)

  · rw [if_neg hC]
    apply PElementary.f_apply_eq_zero_of_not_isConj

    rw [Group.pRegular_eq_self_of_isPRegular
      (hf := isOfFinOrder_of_finite g)
      (hr := hg)]

    intro h
    exact hC h.symm

/--
On every `p`-regular element, the local sum has an integer value not
divisible by `p`.
-/
lemma localSum_apply_of_pRegular
    [Finite G] [CharZero k]
    (g : G) (hg : IsPRegular p g) :
    ∃ C : PRegularClass p G,
      IsConj C.repr g ∧
      localSum (k := k) p g =
        (PElementary.index p C.repr : k) := by
  classical

  rcases PRegularClass.unique_of_isPRegular p g hg with
    ⟨C₀, hC₀, hC_unique⟩

  refine ⟨C₀, hC₀, ?_⟩

  simp only [localSum, ClassFun.sum_apply]

  rw [Finset.sum_eq_single C₀]

  · rw [localFunction_apply_pRegular
      (k := k) p C₀ g hg]
    rw [if_pos hC₀]

  · intro C hC_mem hC_ne
    have h_not_conj : ¬ IsConj C.repr g := by
      intro hC
      exact hC_ne (hC_unique C hC)

    rw [localFunction_apply_pRegular
      (k := k) p C g hg]
    rw [if_neg h_not_conj]

  · intro hC₀_not_mem
    exact (hC₀_not_mem (Finset.mem_univ C₀)).elim


/--
On every `p`-regular element, the fixed-prime local sum has an integer value
not divisible by `p`.
-/
lemma localSum_apply_of_pRegular_not_dvd
    [Finite G] [CharZero k]
    (g : G) (hg : IsPRegular p g) :
    ∃ n : ℤ,
      localSum (k := k) p g = (n : k) ∧
      ¬ (p : ℤ) ∣ n := by
  rcases localSum_apply_of_pRegular
      (k := k) p g hg with
    ⟨C, hC, hsum⟩

  rcases PElementary.f_apply_self_coprime
      (k := k) p
      (PRegularClass.repr_isPRegular C) with
    ⟨n, hn, hn_not_dvd⟩

  refine ⟨n, ?_, hn_not_dvd⟩

  calc
    localSum (k := k) p g
        =
      (PElementary.index p C.repr : k) := hsum
    _ =
      PElementary.f (k := k) p C.repr C.repr := by
        symm
        exact
          PElementary.f_apply_a_eq_index
            (k := k) p
            (PRegularClass.repr_isPRegular C)
    _ = (n : k) := hn


section localSumElement

variable [CharZero k] [IsAlgClosed k]
variable [Finite G]

/--
The fixed-prime local sum, regarded as an integer-valued cyclotomic
character.
-/

@[expose] noncomputable def localSumElement :
    ClassFun.IntegralCyclotomicCharacterRing (k := k) (G := G) :=
  ⟨ ⟨ localSum (k := k) p,
      PElementarySpanLambda.le_R_Lambda_top p
        (localSum_mem_PElementarySpanLambda p)
    ⟩,
    PElementary.localSum_mem_C_Z p
  ⟩

@[simp]
lemma coe_localSumElement :
    (localSumElement (k := k) (G := G) p : ClassFun k G) =
        PElementary.localSum p :=
  rfl

end localSumElement

end PElementary
end CFSG.BrauerInduction
