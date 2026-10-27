module

public import CFSG.Sporadic.HeldB.OuterCent
public import CFSG.LocalAnalysis.ComponentInitial.ConjClassSimplicity

public noncomputable section

namespace CFSG.Sporadic.HeldB

open CFSG.LocalAnalysis.ComponentInitial

theorem heOuterQuot_simple :
    IsSimpleGroup (heOuterD ⧸ Subgroup.center heOuterD) := by
  obtain ⟨e, he⟩ := heOuterQuot_classes
  set G := heOuterD ⧸ Subgroup.center heOuterD
  have hcard : Nat.card G = 2520 := card_heOuterD_quot
  have h0 : e 0 = ConjClasses.mk 1 := by
    obtain ⟨i, hi⟩ := e.surjective (ConjClasses.mk 1)
    have h1 : (e i).carrier.ncard = 1 := by
      rw [hi, ConjClasses.carrier_eq_preimage_mk]
      have : ConjClasses.mk ⁻¹' {ConjClasses.mk (1 : G)} = {1} := by
        ext x
        simp [ConjClasses.mk_eq_mk_iff_isConj]
      rw [this, Set.ncard_singleton]
    rw [he] at h1
    have key : ∀ j : Fin 9, heOuterClassSizes j = 1 → j = 0 := by decide
    rw [← key i h1, hi]
  have hC : ∀ c : ConjClasses G, c ∈ Set.range (fun i : Fin 8 => e i.succ) ↔
      c ≠ ConjClasses.mk 1 := by
    intro c
    constructor
    · rintro ⟨j, rfl⟩ h
      rw [← h0] at h
      exact Fin.succ_ne_zero j (e.injective h)
    · intro hc
      obtain ⟨i, rfl⟩ := e.surjective c
      have hi : i ≠ 0 := by
        rintro rfl
        exact hc h0
      obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 hi
      exact ⟨j, rfl⟩
  refine (conjugacy_class_divisor_simplicity (by rw [hcard]; norm_num) (fun i : Fin 8 => e i.succ)
    (fun i j h => Fin.succ_injective _ (e.injective h)) hC fun I hI => ?_).2
  simp only [he] at hI ⊢
  rw [hcard] at hI ⊢
  exact heOuterClass_divisors I hI

theorem heOuterQuot_nonabelian :
    ∃ a b : heOuterD ⧸ Subgroup.center heOuterD, a * b ≠ b * a := by
  by_contra h
  have h' : ∀ a b : heOuterD ⧸ Subgroup.center heOuterD, a * b = b * a := fun a b =>
    by_contra fun hne => h ⟨a, b, hne⟩
  have : IsMulCommutative (heOuterD ⧸ Subgroup.center heOuterD) := ⟨⟨h'⟩⟩
  have hp := (Group.is_simple_iff_prime_card.1 heOuterQuot_simple)
  rw [card_heOuterD_quot] at hp
  exact absurd hp (by norm_num)

theorem ctbh_outer_centralizer_derived_quasisimple :
    heOuterD = ⁅heOuterC, heOuterC⁆ ∧ CFSG.IsQuasisimple heOuterD ∧
      heOuterD.relIndex heOuterC = 2 :=
  ⟨heOuterD_eq_commutator,
    ⟨Subgroup.isPerfect_iff.2 heOuterD_perfect, heOuterQuot_simple, heOuterQuot_nonabelian⟩,
    heOuterD_relIndex⟩

end CFSG.Sporadic.HeldB
