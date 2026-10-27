module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.Quasithin.Dickson

open scoped commutatorElement

def dihedralSign (n : ℕ) : DihedralGroup n →* Multiplicative (ZMod 2) where
  toFun x := match x with
    | .r _ => 1
    | .sr _ => Multiplicative.ofAdd 1
  map_one' := rfl
  map_mul' := by
    rintro (a | a) (b | b)
    · simp [DihedralGroup.r_mul_r]
    · simp [DihedralGroup.r_mul_sr]
    · simp [DihedralGroup.sr_mul_r]
    · simp only [DihedralGroup.sr_mul_sr]
      rw [← ofAdd_add]
      rfl

theorem isSolvable_dihedral (n : ℕ) : Group.IsSolvable (DihedralGroup n) := by
  have hr : ∀ a : DihedralGroup n, dihedralSign n a = 1 → ∃ i, a = DihedralGroup.r i := by
    rintro (i | i) h
    · exact ⟨i, rfl⟩
    · exfalso
      have h1 : dihedralSign n (DihedralGroup.sr i) = Multiplicative.ofAdd (1 : ZMod 2) := rfl
      rw [h1] at h
      exact absurd (congrArg Multiplicative.toAdd h) (by decide)
  have hker : IsMulCommutative (dihedralSign n).ker := ⟨⟨fun a b => by
    obtain ⟨i, hi⟩ := hr a a.2
    obtain ⟨j, hj⟩ := hr b b.2
    apply Subtype.ext
    change (a : DihedralGroup n) * b = b * a
    rw [hi, hj, DihedralGroup.r_mul_r, DihedralGroup.r_mul_r, add_comm]⟩⟩
  have hquot : IsMulCommutative (DihedralGroup n ⧸ (dihedralSign n).ker) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
      (Abelianization.commutator_subset_ker _)
  exact Group.isSolvable_of_subgroup_quotient (dihedralSign n).ker

theorem sl2_three_perfect_eq_bot (K : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)))
    (hK : ⁅K, K⁆ = K) : K = ⊥ := by
  have hmul : ∀ a b : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3),
      a ^ 4 = 1 → b ^ 4 = 1 → (a * b) ^ 4 = 1 := by decide +kernel
  have hcomm : ∀ a b : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3), ⁅a, b⁆ ^ 4 = 1 := by
    decide +kernel
  let T : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) :=
    { carrier := {x | x ^ 4 = 1}
      mul_mem' := fun {a b} ha hb => hmul a b ha hb
      one_mem' := one_pow 4
      inv_mem' := fun {a} ha => by
        have : a ^ 4 = 1 := ha
        change a⁻¹ ^ 4 = 1
        rw [inv_pow, this, inv_one] }
  have hKT : K ≤ T := by
    rw [← hK]
    exact Subgroup.commutator_le.mpr fun a _ b _ => hcomm a b
  by_contra hne
  have : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).2 hne
  have hperf : Group.IsPerfect K := Subgroup.isPerfect_iff.mpr hK
  have hp : IsPGroup 2 K := fun x => ⟨2, Subtype.ext (hKT x.2)⟩
  have := hp.isNilpotent
  exact Group.IsPerfect.not_isNilpotent K ‹_›

end CFSG.Quasithin.Dickson
