module

public import CFSG.Models
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.ClassicalInvolution.SL2Facts
import TauCeti.RepresentationTheory.CharacterTable.Solvable

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Assembly.LowTwoRank

theorem exists_lieModel_psl_two_of_surjective {X : Type} [Group X] (hXs : IsSimpleGroup X)
    (hnab : ∃ a b : X, a * b ≠ b * a) {F : Type} [Field F] [Finite F] (h2 : (2 : F) ≠ 0)
    {φ : Matrix.SpecialLinearGroup (Fin 2) F →* X} (hφ : Function.Surjective φ) :
    ∃ p f : ℕ, p ≠ 2 ∧ CFSG.Models.LieModel X .PSL 2 p f := by
  classical
  have := hXs
  let _ : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hp, hcard⟩ := FiniteField.card F (ringChar F)
  have hp2 : ringChar F ≠ 2 := fun h => h2 (by
    have h0 : ((ringChar F : ℕ) : F) = 0 := ringChar.Nat.cast_ringChar
    rw [h] at h0
    exact_mod_cast h0)
  have hcardN : Nat.card F = ringChar F ^ (n : ℕ) := Nat.card_eq_fintype_card.trans hcard
  have hp3 : 3 ≤ ringChar F := by have := hp.two_le; omega
  have hq3 : 3 ≤ ringChar F ^ (n : ℕ) := hp3.trans (Nat.le_self_pow n.ne_zero _)
  have hXns : ¬ Group.IsSolvable X := fun h =>
    let ⟨a, b, hab⟩ := hnab
    hab ((IsSimpleGroup.comm_iff_isSolvable.mpr h) a b)
  have hq4 : 4 ≤ Nat.card F := by
    rw [hcardN]
    refine Nat.lt_of_le_of_ne hq3 fun h3 => hXns ?_
    have hF3 : Fintype.card F = 3 := by rw [hcard, ← h3]
    have h24 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 2 ^ 3 * 3 ^ 1 := by
      rw [Matrix.card_SL_field, hF3]
      decide
    have : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) F) :=
      TauCeti.isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two Nat.prime_three h24
    exact Group.isSolvable_of_surjective hφ
  have hZX : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hnab
      exact absurd ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a) hab
  have hZker : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) ≤ φ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker, ← Subgroup.mem_bot, ← hZX, Subgroup.mem_center_iff]
    intro x
    obtain ⟨y, rfl⟩ := hφ x
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
  have hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) F) ≠ 1 :=
    CFSG.Semidihedral.OddFieldSL2.minusIdentity_ne_one F h2
  have hker : φ.ker = Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rcases CFSG.ClassicalInvolution.sl2_normal_cases hq4 φ.ker inferInstance with h | h | h
    · exact absurd (h ▸ hZker ((CFSG.ClassicalInvolution.mem_center_sl2_iff _).mpr
        (Or.inr rfl))) (by rw [Subgroup.mem_bot]; exact hneg)
    · exact h
    · obtain ⟨a, b, hab⟩ := hnab
      obtain ⟨a', rfl⟩ := hφ a
      obtain ⟨b', rfl⟩ := hφ b
      have ha : φ a' = 1 := (MonoidHom.mem_ker).mp (h ▸ Subgroup.mem_top a')
      have hb : φ b' = 1 := (MonoidHom.mem_ker).mp (h ▸ Subgroup.mem_top b')
      exact absurd (by rw [ha, hb]) hab
  let e : X ≃* StatedProj (StatedSL 2 F) :=
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        (projectiveSpecialLinearGroupEquivStatedProj 2 F))
  have hadm : StatedLieAdmissible .PSL 2 (ringChar F) n :=
    ⟨hp, n.pos, le_rfl, fun h => by simp only [Prod.mk.injEq, true_and] at h; omega,
      fun h => by
        simp only [Prod.mk.injEq, true_and] at h
        rw [hcardN] at hq4
        omega⟩
  exact ⟨ringChar F, n, hp2, hadm, Or.inl ⟨hadm, F, inferInstance, inferInstance, hcardN, ⟨e⟩⟩⟩

end CFSG.LocalAnalysis.WeakClosure81

end
