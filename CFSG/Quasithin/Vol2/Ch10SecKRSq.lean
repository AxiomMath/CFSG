module

public import CFSG.Quasithin.Vol2.Ch10SecKRSp
public import CFSG.Quasithin.Vol2.Ch10SecKRSf
public import CFSG.Quasithin.Vol2.Ch10SecKRSl

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.KRS

open CFSG.Open CFSG.Quasithin C10P4F
open scoped Matrix

theorem blkSL_one_mul (A A' : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    blkSL (1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) A * blkSL 1 A' = blkSL 1 (A * A') := by
  apply Subtype.ext
  show blk _ _ * blk _ _ = blk _ _
  ext a b
  rw [Matrix.mul_apply, Fin.sum_univ_add]
  rcases fin_add_cases a with ⟨a', rfl⟩ | ⟨a', rfl⟩ <;>
    rcases fin_add_cases b with ⟨b', rfl⟩ | ⟨b', rfl⟩ <;>
    simp [blk_cc, blk_cn, blk_nc, blk_nn, Matrix.mul_apply, Matrix.SpecialLinearGroup.coe_mul]
  all_goals (fin_cases a' <;> fin_cases b' <;> rfl)

theorem blkSL_one_pow (A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (n : ℕ) :
    blkSL (1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) A ^ n = blkSL 1 (A ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    apply Subtype.ext
    show (1 : Matrix (Fin (2 + 3)) (Fin (2 + 3)) (ZMod 2)) = blk _ _
    ext a b
    rcases fin_add_cases a with ⟨a', rfl⟩ | ⟨a', rfl⟩ <;>
      rcases fin_add_cases b with ⟨b', rfl⟩ | ⟨b', rfl⟩ <;>
      simp [blk_cc, blk_cn, blk_nc, blk_nn, Matrix.one_apply]
    all_goals (fin_cases a' <;> fin_cases b' <;> decide)
  | succ n ih => rw [pow_succ, ih, blkSL_one_mul, ← pow_succ]

theorem blkSL_one_one : blkSL (1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
    (1 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = 1 := by
  have h := blkSL_one_pow (1 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) 0
  rw [pow_zero, pow_zero] at h
  exact h.symm

theorem muQ2_surjective {G : Type} [Group G] {J P : Subgroup G} (ρ : ↥J →* SL5)
    (hρs : Function.Surjective ρ) (hker : ∀ j : ↥J, ρ j = 1 → ∃ m : ℕ, (j : G) ^ 2 ^ m = 1)
    (hPJ : P ≤ J) (hQ : ∀ x : ↥P, ρ (Subgroup.inclusion hPJ x) ∈ Q2)
    (hmem : ∀ j : ↥J, (j : G) ^ 3 = 1 →
      (ρ j : Matrix (Fin 5) (Fin 5) (ZMod 2)) * B0 * (ρ j : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ = B0 →
        (j : G) ∈ P) :
    Function.Surjective (muQ2 ρ hPJ hQ) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← theta_SL3]
  refine (Subgroup.closure_le _).mpr ?_
  rintro A ⟨-, hA3⟩
  set B : SL5 := blkSL (1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) A with hB
  have hB3 : B ^ 3 = 1 := by
    rw [hB, blkSL_one_pow, hA3, blkSL_one_one]
  have hker' : ∀ j : ↥J, ρ j = 1 → ∃ m : ℕ, j ^ 2 ^ m = 1 := fun j hj => by
    obtain ⟨m, hm⟩ := hker j hj
    exact ⟨m, Subtype.ext (by simpa using hm)⟩
  obtain ⟨j, hj3, hjB⟩ := exists_three_lift ρ hker' (hρs B) hB3
  have hjP : (j : G) ∈ P := hmem j (by simpa using congrArg Subtype.val hj3)
    (by rw [hjB]; exact blk_one_conj_B0 A)
  refine ⟨⟨j, hjP⟩, ?_⟩
  rw [muQ2_apply]
  have h1 : (⟨ρ (Subgroup.inclusion hPJ ⟨j, hjP⟩), hQ ⟨j, hjP⟩⟩ : ↥(stabStd 2 3)) =
      ⟨blkSL 1 A, blkSL_mem 1 A⟩ := Subtype.ext (by
    show ρ ⟨(j : G), hPJ hjP⟩ = B
    rw [← hjB])
  rw [h1, botH_blkSL]

end CFSG.Quasithin.Vol2.Ch10.SecC.KRS
