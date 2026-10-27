module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.Quasithin

open scoped Matrix

namespace SBc17

variable {F : Type} [Field F]

@[expose] def sp4Block (A B : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  Matrix.fromBlocks (Matrix.diagonal ![A 0 0, B 0 0]) (Matrix.diagonal ![A 0 1, B 0 1])
    (Matrix.diagonal ![A 1 0, B 1 0]) (Matrix.diagonal ![A 1 1, B 1 1])

theorem sp4Block_mul (A B A' B' : Matrix (Fin 2) (Fin 2) F) :
    sp4Block A B * sp4Block A' B' = sp4Block (A * A') (B * B') := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [sp4Block, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply]

theorem sp4Block_one : sp4Block (1 : Matrix (Fin 2) (Fin 2) F) 1 = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [sp4Block, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

theorem sp4Block_symplectic {A B : Matrix (Fin 2) (Fin 2) F} (hA : A.det = 1) (hB : B.det = 1) :
    (sp4Block A B)ᵀ * Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) F) 1 (-1) 0 * sp4Block A B =
      Matrix.fromBlocks 0 1 (-1) 0 := by
  rw [Matrix.det_fin_two] at hA hB
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [sp4Block, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply, Matrix.transpose_apply,
      Matrix.one_apply] <;>
    first
      | done
      | ring1
      | linear_combination hA
      | linear_combination hB
      | linear_combination -hA
      | linear_combination -hB


theorem exists_injective_sl2_prod_statedSp :
    ∃ ι : (Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F) →*
        ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F), Function.Injective ι := by
  let f : (Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F) →*
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
    { toFun := fun p => sp4Block (p.1 : Matrix (Fin 2) (Fin 2) F) (p.2 : Matrix (Fin 2) (Fin 2) F)
      map_one' := by simpa using sp4Block_one
      map_mul' := fun p q => by
        simp only [Prod.fst_mul, Prod.snd_mul, Matrix.SpecialLinearGroup.coe_mul, sp4Block_mul] }
  let g := f.toHomUnits
  have hg : ∀ p, ((g p : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      sp4Block (p.1 : Matrix (Fin 2) (Fin 2) F) (p.2 : Matrix (Fin 2) (Fin 2) F) := fun p => rfl
  have hmem : ∀ p, g p ∈ CFSG.Assembly.LowTwoRank.StatedSp 2 F := by
    intro p
    refine Subgroup.subset_closure ?_
    show ((g p : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ *
      Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) F) 1 (-1) 0 *
        ((g p : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      Matrix.fromBlocks 0 1 (-1) 0
    rw [hg]
    exact sp4Block_symplectic p.1.det_coe p.2.det_coe
  refine ⟨g.codRestrict _ hmem, ?_⟩
  intro p q h
  have h1 : sp4Block (p.1 : Matrix (Fin 2) (Fin 2) F) (p.2 : Matrix (Fin 2) (Fin 2) F) =
      sp4Block (q.1 : Matrix (Fin 2) (Fin 2) F) (q.2 : Matrix (Fin 2) (Fin 2) F) := by
    have := congrArg (fun x : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F) =>
      ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) h
    exact this
  have e : ∀ i j : Fin 2 ⊕ Fin 2, sp4Block (p.1 : Matrix (Fin 2) (Fin 2) F) p.2 i j =
      sp4Block (q.1 : Matrix (Fin 2) (Fin 2) F) q.2 i j := fun i j => by rw [h1]
  refine Prod.ext (Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_)
    (Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_)
  · fin_cases i <;> fin_cases j
    · simpa [sp4Block] using e (Sum.inl 0) (Sum.inl 0)
    · simpa [sp4Block] using e (Sum.inl 0) (Sum.inr 0)
    · simpa [sp4Block] using e (Sum.inr 0) (Sum.inl 0)
    · simpa [sp4Block] using e (Sum.inr 0) (Sum.inr 0)
  · fin_cases i <;> fin_cases j
    · simpa [sp4Block] using e (Sum.inl 1) (Sum.inl 1)
    · simpa [sp4Block] using e (Sum.inl 1) (Sum.inr 1)
    · simpa [sp4Block] using e (Sum.inr 1) (Sum.inl 1)
    · simpa [sp4Block] using e (Sum.inr 1) (Sum.inr 1)

theorem two_le_pRank_statedSp_four [Fintype F] (hF : Fintype.card F = 4) :
    2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F)) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hfin : Finite ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F) := inferInstance
  have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 60 := by
    rw [Matrix.card_SL_field 2, hF, Fin.prod_univ_two]
    norm_num
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Matrix.SpecialLinearGroup (Fin 2) F) 5
    (by rw [hcard]; norm_num)
  obtain ⟨ι, hι⟩ := exists_injective_sl2_prod_statedSp (F := F)
  have hg5 : g ^ 5 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  let Z := Subgroup.zpowers g
  have hZcard : Nat.card Z = 5 := by rw [Nat.card_zpowers, hg]
  let f : (Z × Z) →* ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F) := ι.comp (Z.subtype.prodMap Z.subtype)
  have hf : Function.Injective f := by
    refine hι.comp ?_
    intro a b h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  have hZ5 : ∀ x : Z, x ^ 5 = 1 := by
    intro x
    obtain ⟨i, hi⟩ := x.2
    apply Subtype.ext
    show (x : Matrix.SpecialLinearGroup (Fin 2) F) ^ 5 = 1
    rw [← hi]
    show (g ^ i) ^ 5 = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg5, one_zpow]
  have hZc : ∀ x y : Z, x * y = y * x := by
    intro x y
    obtain ⟨i, hi⟩ := x.2
    obtain ⟨j, hj⟩ := y.2
    apply Subtype.ext
    show (x : Matrix.SpecialLinearGroup (Fin 2) F) * y = y * x
    rw [← hi, ← hj]
    show g ^ i * g ^ j = g ^ j * g ^ i
    exact (Commute.zpow_zpow_self g i j).eq
  refine CFSG.SectionRank.le_pRank_of_injective (by norm_num) ?_ ?_ ?_ f hf (le_top)
  · intro a b
    exact Prod.ext (hZc a.1 b.1) (hZc a.2 b.2)
  · intro a
    exact Prod.ext (by rw [Prod.pow_fst]; exact hZ5 _) (by rw [Prod.pow_snd]; exact hZ5 _)
  · rw [Nat.card_prod, hZcard]
    norm_num

end SBc17

end CFSG.Quasithin
