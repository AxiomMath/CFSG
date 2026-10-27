module

public import CFSG.Quasithin.Background.FLc6Grp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.A38c10

open Matrix CFSG.Quasithin CFSG.Quasithin.FLc CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem QI_four_three_eq : QI 4 {3} = stabilizer (flagSpace 4 (ZMod 2) 3) := by
  ext g
  simp [QI, mem_flagStabilizer]

theorem exists_psi3 : ∃ ψ : ↥(QI 4 {3}) →* SLt 3, Function.Surjective ψ ∧
    ∀ x : ↥(QI 4 {3}), ψ x = 1 → (x : SLt 4) ∈ Ut 4 := by
  have hle : QI 4 {3} ≤ stabilizer (flagSpace 4 (ZMod 2) 3) := QI_four_three_eq.le
  have h3 : (3 : ℕ) ≤ 4 := by norm_num
  have h4 : (3 : ℕ) < 4 := by norm_num
  have h45 : (4 : ℕ) = 4 ∨ (4 : ℕ) = 5 := Or.inl rfl
  refine ⟨(blk3Hom h3).comp (Subgroup.inclusion hle), ?_, ?_⟩
  ·
    have hmem1 : T1 4 h3 ∈ QI 4 {3} := QI_four_three_eq ▸ T1_mem_stab3 h3 h4
    have hmem2 : T2 4 h3 ∈ QI 4 {3} := QI_four_three_eq ▸ T2_mem_stab3 h3 h4
    have hA : gen3A ∈ ((blk3Hom h3).comp (Subgroup.inclusion hle)).range := by
      refine ⟨⟨T1 4 h3, hmem1⟩, Subtype.ext ?_⟩
      show blk3 h3 (T1 4 h3) = a3T1
      exact blk3_T1 h45 h3
    have hB : gen3B ∈ ((blk3Hom h3).comp (Subgroup.inclusion hle)).range := by
      refine ⟨⟨T2 4 h3, hmem2⟩, Subtype.ext ?_⟩
      show blk3 h3 (T2 4 h3) = b3T2
      exact blk3_T2 h45 h3
    intro y
    have hy : y ∈ Subgroup.closure ({gen3A, gen3B} : Set (SLt 3)) := by
      rw [closure_gen3A_gen3B]
      exact Subgroup.mem_top y
    have hle' : Subgroup.closure ({gen3A, gen3B} : Set (SLt 3)) ≤
        ((blk3Hom h3).comp (Subgroup.inclusion hle)).range := by
      rw [Subgroup.closure_le]
      rintro z (rfl | rfl)
      · exact hA
      · exact hB
    exact hle' hy
  · intro x hx
    have hb : blk3 h3 (x : SLt 4) = 1 := by
      have := congrArg (fun y : SLt 3 => (y : Matrix (Fin 3) (Fin 3) (ZMod 2))) hx
      exact this
    refine mem_Ut_of_blk3_eq_one h3 h4 (fun j hj3 hjn => ?_) hb
    have : j = 3 := by omega
    subst this
    exact hle x.2

end CFSG.Quasithin.A38c10
