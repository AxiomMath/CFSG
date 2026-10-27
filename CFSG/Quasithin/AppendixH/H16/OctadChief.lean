module

public import CFSG.Quasithin.AppendixH.H16.OctadGroup
public import CFSG.Quasithin.AppendixH.H16.MaskChief

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.LU24
  CFSG.Monster.Code CFSG.ASVolI.AppH

@[expose] def octWordsOfLen : ℕ → List (List ℕ)
  | 0 => [[]]
  | l + 1 => (octWordsOfLen l).flatMap fun w => [0 :: w, 1 :: w]

@[expose] def octWordsUpTo (L : ℕ) : List (List ℕ) := (List.range (L + 1)).flatMap octWordsOfLen

@[expose] def octFullBasis : List ℕ := [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024]

theorem chief_octV1 : chiefCheck [octG1C, octG2C] [] oct1Basis [[]] = true := by decide +kernel

theorem chief_octV5_V1 :
    chiefCheck [octG1C, octG2C] oct1Basis oct5Basis (octWordsUpTo 3) = true := by decide +kernel

theorem chief_top_octV5 :
    chiefCheck [octG1C, octG2C] oct5Basis octFullBasis (octWordsUpTo 4) = true := by
  decide +kernel

theorem maskSub_nil : maskSub 11 ([] : List ℕ) = (⊥ : Subgroup W11) := by
  ext v
  constructor
  · rintro ⟨m, hm, rfl⟩
    have hm0 : m = 0 := by simpa only [combos, List.mem_singleton] using hm
    rw [hm0, toW_zero]
    exact Subgroup.mem_bot.2 rfl
  · intro hv
    rw [Subgroup.mem_bot] at hv
    exact ⟨0, zero_mem_combos [], by rw [hv, toW_zero]⟩

theorem octFullBasis_reduce : ∀ m < 2 ^ 11, reduceBy (echelon octFullBasis) m = 0 := by
  decide +kernel

theorem maskSub_octFullBasis : maskSub 11 octFullBasis = (⊤ : Subgroup W11) := by
  refine eq_top_iff.2 fun v _ => ?_
  obtain ⟨m, hm, rfl⟩ := toW_surj 11 v
  exact toW_mem_maskSub (mem_combos_of_reduceBy_echelon octFullBasis m (octFullBasis_reduce m hm))

theorem rhoCd_octG1_mem : rhoCd octG1_mem ∈ imgCd (octStab octad0) :=
  rhoCd_mem_imgCd octG1_mem octG1_mem_octStab

theorem rhoCd_octG2_mem : rhoCd octG2_mem ∈ imgCd (octStab octad0) :=
  rhoCd_mem_imgCd octG2_mem octG2_mem_octStab

private theorem gens_mem : ∀ i < ([rhoCd octG1_mem, rhoCd octG2_mem] : List (MulAut W11)).length,
    ([rhoCd octG1_mem, rhoCd octG2_mem] : List (MulAut W11)).getD i 1 ∈
      imgCd (octStab octad0) := by
  intro i hi
  rcases i with _ | _ | i
  · exact rhoCd_octG1_mem
  · exact rhoCd_octG2_mem
  · simp at hi

private theorem gens_act : ∀ i < ([rhoCd octG1_mem, rhoCd octG2_mem] : List (MulAut W11)).length,
    ActsBy (([rhoCd octG1_mem, rhoCd octG2_mem] : List (MulAut W11)).getD i 1)
      (([octG1C, octG2C] : List (List ℕ)).getD i []) := by
  intro i hi
  rcases i with _ | _ | i
  · exact actsBy_octG1
  · exact actsBy_octG2
  · simp at hi

theorem isChiefFactorUnder_bot_octV1 :
    IsChiefFactorUnder (actsOnModule (imgCd (octStab octad0))) ⊥ octV1 := by
  rw [← maskSub_nil]
  refine isChiefFactorUnder_maskSub (n := 11) (G := imgCd (octStab octad0))
    [rhoCd octG1_mem, rhoCd octG2_mem] [octG1C, octG2C] gens_mem gens_act [] oct1Basis [[]]
    (by decide) chief_octV1 ?_ ?_ isActsInv_octV1
  · rw [maskSub_nil]
    refine bot_lt_iff_ne_bot.2 fun h => ?_
    have hc : Nat.card ↥(maskSub 11 oct1Basis) = 2 := card_octV1
    have hc1 : Nat.card ↥(maskSub 11 oct1Basis) = Nat.card ↥(⊥ : Subgroup W11) :=
      congrArg (fun K : Subgroup W11 => Nat.card ↥K) h
    rw [Subgroup.card_bot] at hc1
    omega
  · rw [maskSub_nil]
    rintro f ⟨y, hy, rfl⟩ v hv
    change y v ∈ (⊥ : Subgroup W11)
    rw [Subgroup.mem_bot] at hv
    rw [hv]
    exact Subgroup.mem_bot.2 (MulEquiv.map_one y)

theorem isChiefFactorUnder_octV1_octV5 :
    IsChiefFactorUnder (actsOnModule (imgCd (octStab octad0))) octV1 octV5 :=
  isChiefFactorUnder_maskSub (n := 11) (G := imgCd (octStab octad0))
    [rhoCd octG1_mem, rhoCd octG2_mem] [octG1C, octG2C] gens_mem gens_act oct1Basis oct5Basis
    (octWordsUpTo 3) (by decide +kernel) chief_octV5_V1 octV1_lt_octV5 isActsInv_octV1
    isActsInv_octV5

theorem isChiefFactorUnder_octV5_top :
    IsChiefFactorUnder (actsOnModule (imgCd (octStab octad0))) octV5 ⊤ := by
  rw [← maskSub_octFullBasis]
  refine isChiefFactorUnder_maskSub (n := 11) (G := imgCd (octStab octad0))
    [rhoCd octG1_mem, rhoCd octG2_mem] [octG1C, octG2C] gens_mem gens_act oct5Basis octFullBasis
    (octWordsUpTo 4) (by decide +kernel) chief_top_octV5 ?_ isActsInv_octV5 ?_
  · rw [maskSub_octFullBasis]
    exact octV5_lt_top
  · rw [maskSub_octFullBasis]
    rintro f ⟨y, hy, rfl⟩ v hv
    exact Subgroup.mem_top _

end CFSG.ASVolI.H16
