module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsNineK

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Matrix CFSG.Assembly.LowTwoRank

theorem kSchurSL3_holds : KSchurSL3 := by
  intro X _ _ n hperf Z _ hZc hshape hn
  obtain ⟨K, hKfield, hKfinite, hKcard, ⟨eZ⟩⟩ := hshape
  letI := hKfield
  letI := hKfinite
  haveI : Group.IsPerfect X := ⟨hperf⟩
  let e : X ⧸ Z ≃* SpecialLinearGroup (Fin 3) K :=
    eZ.trans (specialLinearGroupEquivStatedSL 3 K).symm
  let π : X →* SpecialLinearGroup (Fin 3) K :=
    e.toMonoidHom.comp (QuotientGroup.mk' Z)
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective Z)
  have hker : π.ker = Z := by
    ext x
    simp [π, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, MulEquiv.map_eq_one_iff]
  have hcen : π.ker ≤ Subgroup.center X := by
    rw [hker]
    exact hZc
  have hF : 5 ≤ Nat.card K := by
    rw [hKcard]
    calc 5 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨σ, hσ⟩ :=
    CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_central
      (m := 2) (by norm_num) hF hπ hcen
  have hbot :=
    CFSG.LieType.Steinberg.CentralExt.SL2Closed.ker_eq_bot_of_section π hcen σ hσ
  rwa [hker] at hbot

end CFSG.LocalAnalysis.UniquenessCase.UC22
