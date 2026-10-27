module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSp6SmallMain
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSp6SmallCard
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8CuUnique
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Inputs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup CFSG.Quasithin.SmithCurtis
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.SpCurtis

theorem rSp6SmallMod_holds (hSpin : S16SmSpinH1) : RSp6SmallMod := by
  intro W _ _ hW2 H U hS hU0 hcomm hm8
  obtain ⟨e⟩ := cu_nonempty_equiv_of_isSpn hS
  have h2 : ∀ x : Additive W, (2 : ℕ) • x = 0 := fun x => by
    apply Additive.toMul.injective
    rw [two_nsmul, toMul_add, toMul_zero]
    simpa [pow_two] using hW2 (Additive.toMul x)
  letI : Module (ZMod 2) (Additive W) := AddCommGroup.zmodModule h2
  let π : G6 →* ↥H := e.toMonoidHom
  have hπ : Function.Surjective π := e.surjective
  haveI : Nontrivial ↥(s16smSubmod U) := (s16sm_nontrivial_iff U).2 hU0
  have hperf : ∀ ψ : ↥(s16smSubmod U) →ₗ[ZMod 2] ZMod 2,
      (∀ g m, ψ (s16smRepU π hcomm g m) = ψ m) → ψ = 0 :=
    fun ψ hψ => s16sm_hperf_of_comm π hπ hcomm ψ hψ
  have h8 : Module.finrank (ZMod 2)
      (↥(s16smSubmod U) ⧸ (s16smRepU π hcomm).invariants) ≤ 8 := by
    rw [s16sm_finrank_quot_invariants π hπ hcomm]
    exact hm8
  rcases s16sm_main hSpin (s16smRepU π hcomm) hperf h8 with
    ⟨hfin, hinv, hsimple⟩ | ⟨hquot, hcent⟩
  · left
    exact ⟨by rw [s16sm_rk_eq_finrank U]; exact hfin,
      (s16sm_invariants_eq_bot_iff π hπ hcomm).1 hinv,
      s16sm_isIrrOn_of_simple π hπ hcomm hsimple⟩
  · right
    exact ⟨by rw [← s16sm_finrank_quot_invariants π hπ hcomm]; exact hquot,
      by rw [← s16sm_finrank_invariants π hπ hcomm]; exact hcent⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
