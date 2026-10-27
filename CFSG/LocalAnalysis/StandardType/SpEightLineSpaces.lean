module

public import CFSG.LocalAnalysis.StandardType.SpEightCoordinates
public import CFSG.LieType.SeitzGeneration.SpPlaneThreeF2Exceptional
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.StandardType.SpEight

open Matrix CFSG.Open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.KCSpFull
  CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.SpPlaneThree

@[expose] def spMat {E : Subgroup ↥(StatedSp 4 (ZMod 2))} (z : ↥E) : Matrix Idx Idx (ZMod 2) :=
  (((z : ↥(StatedSp 4 (ZMod 2))) : GL Idx (ZMod 2)) : Matrix Idx Idx (ZMod 2))

theorem spEnd_eq_spMat_mulVec {E : Subgroup ↥(StatedSp 4 (ZMod 2))} (z : ↥E) (v : Vec) :
    spEnd (z : ↥(StatedSp 4 (ZMod 2))) v = spMat z *ᵥ v :=
  rfl

theorem omega_eq_spForm (u v : Vec) : omega u v = spForm 4 (ZMod 2) u v := by
  rw [spForm_apply]
  rfl

theorem spPlaneFix_eq_bot_and_finrank_le_two_of_closure_ne_top
    {E : Subgroup ↥(StatedSp 4 (ZMod 2))}
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hcard : Nat.card E = 9)
    (hne : Subgroup.closure {g : ↥(StatedSp 4 (ZMod 2)) | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g} ≠ ⊤) :
    spPlaneFix E = ⊥ ∧ ∀ M : Subgroup ↥E, Nat.card M = 3 →
      Module.finrank (ZMod 2) (spLineSpace M) ≤ 2 := by
  by_contra h
  apply hne
  refine closure_centralizers_spPlane_three_F2_of_big_or_fixed (by simp) hcomm hexp hcard ?_
  by_contra hbf
  push Not at hbf
  exact h ⟨hbf.1, fun M hM => by have := hbf.2 M hM; omega⟩

theorem spLineSpace_ne_bot_of_finrank_le_two_of_four_le {r : ℕ} {K : Type} [Field K] [Finite K]
    {E : Subgroup (StatedSp r K)} (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ 3 = 1) (hcard : Nat.card E = 9) (h3 : (3 : K) ≠ 0)
    (hfix : spPlaneFix E = ⊥)
    (hle : ∀ M : Subgroup ↥E, Nat.card M = 3 → Module.finrank K (spLineSpace M) ≤ 2)
    (hr : 4 ≤ r) {M : Subgroup ↥E} (hM : Nat.card M = 3) : spLineSpace M ≠ ⊥ := by
  classical
  intro hbot
  have D := exists_spPlaneDecomp_three h3 hcomm hexp hcard
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Fintype E := Fintype.ofFinite E
  haveI : Fintype {M : Subgroup ↥E // Nat.card M = 3} := Fintype.ofFinite _
  have hP : CFSG.RankThree.PartOne.KCUnitaryPlane.IsPlane 3 ↥E :=
    ⟨Nat.prime_three, by rw [hcard]; norm_num, fun x => Subtype.ext (hexp x x.2)⟩
  have e := (LinearEquiv.ofBijective (DirectSum.coeLinearMap (spInnerSummand 3 E))
    D.internal).finrank_eq
  rw [Module.finrank_directSum, Fintype.sum_option] at e
  have h0 : Module.finrank K (spInnerSummand 3 E none) = 0 := by
    change Module.finrank K (spPlaneFix E) = 0
    rw [hfix]
    exact finrank_bot K _
  rw [h0, zero_add] at e
  change ∑ M : {M : Subgroup ↥E // Nat.card M = 3},
      Module.finrank K (spLineSpace M.1) =
    Module.finrank K (Fin r ⊕ Fin r → K) at e
  rw [← Finset.sum_subtype (CFSG.RankThree.PartOne.KCUnitaryPlane.lines 3 ↥E)
    (fun L => CFSG.RankThree.PartOne.KCUnitaryPlane.mem_lines)
    (fun L => Module.finrank K (spLineSpace L))] at e
  have hMmem : M ∈ CFSG.RankThree.PartOne.KCUnitaryPlane.lines 3 ↥E :=
    CFSG.RankThree.PartOne.KCUnitaryPlane.mem_lines.mpr hM
  rw [← Finset.add_sum_erase _ (fun L => Module.finrank K (spLineSpace L)) hMmem] at e
  have hbot' : Module.finrank K (spLineSpace M) = 0 := by
    rw [hbot]
    exact finrank_bot K _
  rw [hbot', zero_add] at e
  have hV : Module.finrank K (Fin r ⊕ Fin r → K) = r + r := by simp
  have hbound : ∑ L ∈ (CFSG.RankThree.PartOne.KCUnitaryPlane.lines 3 ↥E).erase M,
      Module.finrank K (spLineSpace L) ≤ 6 := by
    calc _ ≤ ((CFSG.RankThree.PartOne.KCUnitaryPlane.lines 3 ↥E).erase M).card • (2 : ℕ) :=
          Finset.sum_le_card_nsmul _ _ _ fun L hL =>
            hle L (CFSG.RankThree.PartOne.KCUnitaryPlane.mem_lines.mp (Finset.mem_of_mem_erase hL))
      _ = 6 := by
          rw [Finset.card_erase_of_mem hMmem, hP.card_lines]
          norm_num
  omega

theorem spLineSpace_ne_bot_of_finrank_le_two {E : Subgroup ↥(StatedSp 4 (ZMod 2))}
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hcard : Nat.card E = 9) (hfix : spPlaneFix E = ⊥)
    (hle : ∀ M : Subgroup ↥E, Nat.card M = 3 → Module.finrank (ZMod 2) (spLineSpace M) ≤ 2)
    {M : Subgroup ↥E} (hM : Nat.card M = 3) : spLineSpace M ≠ ⊥ :=
  spLineSpace_ne_bot_of_finrank_le_two_of_four_le hcomm hexp hcard (by decide) hfix hle
    (by norm_num) hM

theorem spLineSpace_ne_bot_of_closure_ne_top {E : Subgroup ↥(StatedSp 4 (ZMod 2))}
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hcard : Nat.card E = 9)
    (hne : Subgroup.closure {g : ↥(StatedSp 4 (ZMod 2)) | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g} ≠ ⊤)
    {M : Subgroup ↥E} (hM : Nat.card M = 3) : spLineSpace M ≠ ⊥ := by
  obtain ⟨hfix, hle⟩ := spPlaneFix_eq_bot_and_finrank_le_two_of_closure_ne_top hcomm hexp hcard hne
  exact spLineSpace_ne_bot_of_finrank_le_two hcomm hexp hcard hfix hle hM

end CFSG.StandardType.SpEight
