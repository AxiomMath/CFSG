
module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.LocalAnalysis.SectionRank.Ccomm.PrimeLinear
import CFSG.Adapters.StatedPSLTwo

public section

namespace CFSG.Quasithin.A36B

open Matrix

theorem exists_finset_card_four {r : ℕ} [Fact r.Prime] (h5 : 5 ≤ r) :
    ∃ s : Finset (ZMod r), s.card = 4 := by
  obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (ZMod r)))
    (n := 4) (by rw [Finset.card_univ, ZMod.card]; omega)
  exact ⟨t, ht⟩

theorem isPerfect_sl2 {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) :
    Group.IsPerfect (SpecialLinearGroup (Fin 2) (ZMod r)) := by
  have := Fact.mk hr
  exact CFSG.LinearGroups.special_linear_dimension_two_perfect (exists_finset_card_four h5)

theorem isSimple_psl2 {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) :
    IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin 2) (ZMod r)) := by
  have := Fact.mk hr
  exact Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [Nat.card_zmod]; omega)

theorem isQuasisimple_sl2 {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) :
    CFSG.IsQuasisimple (SpecialLinearGroup (Fin 2) (ZMod r)) := by
  have := Fact.mk hr
  have hperf := isPerfect_sl2 hr h5
  have hsimple : IsSimpleGroup (SpecialLinearGroup (Fin 2) (ZMod r) ⧸
      Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod r))) := isSimple_psl2 hr h5
  refine ⟨hperf, hsimple, ?_⟩
  by_contra hcon
  push Not at hcon
  have hcomm : IsMulCommutative (SpecialLinearGroup (Fin 2) (ZMod r) ⧸
      Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod r))) := ⟨⟨fun a b => hcon a b⟩⟩
  exact Group.IsPerfect.not_isMulCommutative _ hcomm

theorem card_rootsOfUnity_two {K : Type*} [Field K] (hchar : (2 : K) ≠ 0) :
    Nat.card (rootsOfUnity 2 K) = 2 := by
  classical
  let z : rootsOfUnity 2 K :=
    ⟨(-1 : Kˣ), by
      rw [mem_rootsOfUnity]
      apply Units.ext
      simp [pow_two]⟩
  have hz : z ≠ (1 : rootsOfUnity 2 K) := by
    intro hz
    have hvU : (-1 : Kˣ) = 1 := by
      simpa [z] using congrArg (fun x : rootsOfUnity 2 K ↦ (x : Kˣ)) hz
    have hv' : (-1 : K) = 1 := congrArg Units.val hvU
    apply hchar
    calc (2 : K) = 1 - (-1) := by ring
      _ = 1 - 1 := by rw [hv']
      _ = 0 := by ring
  apply (Nat.card_eq_two_iff' (1 : rootsOfUnity 2 K)).2
  refine ⟨z, hz, ?_⟩
  intro y hy
  have hyPow : (y : Kˣ) ^ 2 = 1 := (mem_rootsOfUnity 2 (y : Kˣ)).mp y.property
  let a : K := ((y : Kˣ) : K)
  have hyPow' : a ^ 2 = 1 := by simpa [a] using congrArg Units.val hyPow
  have hfactor : (a - 1) * (a + 1) = 0 := by
    calc (a - 1) * (a + 1) = a ^ 2 - 1 := by ring
      _ = 0 := by rw [hyPow']; ring
  rcases mul_eq_zero.mp hfactor with hminus | hplus
  · exfalso
    apply hy
    apply Subtype.ext
    apply Units.ext
    change a = 1
    exact sub_eq_zero.mp hminus
  · apply Subtype.ext
    apply Units.ext
    change a = -1
    exact eq_neg_of_add_eq_zero_left hplus

theorem card_center_sl2 {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    Nat.card (Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod r))) = 2 := by
  have := Fact.mk hr
  have e := Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (i := (0 : Fin 2)) (R := ZMod r)
  rw [Nat.card_congr e.toEquiv]
  exact card_rootsOfUnity_two (CFSG.SectionRank.Ccomm.two_ne_zero_zmod hr2)

theorem sq_eq_one_of_mem_center_sl2 {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {z : SpecialLinearGroup (Fin 2) (ZMod r)} (hz : z ∈ Subgroup.center _) : z ^ 2 = 1 := by
  have h1 := pow_card_eq_one' (G := Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod r)))
    (x := ⟨z, hz⟩)
  rw [card_center_sl2 hr hr2] at h1
  exact congrArg Subtype.val h1

theorem isPSL_two_of_mulEquiv {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) {Y : Type} [Group Y]
    (e : Y ≃* ProjectiveSpecialLinearGroup (Fin 2) (ZMod r)) : IsPSL 2 r 1 Y :=
  CFSG.Open.StatedAPI.statedClassicalModel_psl_two_of_mulEquiv_zmod hr h5 e

theorem isPSL_of_mulEquiv {r : ℕ} {Y Y' : Type} [Group Y] [Group Y'] (e : Y' ≃* Y)
    (h : IsPSL 2 r 1 Y) : IsPSL 2 r 1 Y' := by
  obtain ⟨hadm, K, hK, hfin, hcard, ⟨f⟩⟩ := h
  exact ⟨hadm, K, hK, hfin, hcard, ⟨e.trans f⟩⟩

end CFSG.Quasithin.A36B
