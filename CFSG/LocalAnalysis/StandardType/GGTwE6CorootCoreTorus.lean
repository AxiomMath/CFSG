module

public import CFSG.LocalAnalysis.StandardType.GGTwE6CorootCoreFrame
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotLeviCentralizerBasic
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24EightRoot
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLevi
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotHR6Y

public section

set_option linter.unusedSectionVars false

namespace CFSG.StandardType.TwE6CorootCore

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.SeitzReduction
  CFSG.LieType.Steinberg.Adjoint CFSG.SeitzReduction.TwistedE6Pilot CFSG.StandardType.TableBExcTwo
open CFSG.ClassicalInvolution.ModelFacts.Levi (thetaDiag rootChar_thetaDiag)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSEight (rootTorusSL2_eq_thetaDiag_e6)

local instance twE6CorootCoreTorusNeZero : NeZero Tag.E6.rank := ⟨by decide⟩

theorem frame_kernel_check : ∀ γ ∈ rootFinset .E6, ∃ i : Fin 4,
    iform (corootFrameRoot i) γ ≠ 0 ∧ |iform (corootFrameRoot i) γ| ≤ 2 := by
  decide +kernel

theorem frame_weyl_check : ∀ γ ∈ rootFinset .E6, ∀ j : Fin Tag.E6.rank, γ = Pi.single j 1 ∨
    (∃ i : Fin 4, iform (corootFrameRoot i) γ - iform (corootFrameRoot i) (Pi.single j 1) ∈
      ({1, -1, 2, -2, 4, -4} : Finset ℤ)) ∨
    coPair .E6 0 γ - coPair .E6 5 γ - (coPair .E6 0 (Pi.single j 1) -
      coPair .E6 5 (Pi.single j 1)) ∈ ({1, -1, 2, -2, 4, -4} : Finset ℤ) ∨
    coPair .E6 2 γ - coPair .E6 4 γ - (coPair .E6 2 (Pi.single j 1) -
      coPair .E6 4 (Pi.single j 1)) ∈ ({1, -1, 2, -2, 4, -4} : Finset ℤ) := by
  decide +kernel

section Char

variable {K : Type} [Field K] [CharP K 2]

theorem zpow_ne_one_of_abs_le_two {x : Kˣ} (hx : x ≠ 1) {d : ℤ} (h0 : d ≠ 0) (h2 : |d| ≤ 2) :
    x ^ d ≠ 1 :=
  fun h => h0 (EPilot.eq_zero_of_zpow_eq_one_of_charTwo hx h2 h)

theorem zpow_ne_one_of_mem {x : Kˣ} (hx : x ≠ 1) {d : ℤ}
    (hd : d ∈ ({1, -1, 2, -2, 4, -4} : Finset ℤ)) : x ^ d ≠ 1 := by
  have hx2 : x ^ (2 : ℤ) ≠ 1 := zpow_ne_one_of_abs_le_two hx (by norm_num) (by norm_num)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
  · exact zpow_ne_one_of_abs_le_two hx (by norm_num) (by norm_num)
  · exact zpow_ne_one_of_abs_le_two hx (by norm_num) (by norm_num)
  · exact hx2
  · exact zpow_ne_one_of_abs_le_two hx (by norm_num) (by norm_num)
  · rw [show (4 : ℤ) = 2 * 2 by norm_num, zpow_mul]
    exact zpow_ne_one_of_abs_le_two hx2 (by norm_num) (by norm_num)
  · rw [show (-4 : ℤ) = 2 * -2 by norm_num, zpow_mul]
    exact zpow_ne_one_of_abs_le_two hx2 (by norm_num) (by norm_num)

end Char

variable {K : Type} [Field K]

theorem rootChar_pairDiag_inv (j j' : Fin Tag.E6.rank) (l : Kˣ) (γ : Fin Tag.E6.rank → ℤ) :
    rootChar (pairDiag j j' l l⁻¹) γ = l ^ (coPair .E6 j γ - coPair .E6 j' γ) := by
  rw [rootChar_pairDiag, inv_zpow', ← zpow_add, ← sub_eq_add_neg]

variable (x l : Kˣ) in
@[expose] noncomputable def frameTori : List (Fin Tag.E6.rank → Kˣ) :=
  [thetaDiag (corootFrameRoot 0) x, thetaDiag (corootFrameRoot 1) l,
    thetaDiag (corootFrameRoot 2) l, thetaDiag (corootFrameRoot 3) l, pairDiag 0 5 l l⁻¹,
    pairDiag 2 4 l l⁻¹]

theorem thetaDiag_mem_frameTori (x l : Kˣ) (i : Fin 4) :
    thetaDiag (corootFrameRoot i) (if i = 0 then x else l) ∈ frameTori x l := by
  fin_cases i <;> simp [frameTori]

theorem pairDiag_mem_frameTori (x l : Kˣ) :
    pairDiag 0 5 l l⁻¹ ∈ frameTori x l ∧ pairDiag 2 4 l l⁻¹ ∈ frameTori x l := by
  simp [frameTori]


theorem rootDiagUnit_thetaDiag_mem_torusGroup {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot .E6 β)
    (c : Kˣ) : rootDiagUnit .E6 (thetaDiag β c) ∈ torusGroup .E6 K := by
  rw [← rootTorusSL2_eq_thetaDiag_e6 hβ c]
  exact (exceptional_Lang_root_rank_one_torus_transport .E6 K hβ).2.1 c

theorem rootDiagUnit_mem_torusGroup_of_mem_frameTori {x l : Kˣ} {b : Fin Tag.E6.rank → Kˣ}
    (hb : b ∈ frameTori x l) : rootDiagUnit .E6 b ∈ torusGroup .E6 K := by
  have hR : ∀ i, IsRoot .E6 (corootFrameRoot i) := fun i => mem_rootFinset.1 (corootFrameRoot_mem i)
  simp only [frameTori, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact rootDiagUnit_thetaDiag_mem_torusGroup (hR 0) x
  · exact rootDiagUnit_thetaDiag_mem_torusGroup (hR 1) l
  · exact rootDiagUnit_thetaDiag_mem_torusGroup (hR 2) l
  · exact rootDiagUnit_thetaDiag_mem_torusGroup (hR 3) l
  · exact rootDiagUnit_pairDiag_mem_torusGroup 0 5 l l⁻¹
  · exact rootDiagUnit_pairDiag_mem_torusGroup 2 4 l l⁻¹

theorem eq_one_of_mem_rootSpan_of_forall {S : Set (Fin Tag.E6.rank → ℤ)} {u : ModGL .E6 K}
    (hu : u ∈ rootSpan .E6 K S) (hS : ∀ α ∈ S, False) : u = 1 :=
  Subgroup.mem_bot.1 ((iSup₂_le fun α hα => (hS α hα).elim : rootSpan .E6 K S ≤ ⊥) hu)

theorem mem_torusGroup_of_commute_frameTori [CharP K 2] {x l : Kˣ} (hx : x ≠ 1) (hl : l ≠ 1)
    {g : ModGL .E6 K} (hg : g ∈ adjointGroup .E6 K)
    (hc : ∀ b ∈ frameTori x l, g * rootDiagUnit .E6 b = rootDiagUnit .E6 b * g) :
    g ∈ torusGroup .E6 K := by
  classical
  have hg1 : g ∈ toralCentralizer .E6 K 1 := by
    refine mem_toralCentralizer.2 ⟨hg, ?_⟩
    rw [rootDiagUnit_one, one_mul, inv_one, mul_one]
  obtain ⟨w, -, h, hh, u, hu, v, hv, rfl⟩ :=
    (Chevalley_toral_centralizer_Bruhat_factors .E6 K 1).1 _ hg1
  have huU : u ∈ posUnipotent .E6 K := rootSpan_mono Set.inter_subset_right hu
  have hvI : v ∈ rootSpan .E6 K (inversionSet w) := rootSpan_mono Set.inter_subset_right hv
  have hbase : ∀ i : Fin 4, (if i = 0 then x else l) ≠ 1 := fun i => by
    split_ifs
    exacts [hx, hl]
  have hL : ∀ b ∈ frameTori x l, b ∈ ((frameTori x l).map fun b => (b, b)).map Prod.fst ∧
      b ∈ ((frameTori x l).map fun b => (b, b)).map Prod.snd := fun b hb =>
    ⟨List.mem_map.2 ⟨(b, b), List.mem_map.2 ⟨b, hb, rfl⟩, rfl⟩,
      List.mem_map.2 ⟨(b, b), List.mem_map.2 ⟨b, hb, rfl⟩, rfl⟩⟩
  obtain ⟨hu', hv', hw⟩ := bruhat_factors_of_conj_list hh huU hvI
    ((frameTori x l).map fun b => (b, b)) fun p hp => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hp
      exact ⟨rootDiagUnit_mem_torusGroup_of_mem_frameTori hb,
        rootDiagUnit_mem_torusGroup_of_mem_frameTori hb, hc b hb⟩
  have hker : ∀ α, IsRoot .E6 α → (∀ b ∈ frameTori x l, rootChar b α = 1) → False := by
    intro α hα hall
    obtain ⟨i, hi0, hi2⟩ := frame_kernel_check α (mem_rootFinset.2 hα)
    have e := hall _ (thetaDiag_mem_frameTori x l i)
    rw [rootChar_thetaDiag] at e
    exact zpow_ne_one_of_abs_le_two (hbase i) hi0 hi2 e
  have hu1 : u = 1 := eq_one_of_mem_rootSpan_of_forall hu' fun α hα =>
    hker α hα.1.1 fun b hb => hα.2 b (hL b hb).1
  have hv1 : v = 1 := eq_one_of_mem_rootSpan_of_forall hv' fun α hα =>
    hker α (inversionSet_pos hα.1).1 fun b hb => hα.2 b (hL b hb).2
  have hchar : ∀ b ∈ frameTori x l, ∀ e, rootChar b (w • e) = rootChar b e := fun b hb =>
    (rootDiagUnit_eq_conj_canonicalRep_iff b b w).1 (hw (b, b) (List.mem_map.2 ⟨b, hb, rfl⟩))
  have hpair : ∀ {j j' : Fin Tag.E6.rank}, pairDiag j j' l l⁻¹ ∈ frameTori x l →
      ∀ e : Fin Tag.E6.rank → ℤ, coPair .E6 j (w • e) - coPair .E6 j' (w • e) -
        (coPair .E6 j e - coPair .E6 j' e) ∈ ({1, -1, 2, -2, 4, -4} : Finset ℤ) → False := by
    intro j j' hm e hd
    have he := hchar _ hm e
    rw [rootChar_pairDiag_inv, rootChar_pairDiag_inv] at he
    exact zpow_ne_one_of_mem hl hd (by rw [zpow_sub, he, mul_inv_cancel])
  have hwj : ∀ j, w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = Pi.single j 1 := by
    intro j
    rcases frame_weyl_check _ (mem_rootFinset.2 (IsRoot.smul (isRoot_single Tag.E6 j) w)) j with
      h | ⟨i, hi⟩ | hi | hi
    · exact h
    · have e := hchar _ (thetaDiag_mem_frameTori x l i) (Pi.single j 1)
      rw [rootChar_thetaDiag, rootChar_thetaDiag] at e
      exact (zpow_ne_one_of_mem (hbase i) hi (by rw [zpow_sub, e, mul_inv_cancel])).elim
    · exact (hpair (pairDiag_mem_frameTori x l).1 _ hi).elim
    · exact (hpair (pairDiag_mem_frameTori x l).2 _ hi).elim
  have hw1 : w = 1 := eq_one_of_forall_height_pos fun i => by
    rw [hwj i, height_single]
    norm_num
  rw [hw1, hu1, hv1, canonicalRep_one, mul_one, mul_one, mul_one]
  exact hh

end CFSG.StandardType.TwE6CorootCore

end
