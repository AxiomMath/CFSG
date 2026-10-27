module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37.ModelOvergroup
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3SevenNamed
public import Certificates.Certificate291442

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37

open CFSG.KC.Misc.F7 CFSG.KC.Loop CFSG.RankThree.Native.ONTriple
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3Seven
open scoped commutatorElement

attribute [local irreducible] dotProduct


set_option linter.unusedSectionVars false

theorem alphaPts_lt {k : ℕ} (hk : k < 9) : nthN alphaPts k < nPt := by
  rw [nthN_eq]
  exact (Certificates.certificate291442 k hk).1

@[expose] noncomputable def ωA (k : ℕ) : Sub7 := ptS (nthN alphaPts k)

theorem xE_val {l : ℕ} (hl : l < 2) (m i : ℕ) :
    ((xE 1 l m i : GM) : Mat45ˣ) =
      (eM ((rL.getD 1 []).getD l 0))⁻¹ * eM (vReg 1 m i) * eM ((rL.getD 1 []).getD l 0) := by
  rw [eM_rL (by norm_num) (by omega)]
  rfl

theorem xE_fix {k : ℕ} (hk : k < 9) {l i : ℕ} (hl : l < 2) (hi : i < 2) :
    xE 1 l (rowAt 1 k l) i • ωA k = ωA k := by
  rw [smul_sub7, xE_val hl, ωA, nthN_eq]
  exact (Certificates.certificate291442 k hk).2 l hl i hi

theorem LSub_one_le_stab {k : ℕ} (hk : k < 9) : LSub 1 k ≤ MulAction.stabilizer GM (ωA k) := by
  rw [ComponentPrimary.L3Seven.LSub, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
  fin_cases i
  · exact xE_fix hk (by norm_num) (by norm_num)
  · exact xE_fix hk (by norm_num) (by norm_num)
  · exact xE_fix hk (by norm_num) (by norm_num)
  · exact xE_fix hk (by norm_num) (by norm_num)

theorem isPerfect_LSub_one {k : ℕ} (hk : k < 9) : Group.IsPerfect (LSub 1 k) := by
  have hs := isSimpleGroup_LSub (j := 1) (by norm_num) hk
  have hfin : Finite (LSub 1 k) := Nat.finite_of_card_ne_zero (by rw [card_LSub (by norm_num) hk]; norm_num)
  have hnc : ∃ a b : LSub 1 k, a * b ≠ b * a := by
    by_contra h
    push Not at h
    let _ : CommGroup (LSub 1 k) := { (inferInstance : Group (LSub 1 k)) with mul_comm := h }
    have hp := IsSimpleGroup.prime_card (α := LSub 1 k)
    rw [card_LSub (by norm_num) hk] at hp
    norm_num at hp
  refine ⟨?_⟩
  rcases (Subgroup.commutator_normal (⊤ : Subgroup (LSub 1 k)) ⊤).eq_bot_or_eq_top with hb | ht
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    have hm : ⁅a, b⁆ ∈ commutator (LSub 1 k) :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [commutator_def, hb, Subgroup.mem_bot] at hm
    exact hab (commutatorElement_eq_one_iff_mul_comm.1 hm)
  · rw [commutator_def]
    exact ht

theorem le_normalizer_or_eq_top_LSub_one {k : ℕ} (hk : k < 9) {Y : Subgroup GM}
    (hY : LSub 1 k ≤ Y) : Y ≤ Subgroup.normalizer (LSub 1 k : Set GM) ∨ Y = ⊤ := by
  have := isPerfect_LSub_one hk
  exact le_normalizer_or_eq_top_of_perfect (ptS_mem_orbit _ (alphaPts_lt hk))
    (LSub_one_le_stab hk) (card_LSub (by norm_num) hk) hY

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37
