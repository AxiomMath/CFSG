module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4OmP1

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Sec2Omega
  CFSG.ClassicalGroups.Orthogonal MulAction

@[expose] def nlU : List F6 :=
  [![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 1, 1], ![0, 0, 0, 1, 0, 1],
    ![0, 0, 0, 1, 1, 0], ![0, 0, 0, 1, 1, 1], ![0, 0, 1, 0, 0, 1], ![0, 0, 1, 0, 1, 0],
    ![0, 0, 1, 0, 1, 1], ![0, 0, 1, 1, 0, 0]]

theorem nlU_spec :
    ∀ a ∈ nlU, qMinus a = 1 ∧ polarMinus sig0 a = 0 ∧ polarMinus tau0 a = 0 := by decide

theorem nlU_fix : ∀ a ∈ nlU, ∀ b ∈ nlU,
    transv a (transv b sig0) = sig0 ∧ transv a (transv b tau0) = tau0 := by
  decide +kernel

theorem nlU_reach : ∀ y : F6, polarMinus y sig0 = 0 → polarMinus y tau0 = 0 → y ≠ 0 →
    ∃ a ∈ nlU, ∃ b ∈ nlU, transv a (transv b y) = y + a := by
  decide +kernel

theorem nlU_conn : ∀ a ∈ nlU, ∀ a' ∈ nlU,
    a = a' ∨ polarMinus a a' = 1 ∨ ∃ c ∈ nlU, polarMinus a c = 1 ∧ polarMinus c a' = 1 := by
  decide +kernel

theorem nlU_span : ∀ x : F6, ∃ c₁ c₂ : ZMod 2, ∃ a ∈ (0 :: nlU), ∃ a' ∈ (0 :: nlU),
    x = c₁ • sig0 + c₂ • tau0 + a + a' := by
  decide +kernel

theorem transv_transv_self : ∀ a a' : F6, polarMinus a a' = 1 → transv a' (transv a a) = a + a' := by
  decide +kernel

theorem proj_perp : ∀ w : F6,
    polarMinus (w + polarMinus w tau0 • sig0 + polarMinus w sig0 • tau0) sig0 = 0 ∧
    polarMinus (w + polarMinus w tau0 • sig0 + polarMinus w sig0 • tau0) tau0 = 0 := by
  decide +kernel

theorem eq_of_proj_eq_zero : ∀ w : F6,
    w + polarMinus w tau0 • sig0 + polarMinus w sig0 • tau0 = 0 →
      w = polarMinus w tau0 • sig0 + polarMinus w sig0 • tau0 := by
  decide +kernel

set_option synthInstance.maxSize 512 in
theorem fixed_decide : ∀ x : F6, (∀ a ∈ nlU, ∀ b ∈ nlU, transv a (transv b x) = x) →
    x = 0 ∨ x = sig0 ∨ x = tau0 ∨ x = sig0 + tau0 := by
  decide +kernel

theorem nlU_all_mem {W : Submodule (ZMod 2) F6}
    (hrr : ∀ a ∈ nlU, ∀ b ∈ nlU, ∀ x ∈ W, transv a (transv b x) ∈ W) {y : F6} (hyW : y ∈ W)
    (h1 : polarMinus y sig0 = 0) (h2 : polarMinus y tau0 = 0) (hy0 : y ≠ 0) :
    ∀ a ∈ nlU, a ∈ W := by
  obtain ⟨a, ha, b, hb, hab⟩ := nlU_reach y h1 h2 hy0
  have haW : a ∈ W := by
    have h := hrr a ha b hb _ hyW
    rw [hab] at h
    have h2 := W.sub_mem h hyW
    rwa [add_sub_cancel_left] at h2
  have hmove : ∀ a ∈ W, a ∈ nlU → ∀ a' ∈ nlU, polarMinus a a' = 1 → a' ∈ W := by
    intro a haW ha a' ha' h
    have h1 := hrr a' ha' a ha a haW
    rw [transv_transv_self a a' h] at h1
    have h2 := W.sub_mem h1 haW
    rwa [add_sub_cancel_left] at h2
  intro a' ha'
  rcases nlU_conn a ha a' ha' with h | h | ⟨c, hc, h1, h2⟩
  · rwa [← h]
  · exact hmove a haW ha a' ha' h
  · exact hmove c (hmove a haW ha c hc h1) hc a' ha' h2

theorem om_pair_irred {W : Submodule (ZMod 2) F6} (hs : sig0 ∈ W) (ht : tau0 ∈ W)
    (hW : ∀ g : OmG, g • sig0 = sig0 → g • tau0 = tau0 → ∀ w ∈ W, g • w ∈ W) :
    W = Submodule.span (ZMod 2) {sig0, tau0} ∨ W = ⊤ := by
  have hsU : sig0 ∈ Submodule.span (ZMod 2) {sig0, tau0} := Submodule.subset_span (by simp)
  have htU : tau0 ∈ Submodule.span (ZMod 2) {sig0, tau0} := Submodule.subset_span (by simp)
  by_cases hle : W ≤ Submodule.span (ZMod 2) {sig0, tau0}
  · left
    refine le_antisymm hle (Submodule.span_le.mpr ?_)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> assumption
  · right
    obtain ⟨w, hwW, hwU⟩ : ∃ w ∈ W, w ∉ Submodule.span (ZMod 2) {sig0, tau0} := by
      by_contra h
      push Not at h
      exact hle fun w hw => h w hw
    have hrr : ∀ a ∈ nlU, ∀ b ∈ nlU, ∀ x ∈ W, transv a (transv b x) ∈ W := by
      intro a ha b hb x hx
      have ha' := nlU_spec a ha
      have hb' := nlU_spec b hb
      have h := hW (rrOm ha'.1 hb'.1) (by rw [rrOm_smul]; exact (nlU_fix a ha b hb).1)
        (by rw [rrOm_smul]; exact (nlU_fix a ha b hb).2) x hx
      rwa [rrOm_smul] at h
    have hyW : w + polarMinus w tau0 • sig0 + polarMinus w sig0 • tau0 ∈ W :=
      W.add_mem (W.add_mem hwW (W.smul_mem _ hs)) (W.smul_mem _ ht)
    have hy0 : w + polarMinus w tau0 • sig0 + polarMinus w sig0 • tau0 ≠ 0 := by
      intro h
      apply hwU
      rw [eq_of_proj_eq_zero w h]
      exact add_mem (Submodule.smul_mem _ _ hsU) (Submodule.smul_mem _ _ htU)
    have hall := nlU_all_mem hrr hyW (proj_perp w).1 (proj_perp w).2 hy0
    have hall0 : ∀ a' ∈ (0 :: nlU), a' ∈ W := by
      intro a' ha'
      rcases List.mem_cons.mp ha' with rfl | h
      · exact W.zero_mem
      · exact hall a' h
    rw [eq_top_iff]
    intro x _
    obtain ⟨c₁, c₂, a₁, ha₁, a₂, ha₂, rfl⟩ := nlU_span x
    exact W.add_mem (W.add_mem (W.add_mem (W.smul_mem _ hs) (W.smul_mem _ ht)) (hall0 _ ha₁))
      (hall0 _ ha₂)

theorem om_pair_fixed {x : F6}
    (hx : ∀ g : OmG, g • sig0 = sig0 → g • tau0 = tau0 → g • x = x) :
    x = 0 ∨ x = sig0 ∨ x = tau0 ∨ x = sig0 + tau0 := by
  refine fixed_decide x fun a ha b hb => ?_
  have ha' := nlU_spec a ha
  have hb' := nlU_spec b hb
  have h := hx (rrOm ha'.1 hb'.1) (by rw [rrOm_smul]; exact (nlU_fix a ha b hb).1)
    (by rw [rrOm_smul]; exact (nlU_fix a ha b hb).2)
  rwa [rrOm_smul] at h

theorem exists_nonsing_perp : ∃ v : F6, qMinus v = 1 ∧ polarMinus v tau0 = 0 :=
  ⟨![0, 0, 0, 0, 1, 0], by decide, by decide⟩

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
