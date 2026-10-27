module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsWeakClosure
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22u
public import CFSG.Quasithin.Background.E3Basic
public import CFSG.GroupTheory.PCore.Transport
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.theorem_3_4
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem exists_b_of_not_oneFirst {M V₀ V : Subgroup G} {g : G} {n : ℕ}
    (hn : E3.mQuot V (conjSubgroup M g) ≤ n) (h : ¬ OneFirst M V₀ V g) :
    ∃ b ∈ conjSubgroup V g ⊓ M, b ∉ F11.CTilde M V₀ V ∧
      E3.mQuot V (V ⊓ centralizer ({b} : Set G)) ≤ n := by
  unfold OneFirst at h
  obtain ⟨b, hb, hbC⟩ := SetLike.not_le_iff_exists.1 h
  rw [Subgroup.mem_inf] at hb
  obtain ⟨hbVM, hbcent⟩ := hb
  refine ⟨b, hbVM, hbC, ?_⟩
  have hle : V ⊓ conjSubgroup M g ≤ V ⊓ centralizer ({b} : Set G) := by
    intro y hy
    rw [Subgroup.mem_inf] at hy ⊢
    refine ⟨hy.1, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 hbcent) y (Subgroup.mem_inf.2 hy)
  have hm : E3.mQuot V (V ⊓ conjSubgroup M g) = E3.mQuot V (conjSubgroup M g) := by
    unfold E3.mQuot
    rw [inf_comm, Subgroup.inf_relIndex_right]
  calc E3.mQuot V (V ⊓ centralizer ({b} : Set G))
      ≤ E3.mQuot V (V ⊓ conjSubgroup M g) := E3.mQuot_mono hle
    _ = E3.mQuot V (conjSubgroup M g) := hm
    _ ≤ n := hn

theorem exists_b_of_twoFirst {M V : Subgroup G} (hV : IsPGroup 2 V) {g : G} {n : ℕ}
    (h : TwoFirst n M V g) :
    ∃ b ∈ conjSubgroup V g ⊓ M, b ∉ centralizer (V : Set G) ∧
      E3.mQuot V (V ⊓ centralizer ({b} : Set G)) ≤ n := by
  unfold TwoFirst at h
  obtain ⟨I, hI, hne⟩ := h
  simp only [E3.gammaSet, Set.mem_setOf_eq] at hI
  obtain ⟨hIX, t, hIt, hmt⟩ := hI
  obtain ⟨b, hb, hbV⟩ := SetLike.not_le_iff_exists.1 hne
  rw [Subgroup.mem_inf] at hb
  obtain ⟨hbVM, hbCI⟩ := hb
  refine ⟨b, hbVM, hbV, ?_⟩
  have hIV : I ≤ V := le_trans hIX inf_le_left
  have hIcent : I ≤ centralizer ({b} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 hbCI) y hy
  have hIle : I ≤ V ⊓ centralizer ({b} : Set G) := le_inf hIV hIcent
  have hcardV : Nat.card V = 2 ^ E3.mQuot V I * Nat.card I :=
    E3.card_eq_two_pow_mul hV hIV
  have hcardVt : Nat.card (conjSubgroup V t) =
      2 ^ E3.mQuot (conjSubgroup V t) I * Nat.card I :=
    E3.card_eq_two_pow_mul (E3.isPGroup_conjSubgroup hV t) hIt
  have hcard : Nat.card (conjSubgroup V t) = Nat.card V := E3.card_conjSubgroup V t
  have hprod : 2 ^ E3.mQuot V I * Nat.card I = 2 ^ n * Nat.card I := by
    rw [← hmt, ← hcardVt, hcard, hcardV]
  have hpow : 2 ^ E3.mQuot V I = 2 ^ n :=
    Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := I)) hprod
  have hmn : E3.mQuot V I = n := Nat.pow_right_injective (le_refl 2) hpow
  calc E3.mQuot V (V ⊓ centralizer ({b} : Set G))
      ≤ E3.mQuot V I := E3.mQuot_mono hIle
    _ = n := hmn

theorem exists_b_of_inCalO2 {M V₀ V : Subgroup G} (hV : IsPGroup 2 V) {g : G} {n : ℕ}
    (h : InCalO2 n M V₀ V g) (hcase : V₀ = ⊥ ∨ ¬ OneFirst M V₀ V g) :
    ∃ b ∈ conjSubgroup V g ⊓ M, b ∉ F11.CTilde M V₀ V ∧
      E3.mQuot V (V ⊓ centralizer ({b} : Set G)) ≤ n := by
  rcases hcase with rfl | h1
  · obtain ⟨b, hb, hbC, hbn⟩ := exists_b_of_twoFirst hV h.2.1
    refine ⟨b, hb, ?_, hbn⟩
    rw [uc22p22u_cTilde_bot]
    intro hmem
    exact hbC (Subgroup.mem_inf.1 hmem).2
  · exact exists_b_of_not_oneFirst h.1.1.2.1 h1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
