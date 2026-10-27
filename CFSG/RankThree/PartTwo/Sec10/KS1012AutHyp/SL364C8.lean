module

public import CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp.SL364C1
public import CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp.SL364C6
public import CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp.SL364C7
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofL364Lift

public section

namespace CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.Sec4.Res6L364 (K64)

theorem sq_eq_one_rootGL_K64 {u : Fin 3 → K64} {g : GL (Fin 3) K64} (hg : g ∈ rootGL u) :
    g ^ 2 = 1 := by
  obtain ⟨ψ, hψ, hgψ⟩ := mem_rootGL.mp hg
  have h2 : (2 : K64) = 0 := CFSG.RankThree.PartTwo.Sec4.Res6L364.two_eq_zero
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, pow_two, hgψ, elemMat_mul u ψ ψ hψ,
    ← two_smul K64 ψ, h2, zero_smul, elemMat_zero]

theorem isPGroup_two_rootSL_K64 (u : Fin 3 → K64) : IsPGroup 2 (rootSL u) := by
  apply isPGroup_two_of_sq_eq_one
  intro x hx
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  exact sq_eq_one_rootGL_K64 ((mem_rootSL x).mp hx)

theorem card_le_nine_K64 {F : Subgroup (MulAut (CFSG.Open.StatedSL 3 K64))}
    (hF : CFSG.Open.IsElemAbelian 3 F) (hD : ∀ g ∈ F, Dhom K64 g ∈ linearAutGroup 3 K64) :
    Nat.card F ≤ 9 := by
  have hB : CFSG.Open.IsElemAbelian 3 (F.map (Dhom K64)) :=
    CFSG.RankThree.PartTwo.Sec4.isElemAbelian_map _ hF
  have hle : F.map (Dhom K64) ≤ linearAutGroup 3 K64 := by
    rintro _ ⟨g, hg, rfl⟩
    exact hD g hg
  have hcard := CFSG.RankThree.PartTwo.Sec4.card_inf_linearAutGroup_three_le
    CFSG.RankThree.PartTwo.Sec4.Res6L364.three_ne_zero' hB
  rw [inf_eq_left.mpr hle, Subgroup.card_map_of_injective (Dhom_injective K64)] at hcard
  exact hcard

theorem conc_of_card_le_three_K64 {F : Subgroup (MulAut (CFSG.Open.StatedSL 3 K64))}
    (h : Nat.card F ≤ 3) : Conc (CFSG.Open.StatedSL 3 K64) F := by
  have hu0 : (![1, 0, 0] : Fin 3 → K64) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  refine ⟨⊥, bot_le, ?_, rootSL (![1, 0, 0] : Fin 3 → K64), rootSL_ne_bot hu0,
    isPGroup_two_rootSL_K64 _, ?_⟩
  · rw [Subgroup.card_bot]
    omega
  · intro f hf v hv
    rw [Subgroup.mem_bot.mp hf]
    simpa using hv

theorem conc_of_cube_one_K64 {F : Subgroup (MulAut (CFSG.Open.StatedSL 3 K64))}
    (hF : CFSG.Open.IsElemAbelian 3 F) {g : MulAut (CFSG.Open.StatedSL 3 K64)} (hg : g ∈ F)
    (hg1 : g ≠ 1) {A : GL (Fin 3) K64} (hA3 : A ^ 3 = 1) (hgA : Dhom K64 g = conjAut 3 K64 A)
    (h9 : Nat.card F ≤ 9) : Conc (CFSG.Open.StatedSL 3 K64) F := by
  have h3 : g ^ 3 = 1 := hF.2 g hg
  obtain ⟨u, hu0, l, hAu⟩ := exists_eigenvector_of_pow_three hA3
  have hstab := rootSL_stable_of_eigen hgA hAu
  refine ⟨Subgroup.zpowers g, ?_, ?_, rootSL u, rootSL_ne_bot hu0, isPGroup_two_rootSL_K64 u,
    stab_zpowers h3 hstab⟩
  · rw [Subgroup.zpowers_le]
    exact hg
  · rw [card_zpowers_eq_three h3 hg1]
    omega

theorem conc_of_linear {F : Subgroup (MulAut (CFSG.Open.StatedSL 3 K64))}
    (hF : CFSG.Open.IsElemAbelian 3 F) (hD : ∀ g ∈ F, Dhom K64 g ∈ linearAutGroup 3 K64) :
    Conc (CFSG.Open.StatedSL 3 K64) F := by
  have h9 := card_le_nine_K64 hF hD
  by_cases h3 : Nat.card F ≤ 3
  · exact conc_of_card_le_three_K64 h3
  · push Not at h3
    have hBr : F.map (Dhom K64) ≤ (conjAut 3 K64).range := by
      rintro _ ⟨g, hg, rfl⟩
      rw [← CFSG.RankThree.PartTwo.Sec4.linearAutGroup_three_eq_range]
      exact hD g hg
    have hBcard : 4 ≤ Nat.card (F.map (Dhom K64)) := by
      rw [Subgroup.card_map_of_injective (Dhom_injective K64)]
      omega
    obtain ⟨A, ⟨g, hg, hgA⟩, hA1, hdet⟩ := exists_det_one_lift hBr hBcard
    have hg3 : Dhom K64 g ^ 3 = 1 := by rw [← map_pow, hF.2 g hg, map_one]
    obtain ⟨B, hBA, hB3⟩ := exists_cube_one_of_det_one hdet (hgA ▸ hg3)
    have hg1 : g ≠ 1 := fun h => hA1 (by rw [← hgA, h, map_one])
    exact conc_of_cube_one_K64 hF hg hg1 hB3 (hgA.trans hBA.symm) h9

end CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp

end
