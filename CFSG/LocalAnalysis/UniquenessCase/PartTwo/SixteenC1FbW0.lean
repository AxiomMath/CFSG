module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1FbSyl
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAk

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1_gamma_barSub_mem (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h21 : R1621 D) (h22 : R1622 D) (h42 : R16_42 D) (h43 : R16_43_1 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (hc : Case167_1 D V₀ V hV L) {A : Subgroup G} (hA : A ∈ E3.gammaSet V 0 D.T) :
    barSub V₀ V hV A ≤ barSub V₀ V hV D.T ⊓ lBar V₀ V hV L ∧
      (barSub V₀ V hV A ≠ ⊥ → barSub V₀ V hV A ∈ E3.aSet 2 (lBar V₀ V hV L)) := by
  simp only [E3.gammaSet, Set.mem_setOf_eq] at hA
  obtain ⟨hAT, g, hAg, hm⟩ := hA
  have hAM : A ∈ E3.gammaSet V 0 D.M := ⟨hAT.trans D.sylowM.le, g, hAg, hm⟩
  have hH : Hyp1643 D V₀ V 0 A g := ⟨Or.inl rfl, hAM, hAg⟩
  have hleL : barSub V₀ V hV A ≤ lBar V₀ V hV L := h43 V₀ V L hV hS hc 0 A g hH
  refine ⟨le_inf (barSub_mono V₀ V hV hAT) hleL, fun hne => ?_⟩
  have hmemM : barSub V₀ V hV A ∈ calABar 2 D.M V₀ V hV :=
    sixteen_fortyThree_two D hSg h1219 h21 h22 h42 V₀ V L hV hS hc 0 A g hH rfl hne
  have hmemM' : barSub V₀ V hV A ∈ E3.aSet 2 (barSub V₀ V hV D.M) := hmemM
  simp only [E3.aSet, Set.mem_setOf_eq] at hmemM'
  obtain ⟨-, hne', hel, hfix'⟩ := hmemM'
  exact ⟨hleL, hne', hel, hfix'⟩

theorem s16c1_gamma_le_centralizer (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (h21 : R1621 D) (h22 : R1622 D) (h42 : R16_42 D) (h43 : R16_43_1 D)
    (hkitB : OmegaKitB) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hc : Case167_1 D V₀ V hV L) {x : IntMod V hV}
    (hsyl : IsSylowIn 2 (barSub V₀ V hV D.T ⊓ lBar V₀ V hV L) (lBar V₀ V hV L))
    (hz1 : mkTil V₀ V hV x ≠ 1)
    (h960 : Nat.card (ptCent (lBar V₀ V hV L) (mkTil V₀ V hV x)) = 960)
    (horb : (ptCent (barSub V₀ V hV D.T ⊓ lBar V₀ V hV L) (mkTil V₀ V hV x)).relIndex
      (barSub V₀ V hV D.T ⊓ lBar V₀ V hV L) ≤ 4)
    {A : Subgroup G} (hA : A ∈ E3.gammaSet V 0 D.T) :
    A ≤ centralizer ({x.val} : Set G) := by
  simp only [E3.gammaSet, Set.mem_setOf_eq] at hA
  obtain ⟨hAT, g, hAg, hm⟩ := hA
  have hAM : A ∈ E3.gammaSet V 0 D.M := ⟨hAT.trans D.sylowM.le, g, hAg, hm⟩
  have hmem := s16c1_gamma_barSub_mem D hSg h1219 h21 h22 h42 h43 hS hc ⟨hAT, g, hAg, hm⟩
  have hAleS : barSub V₀ V hV A ≤ barSub V₀ V hV D.T ⊓ lBar V₀ V hV L := hmem.1
  have hkit := hkitB (Vtil V₀ V hV) (lBar V₀ V hV L) hc.2.1
  have hfix : ∀ a ∈ barSub V₀ V hV A, a (mkTil V₀ V hV x) = mkTil V₀ V hV x := by
    intro a ha
    by_cases hbot : barSub V₀ V hV A = ⊥
    · rw [hbot, Subgroup.mem_bot] at ha
      subst ha
      simp
    · exact hkit.2.2.1 (barSub V₀ V hV D.T ⊓ lBar V₀ V hV L) hsyl
        (barSub V₀ V hV A) (hmem.2 hbot) hAleS (mkTil V₀ V hV x) hz1 h960 horb a ha
  have hcomm : ∀ a ∈ A, ⁅x.val, a⁆ ∈ V₀ := by
    intro a ha
    have haM : a ∈ D.M := D.sylowM.le (hAT ha)
    have hast : a ∈ stabTil V₀ V := s16c1_M_le_stabTil hS haM
    have hact : actTil V₀ V hV ⟨a, hast⟩ ∈ barSub V₀ V hV A :=
      actTil_mem_barSub V₀ V hV ha hast
    have h1 : actTil V₀ V hV ⟨a, hast⟩ (mkTil V₀ V hV x) = mkTil V₀ V hV x :=
      hfix _ hact
    rw [actTil_mk, mkTil_eq_iff, actStab_apply_val] at h1
    have h2 : (a * x.val * a⁻¹ * x.val⁻¹)⁻¹ ∈ V₀ :=
      V₀.inv_mem (by simpa only [Subtype.coe_mk] using h1)
    have hEq : (a * x.val * a⁻¹ * x.val⁻¹)⁻¹ = ⁅x.val, a⁆ := by
      rw [commutatorElement_def]
      group
    rwa [hEq] at h2
  have hi : ((0 + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V :=
    lt_of_lt_of_le (by exact_mod_cast (by omega : 0 + mSub V₀ < mSub V₀ + 4))
      (h42 V₀ V L hV hS hc).1
  have hxcent : x.val ∈ centralizer (A : Set G) :=
    (sixteen_twentyThree_one D h22 hS.setting.hyp16 hAM hAg hi).2.1 x.val x.val_mem hcomm
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  exact (Subgroup.mem_centralizer_iff.1 hxcent a ha).symm

theorem s16c1_wClos_le_centralizer (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (h21 : R1621 D) (h22 : R1622 D) (h42 : R16_42 D) (h43 : R16_43_1 D)
    (hkitB : OmegaKitB) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hc : Case167_1 D V₀ V hV L) {x : IntMod V hV}
    (hsyl : IsSylowIn 2 (barSub V₀ V hV D.T ⊓ lBar V₀ V hV L) (lBar V₀ V hV L))
    (hz1 : mkTil V₀ V hV x ≠ 1)
    (h960 : Nat.card (ptCent (lBar V₀ V hV L) (mkTil V₀ V hV x)) = 960)
    (horb : (ptCent (barSub V₀ V hV D.T ⊓ lBar V₀ V hV L) (mkTil V₀ V hV x)).relIndex
      (barSub V₀ V hV D.T ⊓ lBar V₀ V hV L) ≤ 4) :
    E3.wClos V 0 D.T ≤ centralizer ({x.val} : Set G) := by
  unfold E3.wClos
  exact iSup₂_le fun A hA => s16c1_gamma_le_centralizer D hSg h1219 h21 h22 h42 h43 hkitB hS hc
    hsyl hz1 h960 horb hA

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
