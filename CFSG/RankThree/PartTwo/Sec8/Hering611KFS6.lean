module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAction
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2KleinFourSelfCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourMapInjective
import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialEqualParameterGeneric
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.GorensteinWalter CFSG.RankThree CFSG.RankThree.LocalRank
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo (pglAction toPGL_pglAction)

structure S6Act {Kb : Type*} [Group Kb] (P : Subgroup Kb) (t : Kb) : Prop where
  mem_normalizer : t ∈ Subgroup.normalizer (P : Set Kb)
  theta_bot : aschbacherSolvableCore 3 P = ⊥
  data : ∃ v₁ v₂ h : Kb, v₁ ∈ P ∧ v₂ ∈ P ∧ h ∈ P ∧ v₁ ≠ 1 ∧ v₂ ≠ 1 ∧ v₁ ≠ v₂ ∧
    v₁ * v₁ = 1 ∧ v₂ * v₂ = 1 ∧ v₁ * v₂ = v₂ * v₁ ∧
    h * v₁ * h⁻¹ = v₂ ∧ h * v₂ * h⁻¹ = v₁ * v₂ ∧
    t * v₁ * t⁻¹ = v₁ ∧ t * v₂ * t⁻¹ = v₂ ∧ t * h * t⁻¹ = h
  nontrivial : ∃ x ∈ P, t * x * t⁻¹ ≠ x

section PGL


theorem eq_one_of_mem_range_pglAction {F : Type} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) {τ : MulAut (PSL2 F)}
    (hτ : τ ∈ (pglAction F).range) {v₁ v₂ h : PSL2 F} (hv₁ : v₁ ≠ 1) (hv₂ : v₂ ≠ 1)
    (hv₁₂ : v₁ ≠ v₂) (hv₁sq : v₁ * v₁ = 1) (hv₂sq : v₂ * v₂ = 1) (hc : v₁ * v₂ = v₂ * v₁)
    (hh₁ : h * v₁ * h⁻¹ = v₂) (hh₂ : h * v₂ * h⁻¹ = v₁ * v₂)
    (hτ₁ : τ v₁ = v₁) (hτ₂ : τ v₂ = v₂) (hτh : τ h = h) : τ = 1 := by
  obtain ⟨g, rfl⟩ := hτ
  let ι : PSL2 F →* PGL2 F := Matrix.ProjectiveSpecialLinearGroup.toPGL
  have hι : Function.Injective ι := fun _ _ h =>
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective h
  have hcomm : ∀ x : PSL2 F, pglAction F g x = x → ι x * g = g * ι x := by
    intro x hx
    have h1 := toPGL_pglAction F g x
    rw [hx] at h1
    calc ι x * g = (g * ι x * g⁻¹) * g := by rw [← h1]
      _ = g * ι x := by group
  have hv1sq' : orderOf v₁ = 2 := orderOf_eq_prime (by rw [sq]; exact hv₁sq) hv₁
  have hv2sq' : orderOf v₂ = 2 := orderOf_eq_prime (by rw [sq]; exact hv₂sq) hv₂
  set V : Subgroup (PSL2 F) := Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂ with hV
  have hVK : IsKleinFour V :=
    CFSG.Semidihedral.FixedCoreNontrivial.isKleinFour_sup_zpowers hv1sq' hv2sq' hv₁₂ hc
  have hVP : IsKleinFour (V.map ι) := isKleinFour_map_of_injective V hVK ι hι
  have hVC : V ≤ (Subgroup.centralizer ({g} : Set (PGL2 F))).comap ι := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      exact (hcomm v₁ hτ₁)
    · rw [Subgroup.zpowers_le, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      exact (hcomm v₂ hτ₂)
  have hgC : g ∈ Subgroup.centralizer ((V.map ι : Subgroup (PGL2 F)) : Set (PGL2 F)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨v, hv, rfl⟩
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hVC hv))
  rw [pgl2_kleinFour_centralizer_eq_self F hF _ hVP] at hgC
  obtain ⟨w, hwV, hwg⟩ := hgC
  have hwh : w * h = h * w := hι (by rw [map_mul, map_mul, hwg]; exact (hcomm h hτh).symm)
  have hw1 : w = 1 := by
    by_contra hw1
    have hv1V : v₁ ∈ V := Subgroup.mem_sup_left (Subgroup.mem_zpowers v₁)
    have hv2V : v₂ ∈ V := Subgroup.mem_sup_right (Subgroup.mem_zpowers v₂)
    have hcase : w = v₁ ∨ w = v₂ ∨ w = v₁ * v₂ := by
      by_cases h1 : w = v₁
      · exact Or.inl h1
      by_cases h2 : w = v₂
      · exact Or.inr (Or.inl h2)
      right; right
      have key := IsKleinFour.eq_mul_of_ne_all (G := V) (x := ⟨v₁, hv1V⟩) (y := ⟨v₂, hv2V⟩)
        (z := ⟨w, hwV⟩) (fun h => hv₁ (congrArg Subtype.val h))
        (fun h => hv₂ (congrArg Subtype.val h))
        (fun h => hv₁₂ (congrArg Subtype.val h)) (fun h => hw1 (congrArg Subtype.val h))
        (fun h => h1 (congrArg Subtype.val h)) (fun h => h2 (congrArg Subtype.val h))
      exact congrArg Subtype.val key
    rcases hcase with hw | hw | hw
    · rw [hw] at hwh
      have : v₁ = v₂ := by
        calc v₁ = v₁ * h * h⁻¹ := by group
          _ = h * v₁ * h⁻¹ := by rw [hwh]
          _ = v₂ := hh₁
      exact hv₁₂ this
    · rw [hw] at hwh
      have : v₂ = v₁ * v₂ := by
        calc v₂ = v₂ * h * h⁻¹ := by group
          _ = h * v₂ * h⁻¹ := by rw [hwh]
          _ = v₁ * v₂ := hh₂
      exact hv₁ (by simpa using this.symm)
    · rw [hw] at hwh
      have h3 : h * (v₁ * v₂) * h⁻¹ = v₁ := by
        rw [show h * (v₁ * v₂) * h⁻¹ = (h * v₁ * h⁻¹) * (h * v₂ * h⁻¹) by group, hh₁, hh₂]
        calc v₂ * (v₁ * v₂) = v₁ * (v₂ * v₂) := by rw [← mul_assoc, ← hc, mul_assoc]
          _ = v₁ := by rw [hv₂sq, mul_one]
      have h4 : v₁ * v₂ = v₁ := by
        calc v₁ * v₂ = h * (v₁ * v₂) * h⁻¹ := by rw [← hwh]; group
          _ = v₁ := h3
      exact hv₂ (by simpa using h4)
  rw [hw1, map_one] at hwg
  rw [← hwg, map_one]

end PGL

end CFSG.RankThree.PartTwo.Sec8.Hering611
