module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec14.Notation
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
import CFSG.RankThree.LocalRank.PrimeComplementCentralizesNormal
import CFSG.RankThree.PartTwo.KFacts.KS44OutSz
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec15.Item153ClaimsTools

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS
open scoped commutatorElement

namespace KS163TwoPowProof

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_map_le {S : Subgroup G} {g : G}
    (h : S.map (MulAut.conj g).toMonoidHom ≤ S) : g ∈ Subgroup.normalizer (S : Set G) := by
  have heq : S.map (MulAut.conj g).toMonoidHom = S := Subgroup.eq_of_le_of_card_ge h
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact h ⟨x, hx, rfl⟩
  · intro hx
    rw [← heq] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
      have h2 : g * y = g * x := mul_right_cancel hyx
      exact mul_left_cancel h2
    rwa [← this]

theorem le_pCoreOf_sup_of_commutator {Y R : Subgroup G} (hR2 : IsPGroup 2 R)
    (hRY : R ≤ Subgroup.normalizer (Y : Set G))
    (hcomm : ∀ r ∈ R, ∀ y ∈ Y, r * y * r⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Y) :
    R ≤ CFSG.Open.pCoreOf 2 (Y ⊔ R) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.Open.pCoreOf 2 Y with hO
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have hYO : Y ≤ Subgroup.normalizer (O : Set G) :=
    Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hRO : R ≤ Subgroup.normalizer (O : Set G) :=
    hRY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  set P := O ⊔ R with hP
  have hP2 : IsPGroup 2 P := IsPGroup.to_sup_of_normal_left' hO2 hR2 hRO
  have hOY : O ≤ Y := by
    rw [hO, CFSG.Open.pCoreOf]
    exact Subgroup.map_subtype_le _
  have hPle : P ≤ Y ⊔ R := sup_le (hOY.trans le_sup_left) le_sup_right
  have hYP : Y ≤ Subgroup.normalizer (P : Set G) := by
    intro y hy
    refine mem_normalizer_of_map_le ?_
    show P.map (MulAut.conj y).toMonoidHom ≤ P
    rw [hP, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨o, ho, rfl⟩
      exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hYO hy) o).mp ho)
    · rintro _ ⟨r, hr, rfl⟩
      have h1 : y * r * y⁻¹ * r⁻¹ ∈ O := by
        have := hcomm r hr y hy
        have h2 := O.inv_mem this
        rw [show (r * y * r⁻¹ * y⁻¹)⁻¹ = y * r * y⁻¹ * r⁻¹ by group] at h2
        exact h2
      change y * r * y⁻¹ ∈ O ⊔ R
      rw [show y * r * y⁻¹ = (y * r * y⁻¹ * r⁻¹) * r by group]
      exact mul_mem (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right hr)
  have hRP : R ≤ Subgroup.normalizer (P : Set G) := by
    intro r hr
    refine mem_normalizer_of_map_le ?_
    show P.map (MulAut.conj r).toMonoidHom ≤ P
    rw [hP, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨o, ho, rfl⟩
      exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hRO hr) o).mp ho)
    · rintro _ ⟨s, hs, rfl⟩
      exact Subgroup.mem_sup_right (mul_mem (mul_mem hr hs) (inv_mem hr))
  have hPO := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPle (sup_le hYP hRP) hP2
  exact le_sup_right.trans hPO

end KS163TwoPowProof

variable {G : Type} [Group G] [Finite G]

end CFSG.RankThree.PartTwo.Sec16
