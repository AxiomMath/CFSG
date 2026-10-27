module

public import CFSG.LieType.SeitzGeneration.ExcTorusPowerMap
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Three
public import CFSG.RankThree.PartOne.KE6.E8T3Arith
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSylow
public import CFSG.LocalAnalysis.StandardType.GGTBWNormE8PowerMap
public import CFSG.LieType.SeitzGeneration.ExcPlaneFamilies
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Four
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Three
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.Lattice.SteinbergBIE8OrderNine
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.CTCasesCycloGlue
public import CFSG.RankThree.PartOne.KE.E8FiveArith
public import CFSG.RankThree.PartOne.KE6.E8T3Data
public import CFSG.RankThree.PartOne.KF4.KernelTools
public import Certificates.Certificate1952

public noncomputable section

namespace CFSG.StandardType.E8PhiThreeWNorm

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE6
  CFSG.LieType.SeitzGeneration
  CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem pow_eight_ne_one_of_order_three {p q : ℕ}
    (hq : orderOf (q : ZMod p) = 3) : (q : ZMod p) ^ 8 ≠ 1 := by
  intro h
  have hdiv := orderOf_dvd_of_pow_eq_one h
  rw [hq] at hdiv
  norm_num at hdiv



theorem sylowTorus_powerMap_E8_phiThree {K : Type} [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hΦ : p ∣ Nat.card K ^ 2 + Nat.card K + 1) :
    SylowTorus (adjointGroup .E8 K) p 4 ∧
      ∃ V : Subgroup (adjointGroup .E8 K), IsElemAbelian p V ∧ Nat.card V = p ^ 4 ∧
        ∃ y : adjointGroup .E8 K, ∀ x ∈ V, y * x * y⁻¹ = x ^ Nat.card K := by
  have hΦ' : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + (1 : ℤ) * Nat.card K + 1 := by
    simpa only [one_mul] using
      (show (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + (Nat.card K : ℤ) + 1 from by exact_mod_cast hΦ)
  obtain ⟨-, -, -, hp7, he⟩ := e8T3_data (Or.inl rfl) hp hp3 hΦ'
  have he' : orderOf ((Nat.card K : ℕ) : ZMod p) = 3 := by simpa using he
  have h := sylowTorus_powerMap_of_blocks 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hp hp3
    (IsWeylMatrix.of_word Tag.E8 e8ThreeWord) [3, 3, 3, 3] e8Three_charpoly e8Three_pow he'
    (by decide) (not_dvd_of_blocks hp hp7 (by decide))
    (not_dvd_div_of_720 hp hp7 (by decide)) (by decide)
  simpa using h


theorem ggTorusWNormSC_recipe_E8_phiThree {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hΦ : p ∣ Nat.card K ^ 2 + Nat.card K + 1) :
    GGTorusWNormSC p (TableBExc.RecipeGroup .E8 K) (TableBExc.RecipeID .E8 K) := by
  have hpgt : 3 < p := by have := hp.two_le; omega
  obtain ⟨hS, hV⟩ := sylowTorus_powerMap_E8_phiThree hp hpgt hΦ
  have hΦ' : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + (1 : ℤ) * Nat.card K + 1 := by
    simpa only [one_mul] using
      (show (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + (Nat.card K : ℤ) + 1 from by exact_mod_cast hΦ)
  obtain ⟨-, -, -, -, he⟩ := e8T3_data (Or.inl rfl) hp hpgt hΦ'
  exact E8PowerWNorm.ggTorusWNormSC_recipe_E8_of_powerMap hp hp2 hS hV
    (pow_eight_ne_one_of_order_three (by simpa using he))

theorem largeEvenLabelAll_wnorm_E8_phiThree {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {lab : LargeEvenLabel} (htag : lab.tag = .E8)
    (hΦ : p ∣ (2 ^ lab.n) ^ 2 + 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  obtain ⟨t, r, f⟩ := lab
  dsimp only at htag hΦ ⊢
  subst htag
  have hf : 1 ≤ f := by
    by_contra h
    have hf0 : f = 0 := by omega
    subst f
    have hdiv : p ∣ 3 := by simpa using hΦ
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hdiv)
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQK⟩ := hQ
  let : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  refine ⟨K, i1, i2, hK, hQK, ?_⟩
  exact ggTorusWNormSC_recipe_E8_phiThree hp hp2 hp3 (by rw [hK]; exact hΦ)

end CFSG.StandardType.E8PhiThreeWNorm
