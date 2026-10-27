module

public import CFSG.RankThree.PartTwo.Sec6.HeringB3Tools
public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusSp4Odd
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof
public import CFSG.RankThree.PartTwo.KFacts.AutG2OrderThree
public import CFSG.RankThree.PartTwo.KFacts.K71G2
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieG2
import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenG2Two
import CFSG.RankThree.Chevalley.SteinbergCFExceptionalModelCover
import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
import CFSG.LieType.Chevalley.SignKernelComponentPerfect
import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdBasic
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdGen
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6A312Rank2

public section

namespace CFSG.RankThree.PartTwo.Sec6.BThreeCensus

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartTwo.KFacts

section Certs


variable {K : Type} [Field K] [Finite K]

theorem not_three_dvd_card_of_ringChar_ne_three (h : ringChar K ≠ 3) : ¬ 3 ∣ Nat.card K := by
  intro h3
  have : Fintype K := Fintype.ofFinite K
  haveI := ringChar.charP K
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K (ringChar K)
  rw [Nat.card_eq_fintype_card, hcard] at h3
  exact h ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
    (Nat.prime_three.dvd_of_dvd_pow h3)).symm

theorem three_dvd_card_adjointG2 (h : ringChar K ≠ 3) :
    3 ∣ Nat.card (adjointGroup .G2 K) := by
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2]
  unfold CFSG.Open.ordG2
  refine Dvd.dvd.mul_left ?_ _
  have hq := not_three_dvd_card_of_ringChar_ne_three h
  generalize Nat.card K = q at hq ⊢
  have h1 : q ^ 2 % 3 = 1 := by
    have : q % 3 = 1 ∨ q % 3 = 2 := by omega
    rcases this with h1 | h1 <;> simp [Nat.pow_mod, h1]
  omega

theorem exists_order_three_adjointG2 (h : ringChar K ≠ 3) :
    ∃ x : adjointGroup .G2 K, x ≠ 1 ∧ x ^ 3 = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 (three_dvd_card_adjointG2 h)
  exact ⟨x, fun h1 => by simp [h1] at hx, by rw [← hx]; exact pow_orderOf_eq_one x⟩

theorem perfSubnormalBot_centralizer_g2 (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K)
    (z : adjointGroup .G2 K) (hz3 : z ^ 3 = 1) :
    PerfSubnormalBot (Subgroup.centralizer ({z} : Set (adjointGroup .G2 K))) := by
  by_cases hz1 : z = 1
  · subst hz1
    have hC : Subgroup.centralizer ({1} : Set (adjointGroup .G2 K)) = ⊤ := by
      ext y
      simp [Subgroup.mem_centralizer_singleton_iff]
    rw [hC]
    have hs : IsSimpleGroup (adjointGroup .G2 K) :=
      CFSG.QuasithinUnique.Id2519.isSimpleGroup_adjointGroup_g2 (by omega)
    exact perfSubnormalBot_of_isSimpleGroup Subgroup.topEquiv.isSimpleGroup
      (by obtain ⟨x, hx1, hx3⟩ := exists_order_three_adjointG2 hK3
          exact ⟨x, Subgroup.mem_top x, hx1, hx3⟩)
  · obtain ⟨g, hg⟩ := KS11Lie7Proof.g2ThreeConjSL2_holds K hK3 hK4 z hz3 hz1
    refine perfSubnormalBot_centralizer_of_conj z g ?_
    have hw3 : (g * z * g⁻¹) ^ 3 = 1 := by
      rw [conj_pow, hz3]
      group
    have hw1 : g * z * g⁻¹ ≠ 1 := fun h => hz1 (by
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group)
    rcases hg with hS | hM
    · obtain ⟨N, hNC, hcomm, hNq, x, hxN, -, hx1, hx3⟩ :=
        KS11Lie7Proof.g2ThreeACent_holds K hK3 hK4 _ hS hw3 hw1
      exact perfSubnormalBot_of_commutators_le_quasisimple hNC hcomm hNq ⟨x, hxN, hx1, hx3⟩
    · obtain ⟨hcomm, -⟩ := KS11Lie4Proof.g2ThreeBCent_holds K hK3 hK4 _ hM hw3 hw1
      obtain ⟨e⟩ := KS11Lie4Proof.nonempty_mulEquiv_g2ShortSL2 (K := K)
      exact perfSubnormalBot_of_commutators_le_glTwo hcomm
        (Matrix.SpecialLinearGroup.toGL.comp e.symm.toMonoidHom)
        (Matrix.SpecialLinearGroup.toGL_injective.comp e.symm.injective)

theorem b3Fix_g2_of_inner (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K)
    {β : MulAut (adjointGroup .G2 K)} (hβ : β ^ 3 = 1) (hin : IsInnerAut β)
    {C : Subgroup (adjointGroup .G2 K)} (hC : ∀ z, z ∈ C ↔ β z = z) : B3Fix C := by
  obtain ⟨z, rfl⟩ := hin
  have hz3 : z ^ 3 = 1 := pow_three_eq_one_of_conj_pow_three center_adjointGroup_eq_bot hβ
  rw [fixed_conj_eq_centralizer hC]
  exact b3Fix_of_perfSubnormalBot (perfSubnormalBot_centralizer_g2 hK3 hK4 z hz3)

theorem card_eq_two_or_four_le_of_ringChar_two {k : Type} [Field k] [Finite k]
    (h : ringChar k = 2) : Nat.card k = 2 ∨ 4 ≤ Nat.card k := by
  have : Fintype k := Fintype.ofFinite k
  haveI := ringChar.charP k
  obtain ⟨n, hp, hcard⟩ := FiniteField.card k (ringChar k)
  rw [Nat.card_eq_fintype_card, hcard, h]
  rcases n with ⟨n, hn⟩
  rcases (by omega : n = 1 ∨ 2 ≤ n) with rfl | h2
  · left
    rfl
  · right
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h2

theorem b3Fix_g2_of_outer (hK2 : ringChar K = 2) (hK4 : 4 ≤ Nat.card K)
    {β : MulAut (adjointGroup .G2 K)} (hβ : β ^ 3 = 1) (hout : ¬ IsInnerAut β)
    {C : Subgroup (adjointGroup .G2 K)} (hC : ∀ z, z ∈ C ↔ β z = z) : B3Fix C := by
  have hK3 : ringChar K ≠ 3 := by rw [hK2]; norm_num
  obtain ⟨σ, hσ, k, hk⟩ := g2_order_three_field_descent hK3 hK4 hβ hout
  have hmap : C.map (MulAut.conj k⁻¹ : adjointGroup .G2 K ≃* _).toMonoidHom =
      (g2Incl σ).range := by
    ext y
    rw [Subgroup.mem_map, mem_range_g2Incl_iff hK2 σ y]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h1 := (hC x).mp hx
      rw [hk, conj_mul_conj_inv_apply] at h1
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      calc g2FieldHom K σ (k⁻¹ * x * k)
          = k⁻¹ * (k * g2FieldHom K σ (k⁻¹ * x * k) * k⁻¹) * k := by group
        _ = k⁻¹ * x * k := by rw [h1]
    · intro hy
      refine ⟨k * y * k⁻¹, ?_, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
      rw [hC, hk, conj_mul_conj_inv_apply]
      have : k⁻¹ * (k * y * k⁻¹) * k = y := by group
      rw [this, hy]
  have hB : B3Fix (g2Incl σ).range := by
    haveI : CharP K 2 := ringChar.of_eq hK2
    haveI : CharP (fixSubfield σ) 2 :=
      RingHom.charP (fixSubfield σ).subtype (fixSubfield σ).subtype_injective 2
    have hk₀ : ringChar (fixSubfield σ) = 2 := ringChar.eq _ 2
    have hk₀3 : ringChar (fixSubfield σ) ≠ 3 := by rw [hk₀]; norm_num
    rcases card_eq_two_or_four_le_of_ringChar_two hk₀ with h2 | h4
    · refine b3Fix_of_card_dvd (M := 12096) ?_ fun a ha => not_suzukiOrder_dvd_12096 ha
      have : Nat.card (g2Incl σ).range = Nat.card (adjointGroup .G2 (fixSubfield σ)) :=
        (Nat.card_congr (MonoidHom.ofInjective (g2Incl_injective σ)).toEquiv).symm
      rw [this, CFSG.ComponentClassification.ExcSelector.card_adjointGroup_G2_two h2]
    · have hs : IsSimpleGroup (adjointGroup .G2 (fixSubfield σ)) :=
        CFSG.QuasithinUnique.Id2519.isSimpleGroup_adjointGroup_g2 (by omega)
      have hs' : IsSimpleGroup (g2Incl σ).range :=
        (MonoidHom.ofInjective (g2Incl_injective σ)).symm.isSimpleGroup
      obtain ⟨x, hx1, hx3⟩ := exists_order_three_adjointG2 (K := fixSubfield σ) hk₀3
      refine b3Fix_of_perfSubnormalBot (perfSubnormalBot_of_isSimpleGroup hs'
        ⟨g2Incl σ x, ⟨x, rfl⟩, fun h => hx1 (g2Incl_injective σ (h.trans (map_one _).symm)), ?_⟩)
      rw [← map_pow, hx3, map_one]
  exact b3Fix_of_map (MulAut.conj k⁻¹ : adjointGroup .G2 K ≃* _) (by rw [hmap]; exact hB)

theorem threePrimeB3_adjointG2_charTwo (hK2 : ringChar K = 2) (hK4 : 4 ≤ Nat.card K) :
    ThreePrimeB3 (adjointGroup .G2 K) := by
  refine threePrimeB3_of_b3Fix fun β hβ C hC => ?_
  by_cases hin : IsInnerAut β
  · exact b3Fix_g2_of_inner (by rw [hK2]; norm_num) hK4 hβ hin hC
  · exact b3Fix_g2_of_outer hK2 hK4 hβ hin hC

theorem threePrimeB3_adjointG2_of_prime (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K) {p : ℕ}
    (hp : p.Prime) (hKp : Nat.card K = p) : ThreePrimeB3 (adjointGroup .G2 K) := by
  refine threePrimeB3_of_b3Fix fun β hβ C hC => ?_
  refine b3Fix_g2_of_inner hK3 hK4 hβ ?_ hC
  by_contra hout
  obtain ⟨σ, hσ, -⟩ := g2_order_three_field_descent hK3 hK4 hβ hout
  exact orderOf_ne_three_of_card_prime hp hKp σ hσ

theorem threePrimeB3_of_chevalleyG2_even {X : Type} [Group X] {f : ℕ}
    (h : ChevalleyExceptionalModel X .G2 2 f) : ThreePrimeB3 X := by
  obtain ⟨⟨-, hf, -, h3⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hK2 : ringChar K = 2 := ringChar_eq_of_card_pow Nat.prime_two hK
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    by_cases hf2 : 2 ≤ f
    · calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    · have : f = 1 := by omega
      subst this
      norm_num at h3
  exact threePrimeB3_of_mulEquiv (e.trans (CFSG.RankThree.Chevalley.adjointQuotientEquiv .G2 K))
    (threePrimeB3_adjointG2_charTwo hK2 hK4)

theorem threePrimeB3_of_chevalleyG2_odd {X : Type} [Group X] {p : ℕ} (hp3 : 3 < p)
    (h : ChevalleyExceptionalModel X .G2 p 1) : ThreePrimeB3 X := by
  obtain ⟨⟨hp, -, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  rw [pow_one] at hK
  have hK3 : ringChar K ≠ 3 := by
    rw [ringChar_eq_of_card_pow (f := 1) hp (by rw [hK, pow_one])]
    omega
  exact threePrimeB3_of_mulEquiv (e.trans (CFSG.RankThree.Chevalley.adjointQuotientEquiv .G2 K))
    (threePrimeB3_adjointG2_of_prime hK3 (by omega) hp hK)

end Certs

end CFSG.RankThree.PartTwo.Sec6.BThreeCensus
