module

public import CFSG.RankThree.PartTwo.Sec4.Item419Res3ProofAutThree
public import CFSG.RankThree.PartTwo.Sec4.HeringK419Gen
public import CFSG.RankThree.PartTwo.Sec4.Item47WitnessG2
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof
import CFSG.Quasithin.Background.E6NineteenC
import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofG2Ord3

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open Item419Res3 HeringK419

namespace HeringK419G2

section Certs


theorem exists_involution_commute {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK4 : 4 ≤ Nat.card K) {z : adjointGroup .G2 K} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    ∃ u : adjointGroup .G2 K, orderOf u = 2 ∧ u * z = z * u := by
  have hKchar : ringChar K ≠ 3 := by rw [ringChar.eq K 2]; norm_num
  obtain ⟨g, hg⟩ := Sec11.KS11Lie7Proof.g2ThreeConjSL2_holds K hKchar hK4 z hz3 hz1
  obtain ⟨j, hj1, hj2⟩ := Sec8.Item812Res8.exists_involution_sl2 K
  have key : ∀ u' : adjointGroup .G2 K, u' ^ 2 = 1 → u' ≠ 1 →
      u' * (g * z * g⁻¹) = (g * z * g⁻¹) * u' →
      ∃ u : adjointGroup .G2 K, orderOf u = 2 ∧ u * z = z * u := by
    intro u' hu'2 hu'1 hcomm
    refine ⟨g⁻¹ * u' * g, ?_, ?_⟩
    · refine orderOf_eq_prime ?_ ?_
      · calc (g⁻¹ * u' * g) ^ 2 = g⁻¹ * u' ^ 2 * g := by
              rw [sq, sq]; group
          _ = 1 := by rw [hu'2]; group
      · intro h
        apply hu'1
        calc u' = g * (g⁻¹ * u' * g) * g⁻¹ := by group
          _ = 1 := by rw [h]; group
    · calc (g⁻¹ * u' * g) * z = g⁻¹ * (u' * (g * z * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * z * g⁻¹) * u') * g := by rw [hcomm]
        _ = z * (g⁻¹ * u' * g) := by group
  rcases hg with hS | hL
  · obtain ⟨e⟩ := Sec11.KS11Lie4Proof.nonempty_mulEquiv_g2LongSL2 (K := K)
    refine key (e j : adjointGroup .G2 K) ?_ ?_ ?_
    · rw [← Subgroup.coe_pow, ← map_pow, hj2, map_one]
      rfl
    · intro h
      exact hj1 (EmbeddingLike.map_eq_one_iff.mp (Subtype.ext h))
    · exact (Sec11.KS11Lie4Proof.g2Short_commute_g2Long hS (e j).2).symm
  · obtain ⟨e⟩ := Sec11.KS11Lie4Proof.nonempty_mulEquiv_g2ShortSL2 (K := K)
    refine key (e j : adjointGroup .G2 K) ?_ ?_ ?_
    · rw [← Subgroup.coe_pow, ← map_pow, hj2, map_one]
      rfl
    · intro h
      exact hj1 (EmbeddingLike.map_eq_one_iff.mp (Subtype.ext h))
    · exact Sec11.KS11Lie4Proof.g2Short_commute_g2Long (e j).2 hL

theorem hasTwoWitness_g2 {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ n) {z : adjointGroup .G2 K} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    HasTwoWitness z := by
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨u, hu2, huz⟩ := exists_involution_commute hK4 hz3 hz1
  have hchar := Quasithin.E6.charTwo_adjointGroup (τ := .G2) (f := n) (by omega) hK u hu2
  have hcore := ClassicalInvolution.inf_centralizer_pCoreOf_le_of_isCharacteristicP hchar
  exact hasTwoWitness_of_charTwoLocal (Subgroup.centralizer {u}) hcore
    (Subgroup.mem_centralizer_singleton_iff.mpr huz.symm) hz3 hz1

theorem _root_.CFSG.RankThree.PartTwo.Sec4.k419AutThreeInnerG2_holds :
    K419AutThreeInnerG2 := by
  intro X _ n hX k hk3 hk1
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_G2 hX
  have hn : 2 ≤ n := by
    obtain ⟨⟨-, hn1, -, h3⟩, -⟩ := hX
    by_contra h
    interval_cases n <;> simp at h3 hn1
  exact hasTwoWitness_of_mulEquiv e (hasTwoWitness_g2 hn hK (by rw [← map_pow, hk3, map_one])
    (fun h => hk1 (EmbeddingLike.map_eq_one_iff.mp h)))


end Certs

section OuterCerts


theorem hasOuterWitness_g2FieldHom {K : Type} [Field K] [CharP K 2] {σ : K ≃+* K} (hσ : σ ≠ 1) :
    HasOuterWitness (g2FieldHom K σ) := by
  refine ⟨simplePosSubgroup Tag.G2 K WitnessG2.i₀, ?_, ?_, ?_⟩
  · intro g
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    obtain ⟨c, hc⟩ := (mem_simplePosSubgroup (i := WitnessG2.i₀)).1 g.2
    rw [pow_one, pow_two, Subgroup.coe_mul, Subgroup.coe_mul, hc, ← xUnit_add,
      CharTwo.add_self_eq_zero, xUnit_zero]
    rfl
  · intro u hu
    obtain ⟨c, hc⟩ := (mem_simplePosSubgroup (i := WitnessG2.i₀)).1 hu
    exact ⟨_, WitnessG2.coe_g2FieldHom_of_coe_eq_xUnit σ hc⟩
  · obtain ⟨c, hc⟩ : ∃ c : K, σ c ≠ c := by
      by_contra hcon
      push Not at hcon
      exact hσ (RingEquiv.ext hcon)
    refine ⟨⟨xUnit Tag.G2 K WitnessG2.i₀ c, xUnit_mem_adjointGroup WitnessG2.i₀ c⟩, ⟨c, rfl⟩,
      fun h => hc ?_⟩
    have h2 := congrArg (fun g : adjointGroup Tag.G2 K => ((g : ModGL Tag.G2 K) :
      Module.End K (RootModule Tag.G2 K))) h
    simp only at h2
    rw [WitnessG2.coe_g2FieldHom_of_coe_eq_xUnit σ (u := ⟨xUnit Tag.G2 K WitnessG2.i₀ c,
      xUnit_mem_adjointGroup WitnessG2.i₀ c⟩) rfl, coe_xUnit, coe_xUnit] at h2
    exact xOp_injective (τ := Tag.G2) (R := K) WitnessG2.i₀ h2

theorem _root_.CFSG.RankThree.PartTwo.Sec4.k419AutThreeOuterG2_holds :
    K419AutThreeOuterG2 := by
  intro X _ n hX β hβ3 hβ
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_G2 hX
  have hn : 2 ≤ n := by
    obtain ⟨⟨-, hn1, -, h3⟩, -⟩ := hX
    by_contra h
    interval_cases n <;> simp at h3 hn1
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hKchar : ringChar K ≠ 3 := by rw [ringChar.eq K 2]; norm_num
  refine hasOuterWitness_of_mulEquiv e ?_
  have hα3 : (MulAut.congr e β) ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  have hα : ¬ IsInnerAut (MulAut.congr e β) := fun h => hβ ((isInnerAut_congr e β).mp h)
  obtain ⟨σ, hσ3, k, hk⟩ := g2_order_three_field_descent hKchar hK4 hα3 hα
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ3
    omega
  exact hasOuterWitness_of_conj (MulAut.conj k) (g2FieldHom K σ) _ hk
    (hasOuterWitness_g2FieldHom hσ1)

end OuterCerts

end HeringK419G2

end CFSG.RankThree.PartTwo.Sec4
