module

public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7Defs
public import CFSG.LieType.Chevalley.EvenF4AutomorphismNormalForm
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Open

private theorem lr2of4_conj_injective {S : Type} [Group S]
    (hZ : Subgroup.center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  intro a b hab
  have h1 : MulAut.conj (b⁻¹ * a) = 1 := by
    rw [map_mul, map_inv, hab, inv_mul_cancel]
  have h2 : b⁻¹ * a ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro w
    have h3 := congrArg (fun f : MulAut S => f w) h1
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.one_apply] at h3
    have h4 : (b⁻¹ * a) * w = w * (b⁻¹ * a) := by
      have h5 := congrArg (fun t => t * (b⁻¹ * a)) h3
      simpa [mul_assoc] using h5
    exact h4.symm
  rw [hZ, Subgroup.mem_bot] at h2
  exact (inv_mul_eq_one.mp h2).symm

private theorem lr2of4_factorization_eq_of_center_bot
    {S : Type} [Group S] [Finite S] {n : ℕ} (hZ : Subgroup.center S = ⊥)
    (Θ : MulAut S →* Multiplicative (ZMod n))
    (hsurj : Function.Surjective Θ)
    (hker : Θ.ker = (MulAut.conj : S →* MulAut S).range)
    (h7n : ¬ 7 ∣ n) :
    (Nat.card (MulAut S)).factorization 7 = (Nat.card S).factorization 7 := by
  haveI : Nonempty S := ⟨1⟩
  have hinj := lr2of4_conj_injective hZ
  have hn : n ≠ 0 := by
    rintro rfl
    exact h7n (dvd_zero 7)
  have hker_card : Nat.card Θ.ker = Nat.card S := by
    rw [hker]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hrange_card : Nat.card Θ.range = n := by
    rw [MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top]
    exact (Nat.card_congr (Multiplicative.toAdd (α := ZMod n))).trans (Nat.card_zmod n)
  have hcard : Nat.card (MulAut S) = Nat.card S * n := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup Θ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange Θ).toEquiv, hker_card,
      hrange_card] at h
    exact h.trans (mul_comm _ _)
  rw [hcard, Nat.factorization_mul (Nat.card_pos.ne') hn]
  simp [Nat.factorization_eq_zero_of_not_dvd h7n]

private theorem lr2opf4_card_mulAut_dvd_of_center_bot
    {S : Type} [Group S] {n : ℕ} (hZ : Subgroup.center S = ⊥)
    (Θ : MulAut S →* Multiplicative (ZMod n))
    (hsurj : Function.Surjective Θ)
    (hker : Θ.ker = (MulAut.conj : S →* MulAut S).range) :
    Nat.card (MulAut S) ∣ n * Nat.card S := by
  haveI : Nonempty S := ⟨1⟩
  have hinj := lr2of4_conj_injective hZ
  have hker_card : Nat.card Θ.ker = Nat.card S := by
    rw [hker]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hrange_card : Nat.card Θ.range = n := by
    rw [MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top]
    exact (Nat.card_congr (Multiplicative.toAdd (α := ZMod n))).trans (Nat.card_zmod n)
  have hcard : Nat.card (MulAut S) = Nat.card S * n := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup Θ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange Θ).toEquiv, hker_card,
      hrange_card] at h
    exact h.trans (mul_comm _ _)
  rw [hcard, mul_comm (Nat.card S) n]

theorem ord7_card_mulAut_dvd_F4
    {f : ℕ} {R : Type} [Group R] (hm : LieModel R .F4 0 2 f) :
    Nat.card (MulAut R) ∣ (2 * f) * Nat.card R := by
  rw [CFSG.Blueprint.LieModel] at hm
  rcases hm with ⟨hmem, _⟩ | ⟨-, hmem, hm⟩ | ⟨-, hmem, _⟩ | ⟨-, htag, _⟩
  · exact absurd hmem (by simp [classicalTags])
  · obtain ⟨-, hum⟩ := hm
    obtain ⟨K, hKfield, hKfin, hKcard, ⟨eR0⟩⟩ := hum
    letI := hKfield
    letI := hKfin
    have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
    have hf : 1 ≤ f := by
      rcases Nat.eq_zero_or_pos f with h | h
      · rw [h, pow_zero] at hKcard
        omega
      · exact h
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP K 2 := by
      letI : Fintype K := Fintype.ofFinite K
      exact charP_of_card_eq_prime_pow (p := 2) (f := f) (by
        rw [← Nat.card_eq_fintype_card]
        exact hKcard)
    haveI : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := inferInstanceAs (CharP K 2)
    obtain ⟨-, -, ⟨Θ, -, hsurj, hker⟩, -⟩ :=
      CFSG.LieType.Chevalley.even_F4_exact_automorphism_normal_form (f := f) hf K hKcard
    have hdvd :
        Nat.card (MulAut (CFSG.Blueprint.Chevalley.adjointGroup .F4 K)) ∣
          (2 * f) * Nat.card (CFSG.Blueprint.Chevalley.adjointGroup .F4 K) :=
      lr2opf4_card_mulAut_dvd_of_center_bot
        (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (K := K)) Θ hsurj hker
    let eAdj : AdjointQuotient .F4 K ≃* CFSG.Blueprint.Chevalley.adjointGroup .F4 K :=
      (QuotientGroup.quotientMulEquivOfEq (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (K := K))).trans
        QuotientGroup.quotientBot
    let eR : R ≃* CFSG.Blueprint.Chevalley.adjointGroup .F4 K := eR0.trans eAdj
    have hcardMul : Nat.card (MulAut R) =
        Nat.card (MulAut (CFSG.Blueprint.Chevalley.adjointGroup .F4 K)) :=
      Nat.card_congr (MulAut.congr eR).toEquiv
    have hcardR : Nat.card R = Nat.card (CFSG.Blueprint.Chevalley.adjointGroup .F4 K) :=
      Nat.card_congr eR.toEquiv
    rw [hcardMul, hcardR]
    exact hdvd
  · exact absurd hmem (by simp [reeTitsTags])
  · exact absurd htag (by simp)

theorem ord7Param_F4
    {f : ℕ} (h7 : ¬ 7 ∣ f) : Ord7Param .F4 0 2 f := by
  intro R _ _ hR hmodel
  rw [CFSG.Blueprint.LieModel] at hmodel
  rcases hmodel with ⟨hmem, _⟩ | ⟨-, hmem, hm⟩ | ⟨-, hmem, _⟩ | ⟨-, htag, _⟩
  · exact absurd hmem (by simp [classicalTags])
  · obtain ⟨-, hum⟩ := hm
    obtain ⟨K, hKfield, hKfin, hKcard, ⟨eR0⟩⟩ := hum
    letI := hKfield
    letI := hKfin
    have hf : 1 ≤ f := by
      rcases Nat.eq_zero_or_pos f with h | h
      · exact absurd (h ▸ dvd_zero 7) h7
      · exact h
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP K 2 := by
      letI : Fintype K := Fintype.ofFinite K
      exact charP_of_card_eq_prime_pow (p := 2) (f := f) (by
        rw [← Nat.card_eq_fintype_card]
        exact hKcard)
    haveI : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := inferInstanceAs (CharP K 2)
    obtain ⟨-, -, ⟨Θ, -, hsurj, hker⟩, -⟩ :=
      CFSG.LieType.Chevalley.even_F4_exact_automorphism_normal_form (f := f) hf K hKcard
    have hfac : (Nat.card (MulAut (CFSG.Blueprint.Chevalley.adjointGroup .F4 K))).factorization 7 =
        (Nat.card (CFSG.Blueprint.Chevalley.adjointGroup .F4 K)).factorization 7 :=
      lr2of4_factorization_eq_of_center_bot (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (K := K)) Θ hsurj hker
        (by
          intro h
          exact h7 ((Nat.prime_seven.dvd_mul.mp h).resolve_left (by norm_num)))
    let eAdj : AdjointQuotient .F4 K ≃* CFSG.Blueprint.Chevalley.adjointGroup .F4 K :=
      (QuotientGroup.quotientMulEquivOfEq (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (K := K))).trans
        QuotientGroup.quotientBot
    let eR : R ≃* CFSG.Blueprint.Chevalley.adjointGroup .F4 K := eR0.trans eAdj
    have hcardMul : Nat.card (MulAut R) = Nat.card (MulAut (CFSG.Blueprint.Chevalley.adjointGroup .F4 K)) :=
      Nat.card_congr (MulAut.congr eR).toEquiv
    have hcardR : Nat.card R = Nat.card (CFSG.Blueprint.Chevalley.adjointGroup .F4 K) :=
      Nat.card_congr eR.toEquiv
    rw [hcardMul, hcardR, hfac]
  · exact absurd hmem (by simp [reeTitsTags])
  · exact absurd htag (by simp)

end CFSG.StandardType.SporadicShape
