module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley


private theorem q2cF4R_conj_injective {R : Type*} [Group R] (hZ : Subgroup.center R = ⊥) :
    Function.Injective (MulAut.conj : R →* MulAut R) := by
  intro x y hxy
  have h1 : MulAut.conj (x⁻¹ * y) = 1 := by
    rw [map_mul, map_inv, hxy, inv_mul_cancel]
  have hmem : x⁻¹ * y ∈ Subgroup.center R := by
    rw [Subgroup.mem_center_iff]
    intro r
    have h2 : MulAut.conj (x⁻¹ * y) r = r := by
      rw [h1]; rfl
    rw [MulAut.conj_apply] at h2
    calc r * (x⁻¹ * y) = ((x⁻¹ * y) * r * (x⁻¹ * y)⁻¹) * (x⁻¹ * y) := by rw [h2]
      _ = (x⁻¹ * y) * r := by group
  rw [hZ, Subgroup.mem_bot] at hmem
  have hyx : y = x := by
    calc y = x * (x⁻¹ * y) := by group
      _ = x := by rw [hmem, mul_one]
  exact hyx.symm

private theorem q2cF4R_card_le_of_dvd_sub_one {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1)
    {E : Subgroup (adjointGroup .F4 K)} (hE : IsElemAbelian p E) : Nat.card E ≤ p ^ 4 := by
  rcases eq_or_ne p 3 with rfl | hp3
  · exact GGF4ToralRankInput.card_le hp hpq (TableBF4.ggF4ToralRankInput_three hpq) hE
  · exact GGF4ToralRankInput.card_le hp hpq
      (TableBF4.ggF4ToralRankInput_of_five_le hp
        (hp.five_le_of_ne_two_of_ne_three hp2 hp3) hpq) hE

private theorem q2cF4R_card_le_of_card_two {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {E : Subgroup (adjointGroup .F4 K)} (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 3 ^ 4 :=
  TableBF4Two.card_le_adjointF4 hK hE

theorem q2c_F4_rank {p d : ℕ} {lab : LargeEvenLabel} (hlab : lab.tag = .F4) (hp : p.Prime)
    (hp2 : p ≠ 2) (hsplit : LargeEvenSplit p lab) (hpd : p ∣ d) :
    LargeEvenLabelAll lab (fun R _ I _ =>
      ∀ A : Subgroup (MulAut R), IsElemAbelian p A → (∀ a ∈ A, a ∈ I) →
      (∀ r : ℕ, GGTorusLift p r R → p ^ r ≤ Nat.card A) →
      p ^ (d - 1) ≤ Nat.card A → Nat.card A ≤ p ^ d →
      (p = 5 ∧ d = 5) ∨ (lab.n = 1 ∧ p = 3 ∧ d = 3)) := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hlab
  subst hlab
  have hsplt : p ∣ 2 ^ n - 1 ∨ (n = 1 ∧ p = 3) :=
    (largeEvenSplit_F4_iff (lab := ⟨.F4, l, n⟩) rfl).mp hsplit
  haveI : Fact p.Prime := ⟨hp⟩
  intro Q hQ
  obtain ⟨K, _, _, hKcard, hQ'⟩ := hQ
  haveI : CharP K 2 := charP_two_of_card hKcard
  refine ⟨K, inferInstance, inferInstance, hKcard, hQ', ?_⟩
  intro A hA hAI hbig hlo hup
  have hZ : Subgroup.center (TableBF4.RecipeGroup K) = ⊥ :=
    TableBF4.center_recipeGroup_eq_bot K
  let f : TableBF4.RecipeGroup K →* MulAut (TableBF4.RecipeGroup K) := MulAut.conj
  have hf : Function.Injective f := q2cF4R_conj_injective hZ
  have hArange : A ≤ f.range := fun a ha => TableBF4.idImage_subset_inn K (hAI a ha)
  let A₀ : Subgroup (TableBF4.RecipeGroup K) := A.comap f
  have hcardA₀ : Nat.card A₀ = Nat.card A := by
    have hmap : A₀.map f = A := Subgroup.map_comap_eq_self hArange
    calc Nat.card A₀ = Nat.card (A₀.map f) := (Subgroup.card_map_of_injective hf).symm
      _ = Nat.card A :=
        congrArg (fun H : Subgroup (MulAut (TableBF4.RecipeGroup K)) => Nat.card ↥H) hmap
  have hA₀ : IsElemAbelian p A₀ := hA.comap hf
  let e : TableBF4.RecipeGroup K ≃* adjointGroup .F4 K := TableBF4.recipeEquiv K
  let A₁ : Subgroup (adjointGroup .F4 K) := A₀.map e.toMonoidHom
  have hA₁ : IsElemAbelian p A₁ := CFSG.SectionRank.isElemAbelian_map hA₀ e.toMonoidHom
  have hcardA₁ : Nat.card A₁ = Nat.card A₀ := Subgroup.card_map_of_injective e.injective
  have hcard_le : Nat.card A ≤ p ^ 4 := by
    rw [← hcardA₀, ← hcardA₁]
    rcases hsplt with hpq | ⟨hn1, hp3⟩
    · have hpq' : p ∣ Nat.card K - 1 := by rw [hKcard]; exact hpq
      exact q2cF4R_card_le_of_dvd_sub_one hp hp2 hpq' hA₁
    · have hK2 : Nat.card K = 2 := by rw [hKcard, hn1]; norm_num
      have h3 := q2cF4R_card_le_of_card_two hK2 (E := A₁) (hp3 ▸ hA₁)
      rw [hp3]
      exact h3
  rcases hsplt with hpq | ⟨hn1, hp3⟩
  · have hpq' : p ∣ Nat.card K - 1 := by rw [hKcard]; exact hpq
    have hlower : p ^ 4 ≤ Nat.card A :=
      hbig 4 (TableBF4.ggTorusLift_F4 hp hp2 hpq')
    have hd_ge : 4 ≤ d := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hlower.trans hup)
    have hd_le : d - 1 ≤ 4 := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hlo.trans hcard_le)
    have hd : d = 4 ∨ d = 5 := by omega
    rcases hd with rfl | rfl
    · exfalso
      have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (m := 2) (n := 2)
        (by rw [show (2 : ℕ) ^ 2 = 4 by norm_num]; exact hpd)
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
    · exact Or.inl ⟨(Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp hpd, rfl⟩
  · have hlower : p ^ 3 ≤ Nat.card A :=
      hbig 3 (hp3.symm ▸ TableBF4Two.ggTorusLift_F4Two (K := K))
    have hd_ge : 3 ≤ d := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hlower.trans hup)
    have hd_le : d - 1 ≤ 4 := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hlo.trans hcard_le)
    have hd : d = 3 := by
      have hcases : d = 3 ∨ d = 4 ∨ d = 5 := by omega
      rcases hcases with rfl | rfl | rfl
      · rfl
      · rw [hp3] at hpd; exact absurd hpd (by norm_num)
      · rw [hp3] at hpd; exact absurd hpd (by norm_num)
    exact Or.inr ⟨hn1, hp3, hd⟩

end CFSG.StandardType
