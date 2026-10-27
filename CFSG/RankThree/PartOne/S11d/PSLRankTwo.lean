module

public import CFSG.RankThree.PartOne.S11d.RankTwoLinear
public import CFSG.RankThree.PartOne.S11c.CentralWitness
public import CFSG.RankThree.PartOne.S11c.Sec66TLift
public import CFSG.RankThree.PartOne.LIT.RankMatrix
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation

public section

namespace CFSG.RankThree.PartOne

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag Subgroup CFSG
open CFSG.RankThree.PartOne.LIT (glAut glAut_injective)

section QSide

variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem not_dvd_card_of_charTwo [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card K := by
  intro hdvd
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hf, hcard⟩ := FiniteField.card K 2
  have : Nat.card K = 2 ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hcard
  rw [this] at hdvd
  have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd)
  exact hp2 this

theorem not_dvd_card_scalars_psl [NeZero n] {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓK : ¬ ℓ ∣ Nat.card Kˣ) :
    ¬ ℓ ∣ Nat.card (scalars n K) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  intro hdvd
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := scalars n K) ℓ hdvd
  obtain ⟨c, hc, hmat⟩ := z.2
  apply hℓK
  have hzp : z ^ ℓ = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hz1 : (z : Matrix.SpecialLinearGroup (Fin n) K) ≠ 1 := by
    intro h
    have : z = 1 := Subtype.ext h
    rw [this, orderOf_one] at hz
    exact hℓ.one_lt.ne hz
  have hcp : c ^ ℓ = 1 := by
    have h2 : ((z : Matrix.SpecialLinearGroup (Fin n) K)) ^ ℓ = 1 := by
      rw [← Subgroup.coe_pow, hzp]
      rfl
    have h3 : ((z : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ ℓ = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_pow, h2]
      rfl
    rw [hmat, ← map_pow] at h3
    have h4 : ((c : K) ^ ℓ) = 1 := by
      have i0 : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
      have h5 := congrFun (congrFun h3 i0) i0
      simpa [Matrix.scalar_apply, Matrix.diagonal_apply_eq] using h5
    exact Units.ext (by simpa using h4)
  have hc1 : c ≠ 1 := by
    intro h
    apply hz1
    apply Subtype.ext
    rw [hmat, h, Units.val_one, map_one]
    rfl
  have hordc : orderOf c = ℓ := orderOf_eq_prime hcp hc1
  rw [← hordc]
  exact orderOf_dvd_natCard c

theorem two_mul_le_of_pRank_projectiveSL [NeZero n] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card Kˣ) {e : ℕ}
    (he : ∀ j : ℕ, 1 ≤ j → p ∣ Nat.card K ^ j - 1 → e ≤ j)
    (h2 : 2 ≤ CFSG.pRank p (projectiveSL n K)) : 2 * e ≤ n := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have hpQ := not_dvd_card_of_charTwo (K := K) hp hp2
  have hrK := LIT.natCast_ne_zero_of_charTwo (F := K) hp hp2
  obtain ⟨A, hAe, hAc⟩ := exists_isElementaryAbelian_card_pRank (H := projectiveSL n K) hp.one_lt
  have hAcard : p ^ 2 ≤ Nat.card A := by
    rw [hAc]
    exact Nat.pow_le_pow_right hp.pos h2
  have hZ : ¬ p ∣ Nat.card (scalars n K) := not_dvd_card_scalars_psl hp hpK
  have hcop : Nat.Coprime (Nat.card (scalars n K)) (Nat.card A) := by
    rw [hAc]
    exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hZ).symm
  obtain ⟨R, hRmap, hRcard, hRinj⟩ :=
    CFSG.RankThree.PartOne.Sec66T.exists_lift_of_central_coprime (scalars n K) hcop A rfl
  have hmemA : ∀ x ∈ R, QuotientGroup.mk' (scalars n K) x ∈ A := fun x hx =>
    hRmap ▸ Subgroup.mem_map_of_mem _ hx
  have hRcomm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := by
    intro x hx y hy
    refine hRinj _ (R.mul_mem hx hy) _ (R.mul_mem hy hx) ?_
    have h1 := hAe.is_comm.comm ⟨QuotientGroup.mk' (scalars n K) x, hmemA x hx⟩
      ⟨QuotientGroup.mk' (scalars n K) y, hmemA y hy⟩
    rw [map_mul, map_mul]
    exact congrArg Subtype.val h1
  have hRexp : ∀ x ∈ R, x ^ p = 1 := by
    intro x hx
    refine hRinj _ (R.pow_mem hx p) 1 R.one_mem ?_
    rw [map_pow, map_one]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian _ (hmemA x hx)
  let ι : Matrix.SpecialLinearGroup (Fin n) K →* ((Fin n → K) ≃ₗ[K] (Fin n → K)) :=
    (glAut (Fin n) K).comp Matrix.SpecialLinearGroup.toGL
  have hι : Function.Injective ι :=
    glAut_injective.comp Matrix.SpecialLinearGroup.toGL_injective
  let E : Subgroup ((Fin n → K) ≃ₗ[K] (Fin n → K)) := R.map ι
  have hEfin : Finite E := Finite.of_equiv R (Subgroup.equivMapOfInjective R ι hι).toEquiv
  have hEcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hRcomm a ha b hb]
  have hEexp : ∀ g ∈ E, g ^ p = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hRexp a ha, map_one]
  have hEcard : p ^ 2 ≤ Nat.card E := by
    have : Nat.card E = Nat.card R :=
      Nat.card_congr (Subgroup.equivMapOfInjective R ι hι).symm.toEquiv
    rw [this, hRcard]
    exact hAcard
  have hd : ∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W]
      (g : W ≃ₗ[K] W), g ^ p = 1 → g ≠ 1 → e ≤ Module.finrank K W := by
    intro W _ _ _ g hg hg1
    obtain ⟨j, hj1, hjm, hdvd⟩ := LIT.exists_dim_of_order_dvd hp
      (by rwa [← Nat.card_eq_fintype_card]) g hg hg1
    exact (he j hj1 (by rwa [Nat.card_eq_fintype_card])).trans hjm
  have := LIT.two_mul_le_finrank hp hrK hd E hEcomm hEexp hEcard
  rwa [Module.finrank_fin_fun] at this

end QSide

end CFSG.RankThree.PartOne
