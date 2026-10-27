module

public import CFSG.LieType.BorelTits.FormFlag

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.LieType.BorelTits Module

universe u v w

section Flag

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V] {H : Type w} [Group H]

theorem card_generalLinearGroup [Fintype K] {M : Type*} [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    {n : ℕ} (hn : finrank K M = n) :
    Nat.card (LinearMap.GeneralLinearGroup K M) =
      ∏ i : Fin n, (Fintype.card K ^ n - Fintype.card K ^ (i : ℕ)) := by
  let b := Module.finBasisOfFinrankEq K M hn
  rw [Nat.card_congr (LinearMap.GeneralLinearGroup.congrLinearEquiv b.equivFun).toEquiv,
    ← Nat.card_congr (Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := K)).toEquiv,
    Matrix.card_GL_field]

theorem finite_generalLinearGroup [Finite K] {M : Type*} [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] : Finite (LinearMap.GeneralLinearGroup K M) := by
  haveI : Fintype K := Fintype.ofFinite K
  let b := Module.finBasis K M
  exact Finite.of_equiv _ ((Matrix.GeneralLinearGroup.toLin (n := Fin (finrank K M)) (R := K)).toEquiv.trans
    (LinearMap.GeneralLinearGroup.congrLinearEquiv b.equivFun).symm.toEquiv)

theorem one_add_pow_four_of_cube [CharP K 2] (N : Module.End K V) (hN : N ^ 3 = 0) : (1 + N) ^ 4 = 1 := by
  have h2 : (2 : Module.End K V) = 0 := by
    have hK : (2 : K) = 0 := CharTwo.two_eq_zero
    have : algebraMap K (Module.End K V) 2 = 2 := map_ofNat _ 2
    rw [← this, hK, map_zero]
  have hdouble : ∀ X : Module.End K V, X + X = 0 := fun X => by rw [← two_mul, h2, zero_mul]
  have hsq : ∀ X : Module.End K V, (1 + X) ^ 2 = 1 + X * X := by
    intro X
    rw [sq, add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, add_assoc, ← add_assoc X X,
      hdouble, zero_add]
  have hN4 : N * N * (N * N) = 0 := by
    have : N * N * (N * N) = N ^ 3 * N := by rw [pow_succ, pow_succ, pow_one]; noncomm_ring
    rw [this, hN, zero_mul]
  calc (1 + N) ^ 4 = ((1 + N) ^ 2) ^ 2 := by rw [← pow_mul]
    _ = 1 + N * N * (N * N) := by rw [hsq, hsq]
    _ = 1 := by rw [hN4, add_zero]

theorem pow_four_eq_one [CharP K 2] {F : ReflForm K V} {ρ : H →* Module.End K V} (hρ : IsIsometric F ρ)
    {W : Submodule K V} {g : H} (hgW : ∀ w ∈ W, ρ g w = w) (hgP : ∀ v ∈ F.perp W, ρ g v - v ∈ W) :
    ρ (g ^ 4) = 1 := by
  set N : Module.End K V := ρ g - 1 with hNdef
  have hNv : ∀ v, N v = ρ g v - v := fun v => by simp [hNdef]
  have h1 : ∀ v, N v ∈ F.perp W := by
    intro v w hw
    rw [hNv, F.β_sub_right]
    have := hρ g w v
    rw [hgW w hw] at this
    rw [this, sub_self]
  have h3 : ∀ x ∈ W, N x = 0 := fun x hx => by rw [hNv, hgW x hx, sub_self]
  have hN3 : N ^ 3 = 0 := by
    ext v
    have hv : (N ^ 3) v = N (N (N v)) := by
      rw [pow_succ, pow_succ, pow_one, Module.End.mul_apply, Module.End.mul_apply]
    rw [hv, LinearMap.zero_apply]
    refine h3 _ ?_
    rw [hNv]
    exact hgP _ (h1 v)
  have hρg : ρ g = 1 + N := by rw [hNdef, add_sub_cancel]
  rw [map_pow, hρg, one_add_pow_four_of_cube N hN3]

theorem card_dvd_of_stabilizes [CharP K 2] {F : ReflForm K V} {ρ : H →* Module.End K V}
    (hρ : IsIsometric F ρ) (hinj : Function.Injective ρ) {W : Submodule K V} {R : Subgroup H} [Finite R]
    [Finite (LinearMap.GeneralLinearGroup K W)]
    [Finite (LinearMap.GeneralLinearGroup K (↥(F.perp W) ⧸ W.comap (F.perp W).subtype))]
    (hodd : Odd (Nat.card R)) (hRW : ∀ r ∈ R, ∀ w ∈ W, ρ r w ∈ W) :
    Nat.card R ∣ Nat.card (LinearMap.GeneralLinearGroup K W) *
      Nat.card (LinearMap.GeneralLinearGroup K (↥(F.perp W) ⧸ W.comap (F.perp W).subtype)) := by
  classical
  have hRP : ∀ r ∈ R, ∀ v ∈ F.perp W, ρ r v ∈ F.perp W := fun r hr v hv =>
    hρ.apply_mem_perp_of_forall (fun w hw => hRW r⁻¹ (R.inv_mem hr) w hw) hv
  set W' : Submodule K ↥(F.perp W) := W.comap (F.perp W).subtype with hW'
  let α₁ : ↥R →* Module.End K W :=
    { toFun := fun r => (ρ r).restrict (hRW r r.2)
      map_one' := by ext x; simp
      map_mul' := fun r s => by ext x; simp [Module.End.mul_apply] }
  let β : ↥R →* Module.End K ↥(F.perp W) :=
    { toFun := fun r => (ρ r).restrict (hRP r r.2)
      map_one' := by ext x; simp
      map_mul' := fun r s => by ext x; simp [Module.End.mul_apply] }
  have hβW' : ∀ r : ↥R, W' ≤ W'.comap (β r) := by
    intro r x hx
    change (((β r) x : ↥(F.perp W)) : V) ∈ W
    exact hRW r r.2 _ hx
  let α₂ : ↥R →* Module.End K (↥(F.perp W) ⧸ W') :=
    { toFun := fun r => W'.mapQ W' (β r) (hβW' r)
      map_one' := by
        ext x
        simp
      map_mul' := fun r s => by
        ext x
        simp [Module.End.mul_apply] }
  let α : ↥R →* LinearMap.GeneralLinearGroup K W ×
      LinearMap.GeneralLinearGroup K (↥(F.perp W) ⧸ W') :=
    α₁.toHomUnits.prod α₂.toHomUnits
  have hinjα : Function.Injective α := by
    rw [injective_iff_map_eq_one]
    intro r hr
    have h1 : α₁ r = 1 := by
      have := congrArg (fun x => ((x.1 : LinearMap.GeneralLinearGroup K W) : Module.End K W)) hr
      simpa [α] using this
    have h2 : α₂ r = 1 := by
      have := congrArg (fun x => ((x.2 : LinearMap.GeneralLinearGroup K (↥(F.perp W) ⧸ W')) :
        Module.End K (↥(F.perp W) ⧸ W'))) hr
      simpa [α] using this
    have hgW : ∀ w ∈ W, ρ r w = w := by
      intro w hw
      have := congrArg (fun f : Module.End K W => ((f ⟨w, hw⟩ : W) : V)) h1
      simpa [α₁] using this
    have hgP : ∀ v ∈ F.perp W, ρ r v - v ∈ W := by
      intro v hv
      have := congrArg (fun f : Module.End K (↥(F.perp W) ⧸ W') => f (Submodule.Quotient.mk ⟨v, hv⟩)) h2
      simp only [α₂, MonoidHom.coe_mk, OneHom.coe_mk, Submodule.mapQ_apply, Module.End.one_apply] at this
      rw [Submodule.Quotient.eq] at this
      have hmem : ((β r ⟨v, hv⟩ - ⟨v, hv⟩ : ↥(F.perp W)) : V) ∈ W := this
      simpa [β] using hmem
    have h4 : ((r : H)) ^ 4 = 1 := hinj (by rw [pow_four_eq_one hρ hgW hgP, map_one])
    have h4' : r ^ 4 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, h4, Subgroup.coe_one])
    have hcard : r ^ Nat.card R = 1 := pow_card_eq_one'
    have hord : orderOf r ∣ Nat.gcd 4 (Nat.card R) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h4') (orderOf_dvd_of_pow_eq_one hcard)
    have hgcd : Nat.gcd 4 (Nat.card R) = 1 := by
      have h22 : Nat.Coprime 2 (Nat.card R) := (Nat.coprime_two_left).2 hodd
      have : Nat.Coprime (2 ^ 2) (Nat.card R) := Nat.Coprime.pow_left 2 h22
      simpa using this
    rw [hgcd, Nat.dvd_one, orderOf_eq_one_iff] at hord
    exact hord
  have h := Subgroup.card_dvd_of_injective α hinjα
  rwa [Nat.card_prod] at h

theorem card_dvd_prod_of_stabilizes [Fintype K] [FiniteDimensional K V] [CharP K 2] {F : ReflForm K V}
    {ρ : H →* Module.End K V} (hρ : IsIsometric F ρ) (hinj : Function.Injective ρ) {W : Submodule K V}
    (hWt : F.IsTotallyIsotropic W) {R : Subgroup H} [Finite R] (hodd : Odd (Nat.card R))
    (hRW : ∀ r ∈ R, ∀ w ∈ W, ρ r w ∈ W) {n a : ℕ} (hn : finrank K V = n) (ha : finrank K W = a) :
    Nat.card R ∣ (∏ i : Fin a, (Fintype.card K ^ a - Fintype.card K ^ (i : ℕ))) *
      ∏ i : Fin (n - 2 * a), (Fintype.card K ^ (n - 2 * a) - Fintype.card K ^ (i : ℕ)) := by
  set W' : Submodule K ↥(F.perp W) := W.comap (F.perp W).subtype with hW'
  have hperp : finrank K (F.perp W) = n - a := by
    have := F.finrank_perp W
    omega
  have hW'dim : finrank K W' = a := by
    rw [← ha]
    exact (Submodule.comapSubtypeEquivOfLe hWt).finrank_eq
  have hQ : finrank K (↥(F.perp W) ⧸ W') = n - 2 * a := by
    have := Submodule.finrank_quotient_add_finrank W'
    omega
  haveI : Finite (LinearMap.GeneralLinearGroup K W) := finite_generalLinearGroup
  haveI : Finite (LinearMap.GeneralLinearGroup K (↥(F.perp W) ⧸ W')) := finite_generalLinearGroup
  have h := card_dvd_of_stabilizes hρ hinj (R := R) hodd hRW
  rwa [card_generalLinearGroup ha, card_generalLinearGroup hQ] at h

end Flag

end CFSG.LocalAnalysis.UniquenessCase.UCK
