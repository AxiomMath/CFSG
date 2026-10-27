module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeRank
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import CFSG.LocalAnalysis.StandardType.GGTableBRank

public section

namespace CFSG.StandardType.SmallRule

open Module CFSG.StandardType.TwoThree CFSG.Assembly TableB

variable {K : Type*} [Field K] [CharP K 2] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem exists_fixed_ne_zero (hK : Nat.card K = 2) {G : Type*} [Group G]
    (ρ : G →* (Module.End K V)ˣ) {P : Subgroup G} (hP : IsPGroup 2 P) {W : Submodule K V}
    (hW0 : W ≠ ⊥) (hW : ∀ p ∈ P, ∀ w ∈ W, (ρ p : Module.End K V) w ∈ W) :
    ∃ w ∈ W, w ≠ 0 ∧ ∀ p ∈ P, (ρ p : Module.End K V) w = w := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite V := Module.finite_of_finite K
  let act : MulAction P W :=
    { smul := fun p w => ⟨(ρ p : Module.End K V) w, hW p p.2 w w.2⟩
      one_smul := fun w => Subtype.ext (by
        change (ρ ((1 : P) : G) : Module.End K V) w = w
        rw [Subgroup.coe_one, map_one, Units.val_one, Module.End.one_apply])
      mul_smul := fun p q w => Subtype.ext (by
        change (ρ ((p * q : P) : G) : Module.End K V) w =
          (ρ (p : G) : Module.End K V) ((ρ (q : G) : Module.End K V) w)
        rw [Subgroup.coe_mul, map_mul, Units.val_mul, Module.End.mul_apply]) }
  have hdvd : 2 ∣ Nat.card W := by
    rw [Module.natCard_eq_pow_finrank (K := K), hK]
    have : finrank K W ≠ 0 := fun h => hW0 (Submodule.finrank_eq_zero.mp h)
    exact dvd_pow_self 2 this
  have h0 : (0 : W) ∈ MulAction.fixedPoints P W := fun p => Subtype.ext (map_zero _)
  obtain ⟨w, hw, hw0⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point W hdvd h0
  refine ⟨w, w.2, fun h => hw0 (Subtype.ext h.symm), fun p hp => ?_⟩
  have := hw ⟨p, hp⟩
  exact congrArg Subtype.val this

theorem card_sq_le_of_isotropic (hK : Nat.card K = 2) (B : LinearMap.BilinForm K V)
    (hB : B.Nondegenerate) (hr : B.IsRefl) (X : Subgroup (Module.End K V)ˣ)
    (hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hexp : ∀ x ∈ X, x ^ 3 = 1)
    (hinv : ∀ x ∈ X, ∀ v w, B ((x : Module.End K V) v) ((x : Module.End K V) w) = B v w)
    {T : Submodule K V} (hT0 : T ≠ ⊥) (hTiso : ∀ u ∈ T, ∀ v ∈ T, B u v = 0)
    (hTX : ∀ x ∈ X, ∀ t ∈ T, (x : Module.End K V) t ∈ T) :
    Nat.card X ^ 2 ≤ 3 ^ (finrank K V - finrank K T) := by
  classical
  have := finite_units_end (K := K) (V := V)
  set S := B.orthogonal T with hS
  have hSX : ∀ x ∈ X, ∀ s ∈ S, (x : Module.End K V) s ∈ S := by
    intro x hx s hs t ht
    have h1 : ((x⁻¹ : (Module.End K V)ˣ) : Module.End K V) t ∈ T :=
      hTX x⁻¹ (X.inv_mem hx) t ht
    have h2 := hinv x hx (((x⁻¹ : (Module.End K V)ˣ) : Module.End K V) t) s
    have h3 : (x : Module.End K V) (((x⁻¹ : (Module.End K V)ˣ) : Module.End K V) t) = t := by
      rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Module.End.one_apply]
    rw [h3] at h2
    rw [h2]
    exact hs _ h1
  have hTS : T ≤ S := fun t ht n hn => hTiso n hn t ht
  have hfix : X ⊓ fixG S = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgX, hgS⟩
    rw [Subgroup.mem_bot]
    have hg1 : ∀ v, ((g : Module.End K V) - 1) v ∈ T := by
      intro v
      rw [← B.orthogonal_orthogonal hB hr T]
      intro s hs
      have h1 := hinv g hgX s v
      rw [hgS s hs] at h1
      rw [LinearMap.sub_apply, Module.End.one_apply, map_sub, h1, sub_self]
    have hg2 : ((g : Module.End K V) - 1) * ((g : Module.End K V) - 1) = 0 := by
      ext v
      rw [Module.End.mul_apply, LinearMap.zero_apply]
      have h1 := hgS _ (hTS (hg1 v))
      rw [LinearMap.sub_apply, Module.End.one_apply, h1, sub_self]
    have hsq : g * g = 1 := by
      apply Units.ext
      rw [Units.val_mul, Units.val_one]
      have e : (g : Module.End K V) * g =
          ((g : Module.End K V) - 1) * ((g : Module.End K V) - 1) +
            2 * (g : Module.End K V) - 1 := by
        noncomm_ring
      rw [e, hg2, two_eq_zero_end]
      have h2 : (1 : Module.End K V) + 1 = 0 := by
        rw [one_add_one_eq_two, two_eq_zero_end]
      rw [zero_mul, add_zero, zero_sub]
      exact neg_eq_of_add_eq_zero_right h2
    calc g = g ^ 3 * (g * g)⁻¹ := by group
      _ = 1 := by rw [hexp g hgX, hsq]; simp
  have h := card_sq_le hK (finrank K S) S rfl X hcomm hexp hSX
  rw [hfix, Subgroup.card_bot, one_pow, mul_one, hS,
    LinearMap.BilinForm.finrank_orthogonal hB T] at h
  exact h

@[expose] def fixSpaceOf {G : Type*} [Group G] (ρ : G →* (Module.End K V)ˣ) (U : Subgroup G) :
    Submodule K V where
  carrier := {v | ∀ u ∈ U, (ρ u : Module.End K V) v = v}
  add_mem' := fun {a b} ha hb u hu => by rw [map_add, ha u hu, hb u hu]
  zero_mem' := fun u _ => map_zero _
  smul_mem' := fun c v hv u hu => by rw [map_smul, hv u hu]

theorem mem_fixSpaceOf {G : Type*} [Group G] {ρ : G →* (Module.End K V)ˣ} {U : Subgroup G}
    {v : V} : v ∈ fixSpaceOf ρ U ↔ ∀ u ∈ U, (ρ u : Module.End K V) v = v :=
  Iff.rfl

theorem rho_mul_apply {G : Type*} [Group G] (ρ : G →* (Module.End K V)ˣ) (g h : G) (v : V) :
    (ρ (g * h) : Module.End K V) v = (ρ g : Module.End K V) ((ρ h : Module.End K V) v) := by
  rw [map_mul, Units.val_mul, Module.End.mul_apply]

theorem exists_isotropic_of_normalizes_two (hK : Nat.card K = 2) {G : Type*} [Group G]
    (ρ : G →* (Module.End K V)ˣ) (hρ : Function.Injective ρ) (B : LinearMap.BilinForm K V)
    (hB : B.Nondegenerate) (hr : B.IsRefl)
    (hinv : ∀ g v w, B ((ρ g : Module.End K V) v) ((ρ g : Module.End K V) w) = B v w)
    {A U : Subgroup G} (hU1 : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hAU : ∀ a ∈ A, ∀ u ∈ U, a * u * a⁻¹ ∈ U) :
    ∃ T : Submodule K V, T ≠ ⊥ ∧ (∀ u ∈ T, ∀ v ∈ T, B u v = 0) ∧
      ∀ a ∈ A, ∀ t ∈ T, (ρ a : Module.End K V) t ∈ T := by
  classical
  set C := fixSpaceOf ρ U with hC
  set W := B.orthogonal C with hW
  have hrinv : ∀ g : G, ∀ v : V, (ρ g : Module.End K V) ((ρ g⁻¹ : Module.End K V) v) = v := by
    intro g v
    rw [← rho_mul_apply, mul_inv_cancel, map_one, Units.val_one, Module.End.one_apply]
  have hCA : ∀ a ∈ A, ∀ c ∈ C, (ρ a : Module.End K V) c ∈ C := by
    intro a ha c hc u hu
    have hu' : a⁻¹ * u * a⁻¹⁻¹ ∈ U := hAU a⁻¹ (A.inv_mem ha) u hu
    have h1 : u * a = a * (a⁻¹ * u * a⁻¹⁻¹) := by group
    rw [← rho_mul_apply, h1, rho_mul_apply, hc _ hu']
  have hWA : ∀ a ∈ A, ∀ w ∈ W, (ρ a : Module.End K V) w ∈ W := by
    intro a ha w hw c hc
    have h1 := hinv a ((ρ a⁻¹ : Module.End K V) c) w
    rw [hrinv] at h1
    rw [h1]
    exact hw _ (hCA a⁻¹ (A.inv_mem ha) c hc)
  have hWU : ∀ u ∈ U, ∀ w ∈ W, (ρ u : Module.End K V) w ∈ W := by
    intro u hu w hw c hc
    have h1 := hinv u c w
    rw [hc u hu] at h1
    rw [h1]
    exact hw c hc
  have hCtop : C ≠ ⊤ := by
    intro htop
    obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU1
    apply hu1
    apply Subtype.ext
    apply hρ
    apply Units.ext
    apply LinearMap.ext
    intro v
    rw [Subgroup.coe_one, map_one, Units.val_one, Module.End.one_apply]
    exact (htop ▸ Submodule.mem_top : v ∈ C) u hu
  have hW0 : W ≠ ⊥ := by
    intro hbot
    apply hCtop
    rw [← B.orthogonal_orthogonal hB hr C, ← hW, hbot, LinearMap.BilinForm.orthogonal_bot]
  obtain ⟨w, hwW, hw0, hwfix⟩ := exists_fixed_ne_zero hK ρ hU2 hW0 hWU
  refine ⟨C ⊓ W, fun h => hw0 ?_, ?_, ?_⟩
  · have : w ∈ C ⊓ W := ⟨hwfix, hwW⟩
    rw [h, Submodule.mem_bot] at this
    exact this
  · intro u hu v hv
    exact hv.2 u hu.1
  · intro a ha t ht
    exact ⟨hCA a ha t ht.1, hWA a ha t ht.2⟩

theorem exists_isotropic_card_sq_le (hK : Nat.card K = 2) {G : Type*} [Group G] [Finite G]
    (ρ : G →* (Module.End K V)ˣ) (hρ : Function.Injective ρ) (B : LinearMap.BilinForm K V)
    (hB : B.Nondegenerate) (hr : B.IsRefl)
    (hinv : ∀ g v w, B ((ρ g : Module.End K V) v) ((ρ g : Module.End K V) w) = B v w)
    {A U : Subgroup G} (hA : IsElemAbelian 3 A) (hU1 : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hAU : ∀ a ∈ A, ∀ u ∈ U, a * u * a⁻¹ ∈ U) :
    ∃ T : Submodule K V, T ≠ ⊥ ∧ (∀ u ∈ T, ∀ v ∈ T, B u v = 0) ∧
      (∀ a ∈ A, ∀ t ∈ T, (ρ a : Module.End K V) t ∈ T) ∧
      Nat.card A ^ 2 ≤ 3 ^ (finrank K V - finrank K T) := by
  obtain ⟨T, hT0, hTiso, hTA⟩ := exists_isotropic_of_normalizes_two hK ρ hρ B hB hr hinv hU1 hU2
    hAU
  refine ⟨T, hT0, hTiso, hTA, ?_⟩
  have hcardX : Nat.card (A.map ρ) = Nat.card A :=
    (Nat.card_congr (A.equivMapOfInjective ρ hρ).toEquiv).symm
  rw [← hcardX]
  refine card_sq_le_of_isotropic hK B hB hr (A.map ρ) ?_ ?_ ?_ hT0 hTiso ?_
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, IsElemAbelian.comm hA ha hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hA.2 a ha, map_one]
  · rintro _ ⟨a, ha, rfl⟩ v w
    exact hinv a v w
  · rintro _ ⟨a, ha, rfl⟩ t ht
    exact hTA a ha t ht

theorem card_sq_le_of_normalizes_two (hK : Nat.card K = 2) {G : Type*} [Group G] [Finite G]
    (ρ : G →* (Module.End K V)ˣ) (hρ : Function.Injective ρ) (B : LinearMap.BilinForm K V)
    (hB : B.Nondegenerate) (hr : B.IsRefl)
    (hinv : ∀ g v w, B ((ρ g : Module.End K V) v) ((ρ g : Module.End K V) w) = B v w)
    {A U : Subgroup G} (hA : IsElemAbelian 3 A) (hU1 : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hAU : ∀ a ∈ A, ∀ u ∈ U, a * u * a⁻¹ ∈ U) :
    Nat.card A ^ 2 ≤ 3 ^ (finrank K V - 1) := by
  obtain ⟨T, hT0, -, -, h⟩ := exists_isotropic_card_sq_le hK ρ hρ B hB hr hinv hA hU1 hU2 hAU
  have : 1 ≤ finrank K T := Submodule.one_le_finrank_iff.mpr hT0
  exact h.trans (Nat.pow_le_pow_right (by norm_num) (by omega))

end CFSG.StandardType.SmallRule

end
