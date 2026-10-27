module

public import CFSG.Quasithin.H13.L32NLem14411b

public section

namespace CFSG.Quasithin.H13.L1442U

open Matrix L1442M Mat8Cert

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem add_self_zero (v : V) : v + v = 0 := by
  have h : (2 : ZMod 2) • v = 0 := by rw [show (2 : ZMod 2) = 0 from rfl, zero_smul]
  rwa [two_smul] at h

theorem fix_eq_zero {Γ : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hirr : ∀ J : Submodule (ZMod 2) V, (∀ γ ∈ Γ, ∀ v ∈ J, γ v ∈ J) → J = ⊥ ∨ J = ⊤)
    {t : V ≃ₗ[ZMod 2] V} (ht1 : t ≠ 1)
    (hnorm : ∀ γ ∈ Γ, γ⁻¹ * t * γ = t ∨ γ⁻¹ * t * γ = t * t) : ∀ v, t v = v → v = 0 := by
  obtain ⟨F, hF⟩ : ∃ F : Submodule (ZMod 2) V,
      F = LinearMap.ker ((t : V →ₗ[ZMod 2] V) - LinearMap.id) := ⟨_, rfl⟩
  have hmem : ∀ v, v ∈ F ↔ t v = v := fun v => by
    rw [hF, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    rfl
  have hinv : ∀ γ ∈ Γ, ∀ v ∈ F, γ v ∈ F := by
    intro γ hγ v hv
    rw [hmem] at hv ⊢
    have key : t (γ v) = γ ((γ⁻¹ * t * γ) v) := by
      show t (γ v) = γ (γ.symm (t (γ v)))
      rw [LinearEquiv.apply_symm_apply]
    rcases hnorm γ hγ with h | h
    · rw [key, h, hv]
    · rw [key, h, LinearEquiv.mul_apply, hv, hv]
  rcases hirr F hinv with h | h
  · intro v hv
    have hv' := (hmem v).mpr hv
    rw [h] at hv'
    exact hv'
  · exfalso
    apply ht1
    ext v
    exact (hmem v).mp (h ▸ Submodule.mem_top)

@[expose] def app : ((Fin 4 → ZMod 2) × (Fin 4 → ZMod 2)) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2) where
  toFun p := ![p.1 0, p.1 1, p.1 2, p.1 3, p.2 0, p.2 1, p.2 2, p.2 3]
  invFun f := (![f 0, f 1, f 2, f 3], ![f 4, f 5, f 6, f 7])
  map_add' p q := by funext i; fin_cases i <;> rfl
  map_smul' c p := by funext i; fin_cases i <;> rfl
  left_inv p := by ext i <;> fin_cases i <;> rfl
  right_inv f := by funext i; fin_cases i <;> rfl

theorem g5s0_app (a b : Fin 4 → ZMod 2) :
    (g5s0 : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ app (a, b) = app (a + b, b) := by
  funext i
  fin_cases i <;> simp [g5s0, app, Matrix.mulVec, dotProduct, Fin.sum_univ_eight]

theorem g5s1_app (a b : Fin 4 → ZMod 2) :
    (g5s1 : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ app (a, b) = app (b, a) := by
  funext i
  fin_cases i <;> simp [g5s1, app, Matrix.mulVec, dotProduct, Fin.sum_univ_eight]

theorem exists_coordsS3 [Finite V] (hdim : Module.finrank (ZMod 2) V = 8)
    {t s : V ≃ₗ[ZMod 2] V} (hfix : ∀ v, t v = v → v = 0) (ht3 : ∀ v, t (t (t v)) = v)
    (hs2 : ∀ v, s (s v) = v) (hst : ∀ v, s (t v) = t (t (s v))) :
    ∃ e : V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2),
      L14411.matOf e s = g5s0 ∧ L14411.matOf e (t * s) = g5s1 := by
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have htt : ∀ v, t (t v) = t v + v := by
    intro v
    have h0 := hfix (t (t v) + t v + v) (by rw [map_add, map_add, ht3]; abel)
    have h1 : t (t v) = -(t v + v) := by rw [← sub_eq_zero, sub_neg_eq_add, ← add_assoc]; exact h0
    rw [h1, neg_eq_iff_add_eq_zero, add_self_zero]
  obtain ⟨Y, hY⟩ : ∃ Y : Submodule (ZMod 2) V,
      Y = LinearMap.ker ((s : V →ₗ[ZMod 2] V) - LinearMap.id) := ⟨_, rfl⟩
  have hmemY : ∀ v, v ∈ Y ↔ s v = v := fun v => by
    rw [hY, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    rfl
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (Y × Y) →ₗ[ZMod 2] V,
      Φ = LinearMap.coprod Y.subtype ((t : V →ₗ[ZMod 2] V).comp Y.subtype) := ⟨_, rfl⟩
  have hΦv : ∀ p : Y × Y, Φ p = (p.1 : V) + t p.2 := fun p => by
    rw [hΦ, LinearMap.coprod_apply]
    rfl
  have hsΦ : ∀ p : Y × Y, s (Φ p) = Φ p + (p.2 : V) := by
    intro p
    have h1 := (hmemY p.1).mp p.1.2
    have h2 := (hmemY p.2).mp p.2.2
    rw [hΦv, map_add, h1, hst, h2, htt]
    abel
  have htsΦ : ∀ p : Y × Y, t (s (Φ p)) = Φ (p.2, p.1) := by
    intro p
    rw [hsΦ, hΦv, hΦv, map_add, map_add, htt]
    have h := add_self_zero (t (p.2 : V))
    calc t (p.1 : V) + (t (p.2 : V) + (p.2 : V)) + t (p.2 : V)
        = t (p.1 : V) + (p.2 : V) + (t (p.2 : V) + t (p.2 : V)) := by abel
      _ = (p.2 : V) + t (p.1 : V) := by rw [h, add_zero, add_comm]
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro p hp
    rw [LinearMap.mem_ker] at hp
    have h2 : (p.2 : V) = 0 := by
      have h1 := hsΦ p
      rw [hp, map_zero, zero_add] at h1
      exact h1.symm
    have h2' : p.2 = 0 := Subtype.ext h2
    have h1 : (p.1 : V) = 0 := by
      rw [hΦv, h2, map_zero, add_zero] at hp
      exact hp
    exact Prod.ext (Subtype.ext h1) h2'
  have hsurj : Function.Surjective Φ := by
    intro v
    have hp2 : v + s v ∈ Y := by
      rw [hmemY, map_add, hs2, add_comm]
    have hp1 : v + t (v + s v) ∈ Y := by
      rw [hmemY, map_add, hst, (hmemY _).mp hp2, htt]
      have h := add_self_zero (s v)
      calc s v + (t (v + s v) + (v + s v)) = v + t (v + s v) + (s v + s v) := by abel
        _ = v + t (v + s v) := by rw [h, add_zero]
    refine ⟨(⟨_, hp1⟩, ⟨_, hp2⟩), ?_⟩
    rw [hΦv]
    show v + t (v + s v) + t (v + s v) = v
    rw [add_assoc, add_self_zero, add_zero]
  let Φe : (Y × Y) ≃ₗ[ZMod 2] V := LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  have hΦe : ∀ p, Φe p = Φ p := fun p => rfl
  have hY4 : Module.finrank (ZMod 2) Y = 4 := by
    have h := Φe.finrank_eq
    rw [Module.finrank_prod, hdim] at h
    omega
  let bY : Y ≃ₗ[ZMod 2] (Fin 4 → ZMod 2) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [hY4, Module.finrank_fin_fun])
  let e : V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2) := Φe.symm.trans ((bY.prodCongr bY).trans app)
  have he : ∀ p : Y × Y, e (Φ p) = app (bY p.1, bY p.2) := by
    intro p
    show app ((bY.prodCongr bY) (Φe.symm (Φe p))) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  refine ⟨e, (L14411.matOf_eq_iff e s g5s0).mpr fun v => ?_,
    (L14411.matOf_eq_iff e (t * s) g5s1).mpr fun v => ?_⟩
  · obtain ⟨p, rfl⟩ := hsurj v
    have h : s (Φ p) = Φ (p.1 + p.2, p.2) := by
      rw [hsΦ, hΦv, hΦv, Submodule.coe_add]
      abel
    rw [h, he, he, map_add, g5s0_app]
  · obtain ⟨p, rfl⟩ := hsurj v
    rw [LinearEquiv.mul_apply, htsΦ, he, he, g5s1_app]

@[expose] noncomputable def unitOf {a b : List ℕ} (ha : Valid8 a) (hb : Valid8 b)
    (hab : mul8 a b = one8) (hba : mul8 b a = one8) : GL (Fin 8) (ZMod 2) where
  val := dec8 a
  inv := dec8 b
  val_inv := by rw [← dec8_mul8 _ _ hb.1, hab, dec8_one8]
  inv_val := by rw [← dec8_mul8 _ _ ha.1, hba, dec8_one8]

theorem matOf_change (e : V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) {a b : List ℕ} (ha : Valid8 a)
    (hb : Valid8 b) (hab : mul8 a b = one8) (hba : mul8 b a = one8) (φ : V ≃ₗ[ZMod 2] V) :
    ((L14411.matOf (e.trans (L14411.linOf (unitOf ha hb hab hba))) φ : GL (Fin 8) (ZMod 2)) :
      Matrix (Fin 8) (Fin 8) (ZMod 2)) =
      dec8 a * (L14411.matOf e φ : Matrix (Fin 8) (Fin 8) (ZMod 2)) * dec8 b := by
  rw [L14411.matOf_trans, Units.val_mul, Units.val_mul]
  rfl

theorem dec8_conj {a b L L' : List ℕ} (hb : b.length = 8) (hL' : L'.length = 8)
    (hab : mul8 a b = one8) (h : mul8 L b = mul8 b L') :
    dec8 a * dec8 L * dec8 b = dec8 L' := by
  rw [mul_assoc, ← dec8_mul8 _ _ hb, h, dec8_mul8 _ _ hL', ← mul_assoc,
    ← dec8_mul8 _ _ hb, hab, dec8_one8, one_mul]

end CFSG.Quasithin.H13.L1442U
