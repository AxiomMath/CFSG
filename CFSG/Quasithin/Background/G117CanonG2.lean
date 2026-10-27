module

public import CFSG.Quasithin.Background.G9StmtsModels
import CFSG.Quasithin.Vol2.Ch12Sec4G2NormZorn
import CFSG.Quasithin.Background.G11Bridge
public import CFSG.Quasithin.Background.B4ModelsLie

public section

namespace CFSG.Quasithin.G11.Canon

open CFSG.Quasithin.G11 CFSG.Open

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

private theorem zornMap_scalar {F F' : Type} [Field F] [Field F'] (σ : F ≃+* F') (c : F) :
    JonesParshall.zornMap σ ((c, 0, 0, c) : quasithinZorn F) = (σ c, 0, 0, σ c) :=
  Prod.ext rfl (Prod.ext (funext fun _ => map_zero σ) (Prod.ext (funext fun _ => map_zero σ) rfl))

omit [Finite V] in
theorem isG2NaturalModule_derived_zmod2 {H : Subgroup (GLV V)}
    (h : IsG2NaturalModule H
      ⁅quasithinG2 (GaloisField 2 1), quasithinG2 (GaloisField 2 1)⁆) :
    IsG2NaturalModule H ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ := by
  obtain ⟨φ, π, h1, h2, h3⟩ := h
  let e : GaloisField 2 1 ≃+* ZMod 2 := (GaloisField.equivZmodP 2).toRingEquiv
  let L₀ : quasithinZorn (ZMod 2) →+ quasithinZorn (GaloisField 2 1) :=
    AddMonoidHom.mk' (JonesParshall.zornMap e.symm) (JonesParshall.zornMap_add e.symm)
  let L : quasithinZorn (ZMod 2) →ₗ[ZMod 2] quasithinZorn (GaloisField 2 1) :=
    { L₀ with
      map_smul' := fun c x => by
        rcases zmod2_eq_zero_or_one c with rfl | rfl <;> simp }
  have hL : ∀ x, L x = JonesParshall.zornMap e.symm x := fun _ => rfl
  have htr : ∀ {F F' : Type} [Field F] [Field F'] (σ : F ≃+* F') (x : quasithinZorn F),
      x.1 + x.2.2.2 = 0 →
        (JonesParshall.zornMap σ x).1 + (JonesParshall.zornMap σ x).2.2.2 = 0 :=
    fun σ x hx => by
      change σ x.1 + σ x.2.2.2 = 0
      rw [← map_add, hx, map_zero]
  refine ⟨φ.trans (H13.VolI.g2DerivedFieldEquiv e), π ∘ₗ L, fun v => ?_, fun x hx => ?_,
    fun k x hx => ?_⟩
  · obtain ⟨x, hx, rfl⟩ := h1 v
    exact ⟨JonesParshall.zornMap e x, htr e x hx, by
      rw [LinearMap.comp_apply, hL, JonesParshall.zornMap_symm_apply]⟩
  · rw [LinearMap.comp_apply, hL, h2 _ (htr e.symm x hx)]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨e c, ?_⟩
      rw [← JonesParshall.zornMap_apply_symm e x, hc, zornMap_scalar]
    · rintro ⟨c, rfl⟩
      exact ⟨e.symm c, zornMap_scalar e.symm c⟩
  · change π (JonesParshall.zornMap e.symm (JonesParshall.zornMap e
      (((φ k : ↥⁅quasithinG2 (GaloisField 2 1), quasithinG2 (GaloisField 2 1)⁆) :
        quasithinZorn (GaloisField 2 1) ≃ₗ[GaloisField 2 1] quasithinZorn (GaloisField 2 1))
          (JonesParshall.zornMap e.symm x)))) = (k : GLV V) (π (L x))
    rw [JonesParshall.zornMap_symm_apply]
    exact h3 k _ (htr e.symm x hx)

omit [Finite V] in
private theorem exists_modQ_equiv {π : quasithinZorn (ZMod 2) →ₗ[ZMod 2] V}
    (h1 : ∀ v : V, ∃ x : quasithinZorn (ZMod 2), x.1 + x.2.2.2 = 0 ∧ π x = v)
    (h2 : ∀ x : quasithinZorn (ZMod 2), x.1 + x.2.2.2 = 0 →
      (π x = 0 ↔ ∃ c : ZMod 2, x = (c, 0, 0, c))) :
    ∃ E : H13.ModQ ≃* Multiplicative V, ∀ (x : quasithinZorn (ZMod 2))
      (hx : x.1 + x.2.2.2 = 0),
        E (QuotientGroup.mk (⟨Multiplicative.ofAdd x, hx⟩ : ↥(zornO0 (ZMod 2)))) =
          Multiplicative.ofAdd (π x) := by
  let f : ↥(zornO0 (ZMod 2)) →* Multiplicative V :=
    (AddMonoidHom.toMultiplicative π.toAddMonoidHom).comp (zornO0 (ZMod 2)).subtype
  have hf : Function.Surjective f := by
    intro m
    obtain ⟨x, hx, hxm⟩ := h1 (Multiplicative.toAdd m)
    refine ⟨⟨Multiplicative.ofAdd x, hx⟩, ?_⟩
    change Multiplicative.ofAdd (π x) = m
    rw [hxm, ofAdd_toAdd]
  have hker : f.ker = (zornR (ZMod 2)).subgroupOf (zornO0 (ZMod 2)) := by
    ext m
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change Multiplicative.ofAdd (π (Multiplicative.toAdd m.1)) = 1 ↔
      ∃ c : ZMod 2, Multiplicative.toAdd m.1 = (c, 0, 0, c)
    rw [ofAdd_eq_one]
    exact h2 _ m.2
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf), fun _ _ => rfl⟩

private theorem isG2NaturalModule_of_card
    {H Γ : Subgroup (GLV V)}
    (hnat : IsG2NaturalModule H ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆)
    (hnorm : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H)
    (hC : ∀ c : GLV V, (∀ h ∈ H, h * c = c * h) → c = 1)
    (hcard : Nat.card ↥Γ = 12096) :
    IsG2NaturalModule Γ (quasithinG2 (ZMod 2)) := by
  obtain ⟨φ, π, h1, h2, h3⟩ := hnat
  obtain ⟨E, hE⟩ := exists_modQ_equiv h1 h2
  let ρ : ↥(quasithinG2 (ZMod 2)) →* MulAut (Multiplicative V) :=
    (MulAut.congr E).toMonoidHom.comp (H13.g2QAct (ZMod 2))
  have hρ : ∀ (g : ↥(quasithinG2 (ZMod 2))) (x : quasithinZorn (ZMod 2)), x.1 + x.2.2.2 = 0 →
      ρ g (Multiplicative.ofAdd (π x)) = Multiplicative.ofAdd
        (π ((g : quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)) x)) := by
    intro g x hx
    have h0 : E.symm (Multiplicative.ofAdd (π x)) =
        QuotientGroup.mk (⟨Multiplicative.ofAdd x, hx⟩ : ↥(zornO0 (ZMod 2))) :=
      E.symm_apply_eq.2 (hE x hx).symm
    change E (H13.g2QAct (ZMod 2) g (E.symm (Multiplicative.ofAdd (π x)))) = _
    rw [h0]
    exact hE _ ((mem_quasithinG2_isZornAuto g.2).trace_zero hx)
  have hρinj : Function.Injective ρ := (MulAut.congr E).injective.comp H13.g2QAct_injective
  have hρH : ∀ h : ↥H, ρ ⟨((φ h : ↥⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆) :
      quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)),
        Subgroup.commutator_le_self _ (φ h).2⟩ = linEquivMulAut (h : GLV V) := by
    intro h
    refine MulEquiv.ext fun m => ?_
    obtain ⟨x, hx, hxm⟩ := h1 (Multiplicative.toAdd m)
    have hm : m = Multiplicative.ofAdd (π x) := by rw [hxm]; rfl
    rw [hm, hρ _ x hx, linEquivMulAut_apply, toAdd_ofAdd]
    exact congrArg Multiplicative.ofAdd (h3 h x hx)
  have hD : ∀ y : MulAut (Multiplicative V),
      y ∈ (H13.g2Derived (ZMod 2)).map ρ ↔ linEquivMulAut.symm y ∈ H := by
    intro y
    rw [H13.mem_map_g2Derived_iff]
    constructor
    · rintro ⟨γ, rfl⟩
      have h := hρH (φ.symm γ)
      rw [MulEquiv.apply_symm_apply] at h
      rw [h, MulEquiv.symm_apply_apply]
      exact (φ.symm γ).2
    · intro hy
      refine ⟨φ ⟨_, hy⟩, ?_⟩
      rw [hρH]
      exact MulEquiv.apply_symm_apply _ _
  have hschur : ∀ y : MulAut (Multiplicative V),
      (∀ k ∈ (H13.g2Derived (ZMod 2)).map ρ, y * k = k * y) → y = 1 := by
    intro y hy
    have hc : linEquivMulAut.symm y = 1 := hC _ fun h hh => by
      have hk := hy (linEquivMulAut h) ((hD _).2 (by rwa [MulEquiv.symm_apply_apply]))
      apply linEquivMulAut.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hk.symm
    rw [← linEquivMulAut.apply_symm_apply y, hc, map_one]
  have hrange : ∀ γ ∈ Γ, linEquivMulAut γ ∈ ρ.range := by
    intro γ hγ
    refine H13.normalizer_two ρ hρinj hschur H13.card_mulAut_g2Derived _ fun k => ?_
    rw [hD, hD, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
    refine ⟨hnorm γ hγ _, fun hk => ?_⟩
    have h := hnorm γ⁻¹ (Γ.inv_mem hγ) _ hk
    rwa [show γ⁻¹ * (γ * linEquivMulAut.symm k * γ⁻¹) * γ⁻¹⁻¹ = linEquivMulAut.symm k by
      group] at h
  let ψ : ↥Γ →* ↥ρ.range :=
    (linEquivMulAut.toMonoidHom.comp Γ.subtype).codRestrict ρ.range fun γ => hrange γ γ.2
  let ι : ↥Γ →* ↥(quasithinG2 (ZMod 2)) := (MonoidHom.ofInjective hρinj).symm.toMonoidHom.comp ψ
  have hι : ∀ γ : ↥Γ, ρ (ι γ) = linEquivMulAut (γ : GLV V) := by
    intro γ
    rw [← MonoidHom.ofInjective_apply hρinj]
    change (((MonoidHom.ofInjective hρinj) ((MonoidHom.ofInjective hρinj).symm (ψ γ)) :
      ↥ρ.range) : MulAut (Multiplicative V)) = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hιinj : Function.Injective ι := fun a b hab =>
    Subtype.ext (linEquivMulAut.injective (by rw [← hι, ← hι, hab]))
  have hιbij : Function.Bijective ι :=
    hιinj.bijective_of_nat_card_le (by rw [H13.Orbit.card_g2Two, hcard])
  refine ⟨MulEquiv.ofBijective ι hιbij, π, h1, h2, fun γ x hx => ?_⟩
  have h := DFunLike.congr_fun (hι γ) (Multiplicative.ofAdd (π x))
  rw [hρ _ x hx, linEquivMulAut_apply, toAdd_ofAdd] at h
  exact Multiplicative.ofAdd.injective h

theorem isG2NaturalModule_overgroup
    {H Γ : Subgroup (GLV V)}
    (hnat : IsG2NaturalModule H
      ⁅quasithinG2 (GaloisField 2 1), quasithinG2 (GaloisField 2 1)⁆)
    (hHΓ : H ≤ Γ) (hnorm : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H)
    (hC : ∀ c : GLV V, (∀ h ∈ H, h * c = c * h) → c = 1)
    (hΓ : Nat.card ↥Γ ≤ 12096) :
    (Γ = H ∧ IsG2NaturalModule Γ ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆) ∨
    (Nat.card ↥Γ = 12096 ∧ IsG2NaturalModule Γ (quasithinG2 (ZMod 2))) := by
  have hnat2 := isG2NaturalModule_derived_zmod2 hnat
  have hH : Nat.card ↥H = 6048 := by
    obtain ⟨φ, -⟩ := hnat
    rw [Nat.card_congr φ.toEquiv, P3G2.card_commutatorG2]
  have : Finite (GLV V) :=
    Finite.of_injective (fun g : GLV V => (g : V → V)) fun _ _ h => LinearEquiv.ext (congrFun h)
  have hpos : 0 < Nat.card ↥Γ := Nat.card_pos
  obtain ⟨c, hc⟩ := hH ▸ Subgroup.card_dvd_of_le hHΓ
  rcases (by omega : c = 1 ∨ c = 2) with rfl | rfl
  · have hΓH : H = Γ := Subgroup.eq_of_le_of_card_ge hHΓ (by omega)
    exact Or.inl ⟨hΓH.symm, hΓH ▸ hnat2⟩
  · exact Or.inr ⟨by omega, isG2NaturalModule_of_card hnat2 hnorm hC (by omega)⟩

end CFSG.Quasithin.G11.Canon
