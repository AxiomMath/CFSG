module

public import CFSG.LieType.BorelTits.OrthogonalForm
import CFSG.LieType.BorelTits.Families

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4FF

open CFSG.LieType.BorelTits

private theorem polar_smul_left_F05 {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Φ : QuadForm K V) (c : K) (u v : V) :
    Φ.polar.β (c • u) v = c * Φ.polar.β u v := by
  rw [Φ.polar.smul_left, Φ.polar_σ, RingEquiv.refl_apply]

private theorem point_fixed_f_F05 {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Φ : QuadForm K V) {v f : V} (hv : Φ.Q v = 0)
    (hvf : Φ.polar.β v f = 1) {T : V →ₗ[K] V} (hT : ∀ x, Φ.Q (T x) = Φ.Q x)
    (hTf : T f - f ∈ Submodule.span K {v}) : T f = f := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hTf
  have hTf' : f + c • v = T f := by rw [hc]; abel
  have hfv : Φ.polar.β f v = 1 := (Φ.polar_symm f v).trans hvf
  have hQ := hT f
  rw [← hTf'] at hQ
  have hqa := Φ.Q_add f (c • v)
  rw [Φ.Q_smul, hv, mul_zero, add_zero, Φ.polar.smul_right, hfv, mul_one] at hqa
  rw [hqa] at hQ
  have hc0 : c = 0 := add_left_cancel (hQ.trans (add_zero _).symm)
  have : T f - f = 0 := by rw [← hc, hc0, zero_smul]
  exact sub_eq_zero.mp this

private theorem point_fixed_perp_F05 {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Φ : QuadForm K V) {v f : V} (hvf : Φ.polar.β v f = 1) {T : V →ₗ[K] V}
    (hT : ∀ x, Φ.Q (T x) = Φ.Q x) (hTf : T f = f) {u : V}
    (h2u : T u - u ∈ Submodule.span K {v}) : T u = u := by
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp h2u
  have hu' : u + t • v = T u := by rw [ht]; abel
  have hmap := Φ.polar_map_of_Q hT u f
  rw [hTf, ← hu'] at hmap
  rw [Φ.polar.add_left, polar_smul_left_F05 Φ t v f, hvf, mul_one] at hmap
  have ht0 : t = 0 := add_left_cancel (hmap.trans (add_zero _).symm)
  have : T u - u = 0 := by rw [← ht, ht0, zero_smul]
  exact sub_eq_zero.mp this

private theorem point_fixed_F05 {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Φ : QuadForm K V) {v f : V} (hvf : Φ.polar.β v f = 1)
    {T : V →ₗ[K] V} (hT : ∀ x, Φ.Q (T x) = Φ.Q x)
    (h3 : ∀ x, T x - x ∈ Φ.polar.perp (Submodule.span K {v}))
    (hTf : T f = f)
    (hf2 : ∀ u ∈ Φ.polar.perp (Submodule.span K {v}), T u = u) (x : V) : T x = x := by
  have hperp : T x - x ∈ Φ.polar.perp (Φ.polar.perp (Submodule.span K {v})) := by
    rw [ReflForm.mem_perp]
    intro u hu
    have hmap := Φ.polar_map_of_Q hT x u
    rw [hf2 u hu] at hmap
    rw [ReflForm.β_sub_right, Φ.polar_symm u (T x), Φ.polar_symm u x, hmap, sub_self]
  rw [ReflForm.perp_perp] at hperp
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hperp
  have hmap2 := Φ.polar_map_of_Q hT x f
  rw [hTf] at hmap2
  have hsub : Φ.polar.β (T x - x) f = 0 := by
    rw [ReflForm.β_sub_left, hmap2, sub_self]
  have hsub2 : Φ.polar.β (T x - x) f = c := by
    rw [← hc, polar_smul_left_F05 Φ c v f, hvf, mul_one]
  have hc0 : c = 0 := (hsub.symm.trans hsub2).symm
  have : T x - x = 0 := by rw [← hc, hc0, zero_smul]
  exact sub_eq_zero.mp this

theorem eq_id_of_point {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Φ : QuadForm K V) {v f : V} (hv : Φ.Q v = 0)
    (hvf : Φ.polar.β v f = 1) {T : V →ₗ[K] V} (hT : ∀ x, Φ.Q (T x) = Φ.Q x)
    (h2 : ∀ x ∈ Φ.polar.perp (Submodule.span K {v}), T x - x ∈ Submodule.span K {v})
    (h3 : ∀ x, T x - x ∈ Φ.polar.perp (Submodule.span K {v}))
    (hTf : T f - f ∈ Submodule.span K {v}) : T = LinearMap.id := by
  have hf : T f = f := point_fixed_f_F05 Φ hv hvf hT hTf
  have hf2 : ∀ u ∈ Φ.polar.perp (Submodule.span K {v}), T u = u := fun u hu =>
    point_fixed_perp_F05 Φ hvf hT hf (h2 u hu)
  ext x
  simpa using point_fixed_F05 Φ hvf hT h3 hf hf2 x

private theorem point_eq_of_sub_mem_F05 {K V H : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Group H] (Φ : QuadForm K V) (ρ : H →* Module.End K V)
    (hρ : Function.Injective ρ) (hQ : ∀ h x, Φ.Q (ρ h x) = Φ.Q x) {v f : V}
    (hv : Φ.Q v = 0) (hvf : Φ.polar.β v f = 1) {R : Subgroup H}
    (h2 : ∀ g ∈ R, ∀ x ∈ Φ.polar.perp (Submodule.span K {v}),
      ρ g x - x ∈ Submodule.span K {v})
    (h3 : ∀ g ∈ R, ∀ x, ρ g x - x ∈ Φ.polar.perp (Submodule.span K {v}))
    {g g' : ↥R} (hgf : ρ g.1 f - ρ g'.1 f ∈ Submodule.span K {v}) : g = g' := by
  let h : H := g'.1⁻¹ * g.1
  have hh : h ∈ R := R.mul_mem (R.inv_mem g'.2) g.2
  have hinv : ρ g'.1 * ρ (g'.1⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hcomp : ρ g.1 = ρ g'.1 * ρ h := by
    have hh' : h = g'.1⁻¹ * g.1 := rfl
    rw [hh', map_mul]
    rw [← mul_assoc, hinv, one_mul]
  have hmapθ : ρ g'.1 (ρ h f - f) = ρ g.1 f - ρ g'.1 f := by
    have h1 : ρ g'.1 (ρ h f) = ρ g.1 f := by
      change (ρ g'.1 * ρ h) f = ρ g.1 f
      rw [hcomp]
    rw [map_sub, h1]
  have hθP : ρ h f - f ∈ Φ.polar.perp (Submodule.span K {v}) := h3 h hh f
  have h2θ : ρ g'.1 (ρ h f - f) - (ρ h f - f) ∈ Submodule.span K {v} :=
    h2 g'.1 g'.2 (ρ h f - f) hθP
  have hθL : ρ h f - f ∈ Submodule.span K {v} := by
    have h1 : ρ g'.1 (ρ h f - f) ∈ Submodule.span K {v} := by rw [hmapθ]; exact hgf
    have := sub_mem h1 h2θ
    rwa [sub_sub_cancel] at this
  have hid : ρ h = LinearMap.id := eq_id_of_point Φ hv hvf (hQ h) (h2 h hh) (h3 h hh) hθL
  have hh1 : h = 1 := hρ (by rw [map_one]; exact hid)
  have hh1' : g'.1⁻¹ * g.1 = 1 := hh1
  exact Subtype.ext (inv_mul_eq_one.mp hh1').symm

private theorem point_quot_injective_F05 {K V H : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Group H] (Φ : QuadForm K V) (ρ : H →* Module.End K V)
    (hρ : Function.Injective ρ) (hQ : ∀ h x, Φ.Q (ρ h x) = Φ.Q x) {v f : V}
    (hv : Φ.Q v = 0) (hvf : Φ.polar.β v f = 1) {R : Subgroup H}
    (h2 : ∀ g ∈ R, ∀ x ∈ Φ.polar.perp (Submodule.span K {v}),
      ρ g x - x ∈ Submodule.span K {v})
    (h3 : ∀ g ∈ R, ∀ x, ρ g x - x ∈ Φ.polar.perp (Submodule.span K {v})) :
    Function.Injective (fun g : ↥R =>
      (Submodule.Quotient.mk (p :=
        Submodule.comap (Φ.polar.perp (Submodule.span K {v})).subtype
          (Submodule.span K {v}))
        ⟨ρ g.1 f - f, h3 g.1 g.2 f⟩)) := by
  intro g g' hgg'
  have hmem := (Submodule.Quotient.eq _).mp hgg'
  have hgf : ρ g.1 f - ρ g'.1 f ∈ Submodule.span K {v} := by
    simpa using hmem
  exact point_eq_of_sub_mem_F05 Φ ρ hρ hQ hv hvf h2 h3 hgf

theorem card_le_of_point {K V H : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Group H] (Φ : QuadForm K V) (ρ : H →* Module.End K V)
    (hρ : Function.Injective ρ) (hQ : ∀ h x, Φ.Q (ρ h x) = Φ.Q x) {v : V} (hv0 : v ≠ 0)
    (hv : Φ.Q v = 0) {R : Subgroup H}
    (h2 : ∀ g ∈ R, ∀ x ∈ Φ.polar.perp (Submodule.span K {v}), ρ g x - x ∈ Submodule.span K {v})
    (h3 : ∀ g ∈ R, ∀ x, ρ g x - x ∈ Φ.polar.perp (Submodule.span K {v})) :
    Nat.card ↥R ≤ Nat.card K ^ (Module.finrank K V - 2) := by
  have hf_exists : ∃ f0, Φ.polar.β v f0 ≠ 0 := by
    by_contra h
    rw [not_exists] at h
    exact hv0 (Φ.polar.nondeg v fun w => not_not.mp (h w))
  obtain ⟨f0, hf0⟩ := hf_exists
  let f : V := (Φ.polar.β v f0)⁻¹ • f0
  have hfv : Φ.polar.β v f = 1 := by
    show Φ.polar.β v ((Φ.polar.β v f0)⁻¹ • f0) = 1
    rw [Φ.polar.smul_right, inv_mul_cancel₀ hf0]
  let L : Submodule K V := Submodule.span K {v}
  let P : Submodule K V := Φ.polar.perp L
  have hLP : L ≤ P := by
    change Submodule.span K {v} ≤ Φ.polar.perp (Submodule.span K {v})
    exact (Φ.isTotallySingular_span_singleton hv).isTotallyIsotropic
  let L' : Submodule K ↥P := Submodule.comap P.subtype L
  let θ : ↥R → ↥P := fun g => ⟨ρ g.1 f - f, h3 g.1 g.2 f⟩
  let φ : ↥R → (↥P ⧸ L') := fun g => Submodule.Quotient.mk (θ g)
  have hφinj : Function.Injective φ := point_quot_injective_F05 Φ ρ hρ hQ hv hfv h2 h3
  haveI : Finite (↥P ⧸ L') := Module.finite_of_finite K
  have hcard : Nat.card ↥R ≤ Nat.card (↥P ⧸ L') := Nat.card_le_card_of_injective φ hφinj
  have hV : Module.finrank K ↥P + Module.finrank K L = Module.finrank K V :=
    Φ.polar.finrank_perp L
  have hL1 : Module.finrank K L = 1 := finrank_span_singleton hv0
  have hL' : Module.finrank K L' = Module.finrank K L :=
    (Submodule.comapSubtypeEquivOfLe hLP).finrank_eq
  have hQd : Module.finrank K (↥P ⧸ L') + Module.finrank K L' = Module.finrank K ↥P :=
    Submodule.finrank_quotient_add_finrank L'
  have hexp : Module.finrank K (↥P ⧸ L') = Module.finrank K V - 2 := by omega
  calc Nat.card ↥R ≤ Nat.card (↥P ⧸ L') := hcard
    _ = Nat.card K ^ Module.finrank K (↥P ⧸ L') := Module.natCard_eq_pow_finrank
    _ = Nat.card K ^ (Module.finrank K V - 2) := by rw [hexp]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4FF
