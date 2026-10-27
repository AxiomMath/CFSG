module

public import CFSG.Quasithin.Background.G10FourBig

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem g10Four_exists_irr_le (K : Subgroup (GLV V)) :
    ∀ (n : ℕ) (J : Submodule (ZMod 2) V), Module.finrank (ZMod 2) J = n → Invariant K J →
      J ≠ ⊥ → ∃ U : Submodule (ZMod 2) V, U ≤ J ∧ U ≠ ⊥ ∧ Invariant K U ∧
        ∀ T : Submodule (ZMod 2) V, Invariant K T → T ≤ U → T = ⊥ ∨ T = U := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro J hJn hJinv hJ0
    by_cases hmin : ∀ T : Submodule (ZMod 2) V, Invariant K T → T ≤ J → T = ⊥ ∨ T = J
    · exact ⟨J, le_rfl, hJ0, hJinv, hmin⟩
    · push Not at hmin
      obtain ⟨T, hTinv, hTJ, hT0, hTne⟩ := hmin
      have hlt : T < J := lt_of_le_of_ne hTJ hTne
      have hfin : Module.finrank (ZMod 2) T < n := hJn ▸ Submodule.finrank_lt_finrank_of_lt hlt
      obtain ⟨U, hUT, hU0, hUinv, hUmin⟩ := ih _ hfin T rfl hTinv hT0
      exact ⟨U, hUT.trans hTJ, hU0, hUinv, hUmin⟩

theorem g10Four_card_linearEquiv_two (U : Type) [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (hU : Module.finrank (ZMod 2) U = 2) : Nat.card (U ≃ₗ[ZMod 2] U) = 6 := by
  let b : Module.Basis (Fin 2) (ZMod 2) U := Module.finBasisOfFinrankEq (ZMod 2) U hU
  let e : (U ≃ₗ[ZMod 2] U) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 2) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) U).symm.trans
      (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv)
  rw [Nat.card_congr e.toEquiv, Matrix.card_GL_field]
  simp [Fin.prod_univ_two]

@[expose] def g10FourRestrictHom (K : Subgroup (GLV V)) (U : Submodule (ZMod 2) V)
    (hK : Invariant K U) : K →* (U ≃ₗ[ZMod 2] U) where
  toFun k := g10FourRestrict K U hK k
  map_one' := LinearEquiv.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => Subtype.ext rfl

variable {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ : Subgroup (GLV V)}

theorem g10Four_invariant_orthogonal (hyp : G101Hyp B Γ v₁ W X X₀) {U : Submodule (ZMod 2) V}
    (hU : Invariant Γ U) : Invariant Γ (B.orthogonal U) := by
  intro γ hγ w hw
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro u hu
  have h1 := hyp.isometry γ hγ ((γ⁻¹ : GLV V) u) w
  have h2 : γ ((γ⁻¹ : GLV V) u) = u := by simp
  rw [h2] at h1
  rw [h1]
  exact (LinearMap.BilinForm.mem_orthogonal_iff.1 hw) _ (hU _ (Γ.inv_mem hγ) u hu)

theorem g10Four_sq_eq_one (hyp : G101Hyp B Γ v₁ W X X₀) {n : GLV V} (hnΓ : n ∈ Γ)
    {U : Submodule (ZMod 2) V} (hnU : ∀ u ∈ U, n u = u) (hnW : ∀ w ∈ B.orthogonal U, n w = w) :
    n * n = 1 := by
  ext v
  have hU : n v - v ∈ B.orthogonal U := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    have := hyp.isometry n hnΓ u v
    rw [hnU u hu] at this
    rw [map_sub, this]
    exact sub_self _
  have h1 : n (n v - v) = n v - v := hnW _ hU
  rw [map_sub] at h1
  show n (n v) = v
  have h2 : n (n v) = n v - v + n v := by
    rw [← h1]
    abel
  rw [h2]
  have h4 := g10Four_add_self (n v)
  calc n v - v + n v = (n v + n v) - v := by abel
    _ = 0 - v := by rw [h4]
    _ = v := by
      rw [zero_sub]
      exact neg_eq_of_add_eq_zero_right (g10Four_add_self v)

theorem g10Four_card_dvd (hyp : G101Hyp B Γ v₁ W X X₀) (h3 : pCoreOf 2 Γ = ⊥)
    {U : Submodule (ZMod 2) V} (hUΓ : Invariant Γ U) (hU2 : Module.finrank (ZMod 2) U = 2)
    (hd : Module.finrank (ZMod 2) V = 4) : Nat.card Γ ∣ 36 := by
  have hUp : Invariant Γ (B.orthogonal U) := g10Four_invariant_orthogonal hyp hUΓ
  have hUp2 : Module.finrank (ZMod 2) (B.orthogonal U) = 2 := by
    have := LinearMap.BilinForm.finrank_orthogonal hyp.nondegenerate' U
    omega
  let φ : Γ →* (U ≃ₗ[ZMod 2] U) × (B.orthogonal U ≃ₗ[ZMod 2] B.orthogonal U) :=
    (g10FourRestrictHom Γ U hUΓ).prod (g10FourRestrictHom Γ (B.orthogonal U) hUp)
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    have hU : ∀ u ∈ U, (γ : GLV V) u = u := by
      intro u hu
      have := congrArg (fun p => ((p.1 ⟨u, hu⟩ : U) : V)) hγ
      simpa [φ, g10FourRestrictHom] using this
    have hUp' : ∀ w ∈ B.orthogonal U, (γ : GLV V) w = w := by
      intro w hw
      have := congrArg (fun p => ((p.2 ⟨w, hw⟩ : B.orthogonal U) : V)) hγ
      simpa [φ, g10FourRestrictHom] using this
    let N : Subgroup (GLV V) := centralizerOn Γ U ⊓ centralizerOn Γ (B.orthogonal U)
    have hγN : (γ : GLV V) ∈ N := ⟨⟨γ.2, hU⟩, ⟨γ.2, hUp'⟩⟩
    have hNΓ : N ≤ Γ := fun n hn => hn.1.1
    have hnorm : Γ ≤ Subgroup.normalizer (N : Set (GLV V)) := by
      intro g hg
      have h1 := Subgroup.mem_normalizer_iff.1 (g10Four_le_normalizer_centralizerOn Γ U hUΓ hg)
      have h2 := Subgroup.mem_normalizer_iff.1
        (g10Four_le_normalizer_centralizerOn Γ (B.orthogonal U) hUp hg)
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · exact fun hx => ⟨(h1 x).1 hx.1, (h2 x).1 hx.2⟩
      · exact fun hx => ⟨(h1 x).2 hx.1, (h2 x).2 hx.2⟩
    have hp : IsPGroup 2 N := by
      intro g
      refine ⟨1, ?_⟩
      apply Subtype.ext
      have := g10Four_sq_eq_one hyp (hNΓ g.2) g.2.1.2 g.2.2.2
      simpa [pow_two] using this
    have hle : N ≤ pCoreOf 2 Γ :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hNΓ hnorm hp
    rw [h3] at hle
    have := hle hγN
    rw [Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hdvd := Subgroup.card_dvd_of_injective φ hinj
  rwa [Nat.card_prod, g10Four_card_linearEquiv_two U hU2,
    g10Four_card_linearEquiv_two (B.orthogonal U) hUp2] at hdvd

end CFSG.Quasithin
