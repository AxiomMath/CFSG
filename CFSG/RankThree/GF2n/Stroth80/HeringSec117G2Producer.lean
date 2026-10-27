module

public import CFSG.ClassicalGroups.Orthogonal.SiegelOverlap
public import CFSG.ClassicalGroups.Orthogonal.SiegelI4Order
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenInvolutions
public import CFSG.RankThree.GF2n.Stroth80.CarterSec11CMG2Rank
public import CFSG.HardMathSupport.Kantor79.LongRootGroup

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ClassicalGroups.Orthogonal.SiegelRT1 CFSG.HardMathSupport.Kantor79 QuadraticMap Module

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Qf : QuadraticForm K V} {X : Type} [Group X]
  {K' : Type} [Field K'] [Finite K'] [CharP K' 2]

omit [Finite K] [FiniteDimensional K V] in
theorem isLongRootElement_of_isConj (ρ : X →* (V ≃ₗ[K] V)) (hρQ : ∀ g v, Qf (ρ g v) = Qf v)
    {Y : Type*} [Group Y] (ψ : X ≃* Y) {t₀ x : X} (ht₀ : IsLongRootElement Qf (ρ t₀))
    (hx : IsConj (ψ x) (ψ t₀)) : IsLongRootElement Qf (ρ x) := by
  have hx' : IsConj x t₀ := by
    obtain ⟨c, hc⟩ := isConj_iff.mp hx
    refine isConj_iff.mpr ⟨ψ.symm c, ψ.injective ?_⟩
    simpa using hc
  obtain ⟨c, hc⟩ := isConj_iff.mp hx'.symm
  rw [← hc, map_mul, map_mul, map_inv]
  exact ht₀.conj (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (hρQ c))

omit [Finite K] [FiniteDimensional K V] [Finite K'] [CharP K' 2] in
theorem orderOf_eq_two_of_isLongRootElement (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)
    (ρ : X →* (V ≃ₗ[K] V)) (hρ : Function.Injective ρ) {t₀ : X}
    (ht₀ : IsLongRootElement Qf (ρ t₀)) : orderOf t₀ = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · refine hρ ?_
    rw [map_pow, map_one, _root_.sq, ht₀.mul_self]
  · intro h1
    have h2 := ht₀.finrank_movedSpace hnd
    rw [h1, map_one] at h2
    have h0 : movedSpace (1 : V ≃ₗ[K] V) = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨v, rfl⟩
      simp
    rw [h0, finrank_bot] at h2
    exact absurd h2 (by norm_num)

omit [CharP K 2] [Finite K'] [CharP K' 2] in
theorem card_dvd_card_GL [Finite X] (ρ : X →* (V ≃ₗ[K] V)) (hρ : Function.Injective ρ) :
    Nat.card X ∣ Nat.card (GL (Fin (finrank K V)) K) := by
  classical
  let b : Module.Basis (Fin (finrank K V)) K V := Module.finBasis K V
  let e : V ≃ₗ[K] (Fin (finrank K V) → K) := b.equivFun
  have h1 : Nat.card (V ≃ₗ[K] V) =
      Nat.card ((Fin (finrank K V) → K) ≃ₗ[K] (Fin (finrank K V) → K)) :=
    Nat.card_congr
      { toFun := fun u => (e.symm.trans u).trans e
        invFun := fun v => (e.trans v).trans e.symm
        left_inv := fun u => by ext x; simp
        right_inv := fun v => by ext x; simp }
  have h2 : Nat.card ((Fin (finrank K V) → K) ≃ₗ[K] (Fin (finrank K V) → K)) =
      Nat.card (GL (Fin (finrank K V)) K) :=
    Nat.card_congr ((Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin (finrank K V) → K))).toEquiv.symm)
  have : Finite (V →ₗ[K] V) := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun u : V ≃ₗ[K] V => (u : V →ₗ[K] V))
      (fun u v h => LinearEquiv.toLinearMap_injective h)
  rw [← h2, ← h1, Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv]
  exact Subgroup.card_subgroup_dvd_card _


theorem isConj_long_of_isLongRootElement (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)
    (ρ : X →* (V ≃ₗ[K] V)) (hρ : Function.Injective ρ) (hρQ : ∀ g v, Qf (ρ g v) = Qf v)
    (ψ : X ≃* ↥(adjointGroup .G2 K')) {t₀ : X} (ht₀ : IsLongRootElement Qf (ρ t₀))
    (hT1 : ∃ s t : ↥(adjointGroup .G2 K'),
      IsConj s ⟨pinnedX .G2 K' g2v 1, pinnedX_mem_adjointGroup g2v 1⟩ ∧
      IsConj t ⟨pinnedX .G2 K' g2v 1, pinnedX_mem_adjointGroup g2v 1⟩ ∧
      (s * t) ^ 4 ≠ 1 ∧ (s * t) ^ 8 = 1) :
    IsConj (ψ t₀) ⟨pinnedX .G2 K' g2c 1, pinnedX_mem_adjointGroup g2c 1⟩ := by
  have h2 : orderOf (ψ t₀) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_two_of_isLongRootElement hnd ρ hρ ht₀
  refine (even_G2_involutions_conjugate_to_root_elements K' (ringChar.eq K' 2) (ψ t₀)
    h2).resolve_right fun hv => ?_
  obtain ⟨s, t, hs, ht, h4, h8⟩ := hT1
  set φ : ↥(adjointGroup .G2 K') →* (V ≃ₗ[K] V) := ρ.comp ψ.symm.toMonoidHom with hφ
  have hφinj : Function.Injective φ := hρ.comp ψ.symm.injective
  have hsieg : ∀ z : ↥(adjointGroup .G2 K'),
      IsConj z ⟨pinnedX .G2 K' g2v 1, pinnedX_mem_adjointGroup g2v 1⟩ →
        IsLongRootElement Qf (φ z) := by
    intro z hz
    refine isLongRootElement_of_isConj ρ hρQ ψ ht₀ ?_
    simpa using hz.trans hv.symm
  rcases pow_four_eq_one_or_odd_orderOf_mul hnd (hsieg s hs) (hsieg t ht) with h | h
  · rw [← map_mul, ← map_pow] at h
    exact h4 (hφinj (h.trans (map_one φ).symm))
  · rw [← map_mul, orderOf_injective φ hφinj] at h
    have hdvd : orderOf (s * t) ∣ 2 ^ 3 := orderOf_dvd_of_pow_eq_one h8
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rcases k with _ | k
    · rw [pow_zero, orderOf_eq_one_iff] at hk
      exact h4 (by rw [hk, one_pow])
    · rw [hk, pow_succ] at h
      exact absurd (Nat.odd_mul.mp h).2 (by decide)

theorem finrank_eq_six_of_g2 (hK4 : 4 ≤ Nat.card K) (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)
    (ρ : X →* (V ≃ₗ[K] V)) (hρ : Function.Injective ρ) (hρQ : ∀ g v, Qf (ρ g v) = Qf v)
    (hV : commutatorSpace ρ.range = ⊤) (hKK : Nat.card K' = Nat.card K)
    (ψ : X ≃* ↥(adjointGroup .G2 K')) {t₀ : X} (ht₀ : IsLongRootElement Qf (ρ t₀))
    (hT1 : ∃ s t : ↥(adjointGroup .G2 K'),
      IsConj s ⟨pinnedX .G2 K' g2v 1, pinnedX_mem_adjointGroup g2v 1⟩ ∧
      IsConj t ⟨pinnedX .G2 K' g2v 1, pinnedX_mem_adjointGroup g2v 1⟩ ∧
      (s * t) ^ 4 ≠ 1 ∧ (s * t) ^ 8 = 1)
    (hT2 : ∃ d₁ d₂ d₃ e y : ↥(adjointGroup .G2 K'),
      IsConj d₁ ⟨pinnedX .G2 K' g2c 1, pinnedX_mem_adjointGroup g2c 1⟩ ∧
      IsConj d₂ ⟨pinnedX .G2 K' g2c 1, pinnedX_mem_adjointGroup g2c 1⟩ ∧
      IsConj d₃ ⟨pinnedX .G2 K' g2c 1, pinnedX_mem_adjointGroup g2c 1⟩ ∧
      IsConj e ⟨pinnedX .G2 K' g2c 1, pinnedX_mem_adjointGroup g2c 1⟩ ∧
      IsConj y ⟨pinnedX .G2 K' g2c 1, pinnedX_mem_adjointGroup g2c 1⟩ ∧
      IsConj (e * y) ⟨pinnedX .G2 K' g2c 1, pinnedX_mem_adjointGroup g2c 1⟩ ∧
      Subgroup.closure ({d₁, d₂, d₃, e} : Set ↥(adjointGroup .G2 K')) = ⊤ ∧
      y ∈ Subgroup.closure ({d₁, d₂, d₃} : Set ↥(adjointGroup .G2 K')) ∧ e * y = y * e) :
    finrank K V = 6 := by
  have hlong := isConj_long_of_isLongRootElement hnd ρ hρ hρQ ψ ht₀ hT1
  have hsieg : ∀ z : ↥(adjointGroup .G2 K'),
      IsConj z ⟨pinnedX .G2 K' g2c 1, pinnedX_mem_adjointGroup g2c 1⟩ →
        IsLongRootElement Qf (ρ (ψ.symm z)) := fun z hz =>
    isLongRootElement_of_isConj ρ hρQ ψ ht₀ (by simpa using hz.trans hlong.symm)
  obtain ⟨d₁, d₂, d₃, e, y, h₁, h₂, h₃, he, hy, hey, hgen, hyH, hcomm⟩ := hT2
  have hfin : Finite X := Finite.of_equiv _ ψ.symm.toEquiv
  have := Fintype.ofFinite K
  have hp : ringChar K = 2 := ringChar.eq K 2
  obtain ⟨m, -, hm⟩ := FiniteField.card K 2
  have hKm : Nat.card K = 2 ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hm]
  have hm2 : 2 ≤ (m : ℕ) := by
    by_contra h
    have : (m : ℕ) ≤ 1 := by omega
    have : 2 ^ (m : ℕ) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
    omega
  have h6 : 6 ≤ finrank K V := by
    refine six_le_of_card_adjointGroup_G2_dvd_card_GL hm2 hKm ?_
    have hc : Nat.card (adjointGroup .G2 K) = Nat.card X := by
      rw [Nat.card_congr ψ.toEquiv, (exact_G2_finite_order K' hKK).2.1,
        (exact_G2_finite_order K (q := Nat.card K) rfl).2.1]
    rw [hc]
    exact card_dvd_card_GL ρ hρ
  refine finrank_eq_six_of_closure_four hnd ρ hV (hsieg d₁ h₁) (hsieg d₂ h₂) (hsieg d₃ h₃)
    (hsieg e he) (hsieg y hy) ?_ ?_ (by rw [← map_mul, ← map_mul, hcomm]) ?_ h6
  · have := congrArg (Subgroup.map ψ.symm.toMonoidHom) hgen
    rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective _ ψ.symm.surjective] at this
    simpa [Set.image_insert_eq] using this
  · have := Subgroup.mem_map_of_mem ψ.symm.toMonoidHom hyH
    rw [MonoidHom.map_closure] at this
    simpa [Set.image_insert_eq] using this
  · rw [← map_mul]
    exact hsieg (e * y) hey

end CFSG.RankThree.GF2n.Stroth80
