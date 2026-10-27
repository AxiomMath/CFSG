module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTrialityLayerDefs
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTrialityLayerElt
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTrialityEightRest
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOmPlusFourField
public import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613KGField

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.StandardType.Triality

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

namespace OrdPTriLayer

section Fix

variable {H : Type*} [Group H]

theorem ggFix_inv (a : MulAut H) : ggFix a⁻¹ = ggFix a := by
  ext x
  rw [mem_ggFix, mem_ggFix]
  constructor
  · intro h
    calc a x = a (a⁻¹ x) := by rw [h]
      _ = x := MulAut.apply_inv_self _ a x
  · intro h
    calc a⁻¹ x = a⁻¹ (a x) := by rw [h]
      _ = x := MulAut.inv_apply_self _ a x

theorem ggFix_mul_mul_inv (φ a : MulAut H) :
    ggFix (φ * a * φ⁻¹) = (ggFix a).map φ.toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv, mem_ggFix, mem_ggFix]
  change φ (a (φ⁻¹ x)) = x ↔ a (φ⁻¹ x) = φ⁻¹ x
  constructor
  · intro h
    apply φ.injective
    rw [h, MulAut.apply_inv_self _ φ x]
  · intro h
    rw [h, MulAut.apply_inv_self _ φ x]

theorem le_largeEvenLayer_self {X : Subgroup H} (hX : CFSG.Assembly.IsQuasisimple ↥X) :
    X ≤ LargeEvenLayer X :=
  le_sSup (show IsComponentOf X X from ⟨le_rfl, IsSubnormal.refl X, hX⟩)

theorem conj_mem_largeEvenLayer {g : H} {τ β : MulAut H}
    (hβ : β = MulAut.conj g * τ * (MulAut.conj g)⁻¹)
    (hq : CFSG.Assembly.IsQuasisimple ↥(ggFix τ)) {x : H} (hx : x ∈ ggFix τ) :
    MulAut.conj g x ∈ LargeEvenLayer (ggFix β) := by
  rw [hβ, ggFix_mul_mul_inv,
    largeEvenLayer_map_of_injective _ (MulAut.conj g).injective (ggFix τ)]
  exact ⟨x, le_largeEvenLayer_self hq hx, rfl⟩

theorem conj_mul_inv_eq (γ : H) {a b : MulAut H} (hab : a⁻¹ = b) :
    (MulAut.conj γ * a)⁻¹ = MulAut.conj (b γ⁻¹) * b := by
  rw [mul_inv_rev, hab, ← map_inv, D4Rank.mulAut_mul_conj]

end Fix

section Gamma

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem theta_pow_mul_fieldAutP_cube (k : ℕ) (σ : K ≃+* K) :
    (theta ^ k * AutOm.fieldAutP 4 σ) ^ 3 = AutOm.fieldAutP 4 (σ ^ 3) := by
  have hc : Commute (theta ^ k) (AutOm.fieldAutP 4 σ : MulAut (Om8 K)) :=
    Commute.pow_left (theta_fieldAutP σ) k
  rw [hc.mul_pow, ← pow_mul, mul_comm k 3, pow_mul, theta_cube, one_pow, one_mul, map_pow]

theorem cube_eq_one_of_conj_mul_cube {γ : Om8 K} {k : ℕ} {σ : K ≃+* K}
    (h : (MulAut.conj γ * (theta ^ k * AutOm.fieldAutP 4 σ)) ^ 3 = 1) : σ ^ 3 = 1 := by
  obtain ⟨γ', hγ'⟩ := D4Rank.conj_mul_cube (theta ^ k * AutOm.fieldAutP 4 σ) γ
  rw [h, theta_pow_mul_fieldAutP_cube] at hγ'
  have hmem : AutOm.fieldAutP 4 (σ ^ 3) ∈ Inn (Om8 K) := by
    refine ⟨γ'⁻¹, ?_⟩
    rw [map_inv]
    exact inv_eq_of_mul_eq_one_right hγ'.symm
  exact L613KG.eq_one_of_fieldAutP_eq_one (NbrGraphD4.fieldAutP_eq_one_of_mem_inner hmem)

theorem theta_sq_mul_fieldAutP_inv (σ : K ≃+* K) :
    (theta ^ 2 * AutOm.fieldAutP 4 σ)⁻¹ = theta * AutOm.fieldAutP 4 σ⁻¹ := by
  refine inv_eq_of_mul_eq_one_right ?_
  calc theta ^ 2 * AutOm.fieldAutP 4 σ * (theta * AutOm.fieldAutP 4 σ⁻¹)
      = theta ^ 2 * (AutOm.fieldAutP 4 σ * theta) * AutOm.fieldAutP 4 σ⁻¹ := by
        simp only [mul_assoc]
    _ = theta ^ 2 * (theta * AutOm.fieldAutP 4 σ) * AutOm.fieldAutP 4 σ⁻¹ := by
        rw [theta_fieldAutP]
    _ = theta ^ 3 * (AutOm.fieldAutP 4 σ * AutOm.fieldAutP 4 σ⁻¹) := by
        rw [pow_succ theta 2]; simp only [mul_assoc]
    _ = 1 := by rw [theta_cube, ← map_mul, mul_inv_cancel, map_one, one_mul]

theorem theta_sq_inv : (theta ^ 2 : MulAut (Om8 K))⁻¹ = theta :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ, theta_cube])

omit [Finite K] [CharP K 2] in
theorem layerAlt_of_eq {X Y : Subgroup (Om8 K)} (hXY : X = Y) {f : ℕ}
    (h : (∃ x ∈ LargeEvenLayer X, orderOf x = 8) ∨
      LieModel (↥(LargeEvenLayer X) ⧸ Subgroup.center ↥(LargeEvenLayer X)) .PSL 3 2 f) :
    (∃ x ∈ LargeEvenLayer Y, orderOf x = 8) ∨
      LieModel (↥(LargeEvenLayer Y) ⧸ Subgroup.center ↥(LargeEvenLayer Y)) .PSL 3 2 f := by
  subst hXY
  exact h

theorem ureg_mem_ggFix_theta_mul (σ : K ≃+* K) :
    ureg ∈ ggFix (theta * AutOm.fieldAutP 4 σ : MulAut (Om8 K)) := by
  rw [mem_ggFix, MulAut.mul_apply, fieldAutP_ureg, theta_ureg]

end Gamma

end OrdPTriLayer

open OrdPTriLayer

theorem ggD4GraphFieldLayerInput_of_lang (hL : GGD4GraphFieldLangInput)
    (hQ : GGD4GraphFieldFixQuasisimpleInput) : GGD4GraphFieldLayerInput := by
  intro K _ _ _ γ k σ hk hσ1 hβ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hσo : orderOf σ = 3 :=
    orderOf_eq_prime (cube_eq_one_of_conj_mul_cube hβ) fun h => hσ1 (by rw [h, map_one])
  have key : ∀ τ : K ≃+* K, orderOf τ = 3 → ∀ γ' : Om8 K,
      (MulAut.conj γ' * (theta * AutOm.fieldAutP 4 τ)) ^ 3 = 1 →
        ∃ x ∈ LargeEvenLayer (ggFix (MulAut.conj γ' * (theta * AutOm.fieldAutP 4 τ))),
          orderOf x = 8 := by
    intro τ hτ γ' h3
    obtain ⟨g, hg⟩ := hL K τ hτ γ' h3
    exact ⟨MulAut.conj g ureg, conj_mem_largeEvenLayer hg (hQ K τ hτ) (ureg_mem_ggFix_theta_mul τ),
      by rw [MulEquiv.orderOf_eq, orderOf_ureg]⟩
  rcases hk with rfl | rfl
  · rw [pow_one] at hβ ⊢
    exact key σ hσo γ hβ
  · have hinv := conj_mul_inv_eq γ (theta_sq_mul_fieldAutP_inv σ)
    have h3 : (MulAut.conj ((theta * AutOm.fieldAutP 4 σ⁻¹ : MulAut (Om8 K)) γ⁻¹) *
        (theta * AutOm.fieldAutP 4 σ⁻¹)) ^ 3 = 1 := by
      rw [← hinv, inv_pow, hβ, inv_one]
    obtain ⟨x, hx, hxo⟩ := key σ⁻¹ (by rw [orderOf_inv, hσo]) _ h3
    refine ⟨x, ?_, hxo⟩
    rwa [← hinv, ggFix_inv] at hx

theorem ggD4GraphLayerInput_of_class (hC : GGD4GraphClassInput)
    (hQ : GGD4GraphFixQuasisimpleInput) : GGD4GraphLayerInput := by
  intro K _ _ _ f hK h3 γ k hk hβ
  have hQ' : CFSG.Assembly.IsQuasisimple ↥(ggFix (theta : MulAut (Om8 K))) :=
    hQ K (by rw [hK]; exact h3)
  have key : ∀ γ' : Om8 K, (MulAut.conj γ' * theta) ^ 3 = 1 →
      (∃ x ∈ LargeEvenLayer (ggFix (MulAut.conj γ' * theta)), orderOf x = 8) ∨
        LieModel (↥(LargeEvenLayer (ggFix (MulAut.conj γ' * theta))) ⧸
          Subgroup.center ↥(LargeEvenLayer (ggFix (MulAut.conj γ' * theta)))) .PSL 3 2 f := by
    intro γ' h3'
    rcases hC K f hK h3 γ' h3' with ⟨g, hg⟩ | h
    · exact Or.inl ⟨MulAut.conj g ureg, conj_mem_largeEvenLayer hg hQ' (mem_ggFix.2 theta_ureg),
        by rw [MulEquiv.orderOf_eq, orderOf_ureg]⟩
    · exact Or.inr h
  rcases hk with rfl | rfl
  · exact layerAlt_of_eq (by rw [pow_one]) (key γ (by rwa [pow_one] at hβ))
  · have hinv := conj_mul_inv_eq γ (theta_sq_inv (K := K))
    have h3' : (MulAut.conj (theta γ⁻¹) * theta) ^ 3 = 1 := by
      rw [← hinv, inv_pow, hβ, inv_one]
    exact layerAlt_of_eq (by rw [← hinv, ggFix_inv]) (key _ h3')

end CFSG.StandardType
