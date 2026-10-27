module

public import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6CrossPrime
public import CFSG.RankThree.Chevalley.SteinbergBTEvenTwistedE6SixTorus
public import CFSG.RankThree.CentralCover.SteinbergBNReflectionNormalizers

public section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Assembly
open CFSG.Assembly.RankThreeEven (localRank)

@[expose] def cartanFunctional (τ : Tag) (p : ℕ) (i : Fin τ.rank) :
    (Fin τ.rank → ZMod p) →ₗ[ZMod p] ZMod p where
  toFun v := ∑ j, (τ.cartan j i : ZMod p) * v j
  map_add' v w := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

theorem cartanFunctional_apply (τ : Tag) (p : ℕ) (i : Fin τ.rank) (v : Fin τ.rank → ZMod p) :
    cartanFunctional τ p i v = ∑ j, (τ.cartan j i : ZMod p) * v j := rfl

theorem cartanFunctional_single (τ : Tag) (p : ℕ) (i : Fin τ.rank) :
    cartanFunctional τ p i (Pi.single i 1) = 2 := by
  classical
  rw [cartanFunctional_apply, Finset.sum_eq_single i (fun j _ hj => by
    rw [Pi.single_eq_of_ne hj, mul_zero]) (fun h => absurd (Finset.mem_univ i) h),
    Pi.single_eq_same, mul_one, Tag.cartan_self]
  norm_num

theorem even_twisted_E6_split_prime_central_cover_two_local_rank {G : Type} [Group G] [Finite G]
    (Y : Subgroup G) {f p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ 2 ^ f + 1)
    (hmod : ChevalleyExceptionalModel (Y ⧸ Subgroup.center Y) .twistedE6 2 f) :
    ∃ u : G, u ∈ Y ∧ orderOf u = 2 ∧ ∃ A : Subgroup G, A ≤ Y ⊓ Subgroup.centralizer {u} ∧
      IsElemAbelian p A ∧ Nat.card A = p ^ 5 ∧ 5 ≤ localRank p G := by
  classical
  obtain ⟨⟨-, hf, -⟩, hmodel⟩ := hmod
  obtain ⟨K, _, _, hK, σ, hσ, φ, hφ, hker⟩ :=
    exists_surj_graphFixedRootGroup_of_model Nat.prime_two hf hmodel
  have : CharP K 2 := ringChar.of_eq
    (ringChar_eq_of_card Nat.prime_two (by omega : 1 ≤ f * 2) (by rw [hK, ← pow_mul]))
  obtain ⟨ρ, hρu, hρv, -⟩ := exceptional_ordinary_rank_one_central_image TwistTag.E6.tag K
    ⟨3, by decide⟩
  obtain ⟨⟨ζ, hζ⟩, ⟨ω, hω⟩, hmain⟩ :=
    even_twisted_E6_nonsplit_six_torus_and_rational_reflections hf K hK σ hσ hp hp3 hpq ρ hρu
      hρv
  obtain ⟨-, -, -, hDC, θ, -, hn⟩ := hmain ζ hζ ω hω
  set g := sixTorusProd ρ (sixTorusP ω)⁻¹
  set c : MulAut (ModGL TwistTag.E6.tag K) := MulAut.conj g
  set Cs := (graphFixedRootGroup TwistTag.E6 K σ).map c.toMonoidHom
  let ψ : graphFixedRootGroup TwistTag.E6 K σ ≃* Cs :=
    (graphFixedRootGroup TwistTag.E6 K σ).equivMapOfInjective c.toMonoidHom c.injective
  let φ' : Y →* Cs := ψ.toMonoidHom.comp φ
  have hφ' : Function.Surjective φ' := ψ.surjective.comp hφ
  have hker' : φ'.ker ≤ Subgroup.center Y := by
    intro y hy
    rw [← hker, MonoidHom.mem_ker]
    have h1 : ψ (φ y) = 1 := hy
    exact ψ.injective (h1.trans (map_one ψ).symm)
  let e : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p) →* Cs :=
    (Subgroup.inclusion hDC).comp θ.toMonoidHom
  have he : Function.Injective e :=
    (Subgroup.inclusion_injective hDC).comp θ.injective
  let n : Fin TwistTag.E6.tag.rank → Cs := fun i => ⟨_, (hn i).1⟩
  have hnact : ∀ i v, n i * e (.ofAdd v) * (n i)⁻¹ =
      e (.ofAdd (v - cartanFunctional TwistTag.E6.tag p i v • Pi.single i 1)) := fun i v =>
    Subtype.ext ((hn i).2.2.2 v)
  have hn1 : orderOf (n ⟨0, by decide⟩) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact (hn ⟨0, by decide⟩).2.1
  obtain ⟨-, u, huY, hu, A, hA, hAab, hAcard, hrank⟩ :=
    CFSG.RankThree.CentralCover.reflection_normalizers_actual_central_cover_fixed_hyperplane_rank
      Y φ' hφ' hker' hp (by omega) (by decide) e he (cartanFunctional TwistTag.E6.tag p)
      (cartanFunctional_single TwistTag.E6.tag p) n hnact hn1
  exact ⟨u, huY, hu, A, hA, hAab, hAcard, hrank⟩

theorem twisted_E6_cross_prime_actual_component_quadratic_factor_exclusion {X : Type} [Group X]
    [Finite X] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (N : Subgroup X) [N.Normal]
    (hN : ¬p ∣ Nat.card N) (hX : localRank p X ≤ 3) (L : Subgroup (X ⧸ N)) {ℓ f : ℕ}
    (hmod : ChevalleyExceptionalModel (L ⧸ Subgroup.center L) .twistedE6 ℓ f) :
    ¬p ∣ (ℓ ^ f) ^ 2 - 1 ∧
      ∀ (f' : ℕ), p ∣ 2 ^ f' + 1 → ∀ (G : Type) [Group G] [Finite G] (Y : Subgroup G),
        ChevalleyExceptionalModel (Y ⧸ Subgroup.center Y) .twistedE6 2 f' →
        ∃ u : G, u ∈ Y ∧ orderOf u = 2 ∧ ∃ A : Subgroup G,
          A ≤ Y ⊓ Subgroup.centralizer {u} ∧ IsElemAbelian p A ∧ Nat.card A = p ^ 5 ∧
          5 ≤ localRank p G := by
  refine ⟨fun hpq => ?_, fun f' hpq G _ _ Y hY =>
    even_twisted_E6_split_prime_central_cover_two_local_rank Y hp hp3 hpq hY⟩
  have hℓ : ℓ.Prime := hmod.1.1
  have hf : 1 ≤ f := hmod.1.2.1
  obtain ⟨hminus, hplus⟩ :=
    twisted_E6_cross_prime_actual_component_toral_factor_restriction hp hp3 N hN hX L hℓ hf hmod
  have hfac : (ℓ ^ f) ^ 2 - 1 = (ℓ ^ f + 1) * (ℓ ^ f - 1) := by
    have := Nat.sq_sub_sq (ℓ ^ f) 1
    rwa [one_pow] at this
  rw [hfac] at hpq
  rcases (Nat.Prime.dvd_mul hp).1 hpq with h | h
  · by_cases hℓ2 : ℓ = 2
    · subst hℓ2
      have hQ := CFSG.RankThree.Classical2.localRank_quotient_le hp (by omega) N hN
      obtain ⟨-, -, -, -, -, -, -, hrank⟩ :=
        even_twisted_E6_split_prime_central_cover_two_local_rank L hp hp3 h hmod
      omega
    · exact (hplus hℓ2).1 h
  · exact hminus h

end CFSG.RankThree.Chevalley
