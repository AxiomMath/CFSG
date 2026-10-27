module

public import CFSG.RankThree.PartOne.S11.CatalogLeaves
public import CFSG.RankThree.PartOne.S11c.G2Plane
public import CFSG.RankThree.Chevalley.SteinbergCFOddG2CentralCoverFiveActors
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.RankThree.LocalRank.SelectorCases

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.RankThree.Chevalley CFSG.LieType.Ree
open CFSG.Assembly.RankThreeEven (localRank)

theorem g2_prime_order_automorphism_inner {T : Type} [Group T] {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hmod : ChevalleyExceptionalModel T .G2 ℓ f)
    (hbound : (3 < ℓ → f = 1) ∧ (ℓ = 3 → f ≤ 2)) {q : ℕ} (hq : q.Prime) (hq4 : 4 < q)
    (β : MulAut T) (hβ : orderOf β = q) : β ∈ (MulAut.conj : T →* MulAut T).range := by
  classical
  have hf : 1 ≤ f := hmod.1.2.1
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmod.2
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ hf hK
  set e' : T ≃* adjointGroup .G2 K := e.trans (adjointQuotientEquiv .G2 K) with he'
  refine mem_range_conj_of_congr e' β ?_
  have hβ' : orderOf (MulAut.congr e' β) = q := by
    rw [MulEquiv.orderOf_eq, hβ]
  have hℓ3 : 3 ≤ ℓ := by
    rcases hℓ.eq_two_or_odd' with h | h
    · exact absurd h hℓ2
    · have := hℓ.two_le
      obtain ⟨k, hk⟩ := h
      omega
  rcases lt_or_eq_of_le hℓ3 with hlt | heq
  ·
    have hf1 := hbound.1 hlt
    obtain ⟨-, Θ, -, -, hΘker, -⟩ :=
      odd_F4_and_nonexceptional_G2_automorphism_normal_form hℓ hℓ2 hf K hK .G2
        (Or.inr ⟨rfl, by omega⟩)
    rw [← hΘker, MonoidHom.mem_ker]
    exact ringEquiv_eq_one_of_card_eq_prime hℓ (by rw [hK, hf1, pow_one]) _
  ·
    subst heq
    have hf2 := hbound.2 rfl
    have : CharP K ReeTag.G2.prime := ‹CharP K 3›
    obtain ⟨-, -, ⟨Θ, -, -, hΘker⟩, -⟩ := G2_three_exact_automorphism_normal_form hf K hK
    have : NeZero (2 * f) := ⟨by omega⟩
    have hinner : ∀ γ : MulAut (adjointGroup ReeTag.G2.tag K), orderOf γ = q →
        γ ∈ (MulAut.conj : adjointGroup ReeTag.G2.tag K →*
          MulAut (adjointGroup ReeTag.G2.tag K)).range := by
      intro γ hγ
      rw [← hΘker, MonoidHom.mem_ker]
      have h1 : orderOf (Θ γ) ∣ q := by
        rw [← hγ]
        exact orderOf_map_dvd _ _
      have h2 : orderOf (Θ γ) ∣ 2 * f := by
        have := orderOf_dvd_natCard (Θ γ)
        rwa [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card] at this
      have h3 : orderOf (Θ γ) = 1 := by
        rcases (Nat.dvd_prime hq).1 h1 with h | h
        · exact h
        · rw [h] at h2
          have := Nat.le_of_dvd (by omega) h2
          omega
      exact orderOf_eq_one_iff.1 h3
    exact hinner _ hβ'

theorem conj_injective_of_mulEquiv_adjointGroup {T : Type*} [Group T] {τ : Tag} {K : Type}
    [Field K] [Finite K] (e : T ≃* adjointGroup τ K) :
    Function.Injective (MulAut.conj : T →* MulAut T) := by
  intro g g' hgg
  have hc : g'⁻¹ * g ∈ Subgroup.center T := Subgroup.mem_center_iff.2 fun x => by
    have h1 := congrArg (fun α : MulAut T => α x) hgg
    simp only [MulAut.conj_apply] at h1
    calc x * (g'⁻¹ * g) = g'⁻¹ * (g' * x * g'⁻¹) * g := by group
      _ = g'⁻¹ * (g * x * g⁻¹) * g := by rw [h1]
      _ = g'⁻¹ * g * x := by group
  have h2 : e (g'⁻¹ * g) ∈ Subgroup.center (adjointGroup τ K) := by
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hc x]
  rw [center_adjointGroup_eq_bot, Subgroup.mem_bot, map_eq_one_iff _ e.injective,
    inv_mul_eq_one] at h2
  exact h2.symm

theorem actualCoverOddG2PlaneCentralization : ActualCoverOddG2PlaneCentralization := by
  intro H _ _ he X ℓ f hℓ hℓ2 hf hmod p E U hplane
  have hloc : localRank ℓ H ≤ 3 := by
    rcases Nat.eq_zero_or_pos (localRank ℓ H) with h0 | hpos
    · omega
    · exact (CFSG.RankThree.Theta.localRank_le_twoLocalOddRank hℓ hℓ2
        (CFSG.RankThree.LocalRank.prime_dvd_card_of_localRank_pos hℓ hpos)).trans he
  obtain ⟨hf1, hf2, -⟩ := odd_G2_actual_central_cover_rank_three_five_actors_inner X hℓ hℓ2
    (QuotientGroup.mk' (Subgroup.center X)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']) hloc hmod
  have hp := hplane.prime
  have hp3 := hplane.three_lt
  have hp4 : 4 < p := by
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two (by omega)
    omega
  have : IsElementaryAbelian p E := hplane.elementary
  have hpinner : ∀ β ∈ E, β ∈ (MulAut.conj : (X ⧸ Subgroup.center X) →*
      MulAut (X ⧸ Subgroup.center X)).range := by
    intro β hβ
    have hβp : β ^ p = 1 := by
      have := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p E) ⟨β, hβ⟩
      simpa using congrArg Subtype.val this
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hβp) with h1 | h1
    · rw [orderOf_eq_one_iff.1 h1]
      exact ⟨1, map_one _⟩
    · exact g2_prime_order_automorphism_inner hℓ hℓ2 hmod ⟨hf1, hf2⟩ hp hp4 β h1
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmod.2
  have hKodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hℓ.odd_of_ne_two hℓ2).pow
  let e' : (X ⧸ Subgroup.center X) ≃* adjointGroup .G2 K := e.trans (adjointQuotientEquiv .G2 K)
  have hinj := conj_injective_of_mulEquiv_adjointGroup e'
  let E' : Subgroup (X ⧸ Subgroup.center X) :=
    E.comap (MulAut.conj : (X ⧸ Subgroup.center X) →* MulAut (X ⧸ Subgroup.center X))
  have hE'map : E'.map (MulAut.conj : (X ⧸ Subgroup.center X) →*
      MulAut (X ⧸ Subgroup.center X)) = E := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.2 fun β hβ => hpinner β hβ
  let eEE' : E' ≃* E :=
    (Subgroup.equivMapOfInjective E' MulAut.conj hinj).trans (MulEquiv.subgroupCongr hE'map)
  have : Fact p.Prime := ⟨hp⟩
  have hE'el : IsElementaryAbelian p E' :=
    isElementaryAbelian_of_mulEquiv' eEE'.symm hplane.elementary
  have hE'card : Nat.card E' = p ^ 2 := by
    rw [Nat.card_congr eEE'.toEquiv]
    exact hplane.card
  have hE'U : ∀ x ∈ E', ∀ u ∈ U, x * u * x⁻¹ ∈ U := fun x hx u hu =>
    hplane.normalized (MulAut.conj x) hx u hu
  let φ : (X ⧸ Subgroup.center X) →* ModGL .G2 K :=
    (adjointGroup .G2 K).subtype.comp e'.toMonoidHom
  have hφ : Function.Injective φ := Subtype.val_injective.comp e'.injective
  have hφC : ∀ x, φ x ∈ adjointGroup .G2 K := fun x => (e' x).2
  have hE'φ : IsElementaryAbelian p (E'.map φ) := IsElementaryAbelian.map (A := E') φ
  have hUfin : Finite (U.map φ) :=
    Finite.of_surjective (fun u : U => (⟨φ u, u, u.2, rfl⟩ : U.map φ))
      (by rintro ⟨_, u, hu, rfl⟩; exact ⟨⟨u, hu⟩, rfl⟩)
  have hmain := g2_plane_centralizes hKodd hp hp3 (E := E'.map φ) (U := U.map φ)
    (by rintro _ ⟨y, -, rfl⟩; exact hφC y) (by rintro _ ⟨y, -, rfl⟩; exact hφC y)
    (by rw [Subgroup.card_map_of_injective hφ]; exact hE'card)
    (hplane.two_group.map φ)
    (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨u, hu, rfl⟩
      exact ⟨x * u * x⁻¹, hE'U x hx u hu, by simp [map_mul]⟩)
  intro β hβ u hu
  obtain ⟨x, hx, rfl⟩ : ∃ x ∈ E', MulAut.conj x = β := by
    have : β ∈ E'.map (MulAut.conj : (X ⧸ Subgroup.center X) →*
      MulAut (X ⧸ Subgroup.center X)) := hE'map ▸ hβ
    obtain ⟨x, hx, hxβ⟩ := this
    exact ⟨x, hx, hxβ⟩
  have hc := hmain (φ x) ⟨x, hx, rfl⟩ (φ u) ⟨u, hu, rfl⟩
  have hxu : x * u = u * x := hφ (by rw [map_mul, map_mul]; exact hc)
  change x * u * x⁻¹ = u
  rw [mul_inv_eq_iff_eq_mul]
  exact hxu

end CFSG.RankThree.PartOne
