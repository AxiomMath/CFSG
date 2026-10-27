module

public import CFSG.RankThree.Transfer.FixedPoints
import Mathlib.GroupTheory.Abelianization.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec8

open MulAction
open CFSG.RankThree.Transfer (cosetValue cosetValue_coe smul_coe_eq_iff
  transfer_eq_prod_fixed_of_orderOf_lt)

theorem prod_eq_one_of_isPGroup {D X A : Type*} [Group D] [MulAction D X] [Fintype X]
    [CommMonoid A] {p : ℕ} [Fact p.Prime] (hD : IsPGroup p D) (f : X → A)
    (hinv : ∀ (d : D) (y : X), f (d • y) = f y) (hpow : ∀ y, f y ^ p = 1)
    (hfix : ∀ y, (∀ d : D, d • y = y) → f y = 1) : ∏ y, f y = 1 := by
  classical
  rw [← Finset.prod_fiberwise Finset.univ
    (fun y : X => (Quotient.mk'' y : Quotient (orbitRel D X)))]
  refine Finset.prod_eq_one fun ω _ => ?_
  have hfib : ∀ y : X, (Quotient.mk'' y : Quotient (orbitRel D X)) = ω ↔
      y ∈ orbit D (Quotient.out ω) := by
    intro y
    conv_lhs => rw [← Quotient.out_eq ω]
    rw [Quotient.mk''_eq_mk, Quotient.eq, orbitRel_apply]
  have hconst : ∀ y ∈ Finset.univ.filter
      (fun y : X => (Quotient.mk'' y : Quotient (orbitRel D X)) = ω),
        f y = f (Quotient.out ω) := by
    intro y hy
    obtain ⟨d, rfl⟩ := (hfib y).mp (Finset.mem_filter.mp hy).2
    exact hinv d _
  refine (Finset.prod_eq_pow_card hconst).trans ?_
  have hcard : (Finset.univ.filter
      (fun y : X => (Quotient.mk'' y : Quotient (orbitRel D X)) = ω)).card =
        Fintype.card (orbit D (Quotient.out ω)) := by
    rw [← Set.toFinset_card]
    congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset]
    exact hfib y
  obtain ⟨n, hn⟩ := hD.card_orbit (Quotient.out ω)
  rw [hcard, Fintype.card_eq_nat_card, hn]
  rcases n with _ | n
  · rw [pow_zero, pow_one]
    refine hfix _ fun d => ?_
    have h1 : Fintype.card (orbit D (Quotient.out ω)) = 1 := by
      rw [Fintype.card_eq_nat_card, hn, pow_zero]
    exact mem_fixedPoints.mp (mem_fixedPoints_iff_card_orbit_eq_one.mpr h1) d
  · rw [pow_succ', pow_mul, hpow, one_pow]

theorem transfer_eq_pow_index_of_extremal {G : Type*} [Group G] [Finite G] {p : ℕ}
    [hp : Fact p.Prime] (P : Sylow p G) {A : Type*} [CommGroup A] (ϕ : (P : Subgroup G) →* A)
    {x : G} (hx : x ∈ (P : Subgroup G)) (hxp : x ^ p = 1)
    (hfus : ∀ t : G,
      (∀ y ∈ (P : Subgroup G) ⊓ Subgroup.centralizer {x}, t⁻¹ * y * t ∈ (P : Subgroup G)) →
        ∀ ht : t⁻¹ * x * t ∈ (P : Subgroup G), ϕ ⟨t⁻¹ * x * t, ht⟩ = ϕ ⟨x, hx⟩) :
    ϕ.transfer x = ϕ ⟨x, hx⟩ ^ (P : Subgroup G).index := by
  classical
  let := Fintype.ofFinite (G ⧸ (P : Subgroup G))
  have hϕ : ∀ h : (P : Subgroup G), orderOf (h : G) < orderOf x → ϕ h = 1 := by
    intro h hlt
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp P.isPGroup' h
    rw [Subgroup.orderOf_coe, hk] at hlt
    have hxle : orderOf x ≤ p := orderOf_le_of_pow_eq_one hp.out.pos hxp
    have hk0 : k = 0 := by
      by_contra hk0
      exact absurd (hlt.trans_le hxle) (not_lt.mpr (Nat.le_self_pow hk0 p))
    rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
    rw [hk, map_one]
  rw [transfer_eq_prod_fixed_of_orderOf_lt ϕ x hϕ]
  have hxD : x ∈ (P : Subgroup G) ⊓ Subgroup.centralizer {x} :=
    ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hDp : IsPGroup p ((P : Subgroup G) ⊓ Subgroup.centralizer {x} : Subgroup G) :=
    P.isPGroup'.to_inf_left
  have ha : ϕ ⟨x, hx⟩ ^ p = 1 := by
    rw [← map_pow]
    have : (⟨x, hx⟩ : (P : Subgroup G)) ^ p = 1 := Subtype.ext (by simp [hxp])
    rw [this, map_one]
  have key : ∏ X : G ⧸ (P : Subgroup G),
      ((if x • X = X then cosetValue ϕ x X else 1) * (ϕ ⟨x, hx⟩)⁻¹) = 1 := by
    refine prod_eq_one_of_isPGroup hDp _ ?_ ?_ ?_
    ·
      intro d X
      induction X using QuotientGroup.induction_on with
      | H t =>
      have hdx : (d : G) * x = x * (d : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp d.2).2
      have hconj : ((d : G) * t)⁻¹ * x * ((d : G) * t) = t⁻¹ * x * t := by
        have h : (d : G)⁻¹ * x * (d : G) = x := by rw [mul_assoc, ← hdx, inv_mul_cancel_left]
        calc ((d : G) * t)⁻¹ * x * ((d : G) * t) = t⁻¹ * ((d : G)⁻¹ * x * (d : G)) * t := by
              group
          _ = t⁻¹ * x * t := by rw [h]
      rw [Subgroup.smul_def, MulAction.Quotient.smul_mk, smul_eq_mul]
      congr 1
      by_cases ht : t⁻¹ * x * t ∈ (P : Subgroup G)
      · have ht' : ((d : G) * t)⁻¹ * x * ((d : G) * t) ∈ (P : Subgroup G) := by rwa [hconj]
        rw [ite_eq_left (smul_coe_eq_iff.mpr ht'), ite_eq_left (smul_coe_eq_iff.mpr ht),
          cosetValue_coe ϕ ht', cosetValue_coe ϕ ht]
        exact congrArg ϕ (Subtype.ext hconj)
      · have ht' : ((d : G) * t)⁻¹ * x * ((d : G) * t) ∉ (P : Subgroup G) := by rwa [hconj]
        rw [ite_eq_right (mt smul_coe_eq_iff.mp ht'), ite_eq_right (mt smul_coe_eq_iff.mp ht)]
    ·
      intro X
      have hw : (if x • X = X then cosetValue ϕ x X else 1) ^ p = 1 := by
        induction X using QuotientGroup.induction_on with
        | H t =>
        split_ifs with hX
        · have ht := smul_coe_eq_iff.mp hX
          rw [cosetValue_coe ϕ ht, ← map_pow]
          have hpow : (t⁻¹ * x * t) ^ p = 1 := by
            rw [← orderOf_dvd_iff_pow_eq_one, CFSG.RankThree.Transfer.orderOf_conj]
            exact orderOf_dvd_of_pow_eq_one hxp
          have : (⟨t⁻¹ * x * t, ht⟩ : (P : Subgroup G)) ^ p = 1 := Subtype.ext (by simp [hpow])
          rw [this, map_one]
        · exact one_pow p
      rw [mul_pow, hw, inv_pow, ha, inv_one, one_mul]
    ·
      intro X hX
      induction X using QuotientGroup.induction_on with
      | H t =>
      have hD : ∀ y ∈ (P : Subgroup G) ⊓ Subgroup.centralizer {x},
          t⁻¹ * y * t ∈ (P : Subgroup G) := by
        intro y hy
        have h := hX ⟨y, hy⟩
        rw [Subgroup.smul_def] at h
        exact smul_coe_eq_iff.mp h
      have ht : t⁻¹ * x * t ∈ (P : Subgroup G) := hD x hxD
      rw [ite_eq_left (smul_coe_eq_iff.mpr ht), cosetValue_coe ϕ ht, hfus t hD ht, mul_inv_cancel]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, mul_eq_one_iff_eq_inv,
    inv_pow, inv_inv] at key
  rw [key, Subgroup.index_eq_card, Nat.card_eq_fintype_card]

theorem commutator_ne_top_of_extremal {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {N : Subgroup G}
    (habel : ∀ y ∈ (P : Subgroup G), ∀ z ∈ (P : Subgroup G), y * z * y⁻¹ * z⁻¹ ∈ N)
    {x : G} (hx : x ∈ (P : Subgroup G)) (hxN : x ∉ N) (hxp : x ^ p = 1)
    (hfus : ∀ g : G,
      (∀ y ∈ (P : Subgroup G) ⊓ Subgroup.centralizer {x}, g⁻¹ * y * g ∈ (P : Subgroup G)) →
        x⁻¹ * (g⁻¹ * x * g) ∈ N) :
    commutator G ≠ ⊤ := by
  set U : Subgroup (P : Subgroup G) := N.subgroupOf P with hU
  have hUn : U.Normal := ⟨fun u hu y => by
    rw [hU, Subgroup.mem_subgroupOf] at hu ⊢
    have h := N.mul_mem (habel y y.2 u u.2) hu
    rwa [inv_mul_cancel_right] at h⟩
  have hcomm : ∀ a b : (P : Subgroup G) ⧸ U, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H y =>
    induction b using QuotientGroup.induction_on with
    | H z =>
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    refine Subgroup.mem_subgroupOf.mpr ?_
    have := habel (z : G)⁻¹ (Subgroup.inv_mem _ z.2) (y : G)⁻¹ (Subgroup.inv_mem _ y.2)
    simpa [mul_assoc] using this
  let : CommGroup ((P : Subgroup G) ⧸ U) :=
    { QuotientGroup.Quotient.group U with mul_comm := hcomm }
  let ϕ : (P : Subgroup G) →* (P : Subgroup G) ⧸ U := QuotientGroup.mk' U
  have hT : ϕ.transfer x = ϕ ⟨x, hx⟩ ^ (P : Subgroup G).index := by
    refine transfer_eq_pow_index_of_extremal P ϕ hx hxp fun t hD ht => ?_
    change (QuotientGroup.mk' U _ : _) = QuotientGroup.mk' U _
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, eq_comm, QuotientGroup.eq]
    exact Subgroup.mem_subgroupOf.mpr (by simpa using hfus t hD)
  have hne : ϕ ⟨x, hx⟩ ≠ 1 := fun h =>
    hxN (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h))
  have hpow : ϕ ⟨x, hx⟩ ^ p = 1 := by
    rw [← map_pow]
    have : (⟨x, hx⟩ : (P : Subgroup G)) ^ p = 1 := Subtype.ext (by simp [hxp])
    rw [this, map_one]
  intro htop
  have h1 : ϕ.transfer x = 1 := by
    have hmem : x ∈ commutator G := htop ▸ Subgroup.mem_top x
    exact MonoidHom.mem_ker.mp (Abelianization.commutator_subset_ker ϕ.transfer hmem)
  rw [hT] at h1
  have hdvd := orderOf_dvd_of_pow_eq_one h1
  rw [orderOf_eq_prime hpow hne] at hdvd
  exact P.not_dvd_index hdvd

end CFSG.RankThree.PartTwo.Sec8
