module

public import CFSG.Timmesfeld.Bridge.Asc72Defs
public import CFSG.Timmesfeld.Bridge.InvolutionSet

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge

variable {G : Type*} [Group G] {D : Set G}

namespace IsOddTransp

variable (hD : IsOddTransp D) {u v w : G}
include hD

theorem orderOf_eq_two (hu : u ∈ D) : orderOf u = 2 := hD.1 u hu

theorem mul_self_eq_one (hu : u ∈ D) : u * u = 1 := by
  rw [← pow_two, ← hD.orderOf_eq_two hu, pow_orderOf_eq_one]

theorem inv_eq (hu : u ∈ D) : u⁻¹ = u := inv_eq_of_mul_eq_one_right (hD.mul_self_eq_one hu)

theorem ne_one (hu : u ∈ D) : u ≠ 1 := by
  rintro rfl
  have h := hD.orderOf_eq_two hu
  rw [orderOf_one] at h
  exact absurd h (by decide)

theorem isInvolutionSet : IsInvolutionSet D := hD.1

theorem eq_of_mul_eq_one (hu : u ∈ D) (h : u * v = 1) : u = v := by
  rw [← hD.inv_eq hu]
  exact (eq_inv_of_mul_eq_one_right h).symm

theorem commute_or_odd (hu : u ∈ D) (hv : v ∈ D) : Commute u v ∨ Odd (orderOf (u * v)) := by
  rcases hD.2 u hu v hv with h | h
  · left
    rw [commute_iff_mul_sq_eq_one (hD.mul_self_eq_one hu) (hD.mul_self_eq_one hv)]
    exact orderOf_dvd_iff_pow_eq_one.mp h
  · exact Or.inr h

theorem odd_of_not_commute (hu : u ∈ D) (hv : v ∈ D) (h : ¬ Commute u v) :
    Odd (orderOf (u * v)) :=
  (hD.commute_or_odd hu hv).resolve_left h

theorem orderOf_mul_eq_two (hu : u ∈ D) (hv : v ∈ D) (hne : u ≠ v) (hc : Commute u v) :
    orderOf (u * v) = 2 := by
  apply orderOf_eq_prime
  · rw [← commute_iff_mul_sq_eq_one (hD.mul_self_eq_one hu) (hD.mul_self_eq_one hv)]
    exact hc
  · exact fun h => hne (hD.eq_of_mul_eq_one hu h)

theorem exists_conj (hu : u ∈ D) (hv : v ∈ D) (h : ¬ Commute u v) :
    ∃ g ∈ Subgroup.closure ({u, v} : Set G), g * u * g⁻¹ = v :=
  exists_conj_of_odd_orderOf_mul (hD.mul_self_eq_one hu) (hD.mul_self_eq_one hv)
    (hD.odd_of_not_commute hu hv h)

theorem commute_of_isPGroup {P : Subgroup G} (hP : IsPGroup 2 P) (hu : u ∈ D) (hv : v ∈ D)
    (huP : u ∈ P) (hvP : v ∈ P) : Commute u v := by
  rcases hD.commute_or_odd hu hv with h | h
  · exact h
  · obtain ⟨k, hk⟩ := hP ⟨u * v, P.mul_mem huP hvP⟩
    have hk' : (u * v) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hdvd : orderOf (u * v) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have h1 : orderOf (u * v) = 1 := by
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      rcases i with _ | i
      · simpa using hi
      · rw [hi, pow_succ] at h
        exact absurd h (by simp [Nat.not_odd_iff_even])
    rw [orderOf_eq_one_iff] at h1
    rw [← hD.eq_of_mul_eq_one hu h1]

theorem oddAcross : OddAcross D := fun _ hx _ hy h =>
  hD.odd_of_not_commute hx hy fun hc => h (reach_of_commute hx hy hc)

theorem commute_mul_iff (hu : u ∈ D) (hv : v ∈ D) (hw : w ∈ D) (hne : u ≠ v)
    (hc : Commute u v) : Commute w (u * v) ↔ Commute w u ∧ Commute w v := by
  constructor
  · intro h
    have hwu : Commute w u := by
      by_contra hwu
      have hodd := hD.odd_of_not_commute hu hw (fun h' => hwu h'.symm)
      have hn1 : orderOf (u * w) ≠ 1 := by
        intro h1
        rw [orderOf_eq_one_iff] at h1
        exact hwu (hD.eq_of_mul_eq_one hu h1 ▸ Commute.refl u)
      have hxy : Commute (u * v) (u * w) := by
        have h1 : Commute (u * v) u := (Commute.mul_left (Commute.refl u) hc.symm)
        exact h1.mul_right h.symm
      have h2 : orderOf (u * v) = 2 := hD.orderOf_mul_eq_two hu hv hne hc
      have hcop : Nat.Coprime (orderOf (u * v)) (orderOf (u * w)) := by
        rw [h2, Nat.coprime_two_left]
        exact hodd
      have hvw : v * w = u * v * (u * w) := by
        calc v * w = u * u * v * w := by rw [hD.mul_self_eq_one hu, one_mul]
          _ = u * (u * v) * w := by rw [mul_assoc u u v]
          _ = u * (v * u) * w := by rw [hc.eq]
          _ = u * v * (u * w) := by group
      have hord : orderOf (v * w) = 2 * orderOf (u * w) := by
        rw [hvw, hxy.orderOf_mul_eq_mul_orderOf_of_coprime hcop, h2]
      rcases hD.2 v hv w hw with h3 | h3
      · rw [hord] at h3
        have := Nat.le_of_dvd (by norm_num) h3
        have hpos := hodd.pos
        omega
      · rw [hord] at h3
        exact (Nat.not_odd_iff_even.mpr (even_two_mul _)) h3
    refine ⟨hwu, ?_⟩
    have := hwu.inv_right.mul_right h
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
  · rintro ⟨h1, h2⟩
    exact h1.mul_right h2

theorem mono {E : Set G} (hE : E ⊆ D) : IsOddTransp E :=
  ⟨fun d hd => hD.1 d (hE hd), fun d hd e he => hD.2 d (hE hd) e (hE he)⟩

omit hD in
theorem image {K : Type*} [Group K] (hD : IsOddTransp D) (φ : G →* K) (hφ : ∀ d ∈ D, φ d ≠ 1) :
    IsOddTransp (φ '' D) := by
  refine ⟨fun _ ⟨x, hx, hxe⟩ => hxe ▸ ?_, ?_⟩
  · exact orderOf_eq_prime (by rw [← map_pow, pow_two, hD.mul_self_eq_one hx, map_one]) (hφ x hx)
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul]
    have hdvd : orderOf (φ (x * y)) ∣ orderOf (x * y) := orderOf_map_dvd φ (x * y)
    rcases hD.2 x hx y hy with h | h
    · exact Or.inl (hdvd.trans h)
    · exact Or.inr (Odd.of_dvd_nat h hdvd)

omit hD in
theorem preimage (hD : IsOddTransp D) (K : Subgroup G) :
    IsOddTransp (((↑) : K → G) ⁻¹' D) := by
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · rw [← Subgroup.orderOf_coe]
    exact hD.1 _ hx
  · rw [← Subgroup.orderOf_coe, Subgroup.coe_mul]
    exact hD.2 _ hx _ hy

end IsOddTransp

structure Setup (G : Type*) [Group G] (D : Set G) : Prop where
  isClass : ∃ d₀ : G, D = {g | IsConj d₀ g}
  oddT : IsOddTransp D
  gen : Subgroup.closure D = ⊤

namespace Setup

variable (hS : Setup G D)
include hS

theorem normal : IsNormalSet D := fun g _ hx => conj_mem_of_isClass hS.isClass g hx

theorem nonempty : D.Nonempty := by
  obtain ⟨d₀, rfl⟩ := hS.isClass
  exact ⟨d₀, IsConj.refl d₀⟩

theorem isConj {x y : G} (hx : x ∈ D) (hy : y ∈ D) : IsConj x y :=
  isConj_of_isClass hS.isClass hx hy

theorem conj_mem (g : G) {x : G} (hx : x ∈ D) : g * x * g⁻¹ ∈ D := hS.normal g x hx

theorem eq_setOf_isConj {x : G} (hx : x ∈ D) : D = {g | IsConj x g} := by
  ext y
  exact ⟨fun hy => hS.isConj hx hy, fun hy => by
    obtain ⟨d₀, rfl⟩ := hS.isClass
    exact IsConj.trans hx hy⟩

theorem subset_or_disjoint (N : Subgroup G) [N.Normal] :
    D ⊆ N ∨ ∀ x ∈ D, x ∉ N := by
  by_cases h : ∃ x ∈ D, x ∈ N
  · obtain ⟨x, hx, hxN⟩ := h
    left
    intro y hy
    obtain ⟨c, rfl⟩ := isConj_iff.mp (hS.isConj hx hy)
    exact ‹N.Normal›.conj_mem x hxN c
  · push Not at h
    exact Or.inr h

theorem eq_top_of_subset (N : Subgroup G) (h : D ⊆ N) : N = ⊤ := by
  rw [eq_top_iff, ← hS.gen, Subgroup.closure_le]
  exact h

theorem abelianization_eq {x y : G} (hx : x ∈ D) (hy : y ∈ D) :
    Abelianization.of x = Abelianization.of y := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp (hS.isConj hx hy)
  rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]

theorem index_commutator_le_two [Finite G] : (commutator G).index ≤ 2 := by
  obtain ⟨d, hd⟩ := hS.nonempty
  set t : Abelianization G := Abelianization.of d with ht
  have htop : (⊤ : Subgroup (Abelianization G)) = Subgroup.zpowers t := by
    refine (eq_top_iff.mpr ?_).symm
    rintro x -
    obtain ⟨g, rfl⟩ : ∃ g : G, Abelianization.of g = x := QuotientGroup.mk_surjective x
    have hg : g ∈ Subgroup.closure D := hS.gen ▸ Subgroup.mem_top g
    have hle : Subgroup.closure D ≤ (Subgroup.zpowers t).comap Abelianization.of := by
      rw [Subgroup.closure_le]
      intro y hy
      show Abelianization.of y ∈ Subgroup.zpowers t
      rw [hS.abelianization_eq hy hd]
      exact Subgroup.mem_zpowers t
    exact hle hg
  have hcard : Nat.card (Abelianization G) ≤ 2 := by
    rw [← Subgroup.card_top (G := Abelianization G), htop, Nat.card_zpowers]
    have h2 : t ^ 2 = 1 := by
      rw [ht, ← map_pow, pow_two, hS.oddT.mul_self_eq_one hd, map_one]
    exact orderOf_le_of_pow_eq_one (by norm_num) h2
  rw [Subgroup.index]
  exact hcard

theorem map {K : Type*} [Group K] (φ : G →* K) (hφ : Function.Surjective φ)
    (h1 : ∀ d ∈ D, φ d ≠ 1) : Setup K (φ '' D) := by
  obtain ⟨d₀, hd₀⟩ := hS.isClass
  refine ⟨⟨φ d₀, ?_⟩, hS.oddT.image φ h1, ?_⟩
  · ext k
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hd₀] at hx
      exact φ.map_isConj (show IsConj d₀ x from hx)
    · intro hk
      obtain ⟨c, rfl⟩ := isConj_iff.mp hk
      obtain ⟨g, rfl⟩ := hφ c
      exact ⟨g * d₀ * g⁻¹, by rw [hd₀]; exact isConj_iff.mpr ⟨g, rfl⟩, by simp⟩
  · rw [← MonoidHom.map_closure, hS.gen, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
    exact hφ

end Setup

theorem disconnected_of_exists_subgroup (hS : Setup G D)
    (hH : ∃ H : Subgroup G, H ≠ ⊤ ∧ (∃ u ∈ D, u ∈ H) ∧
      ∀ u ∈ D, u ∈ H → ∀ v ∈ D, Commute u v → v ∈ H) : Disconnected D := by
  obtain ⟨H, hHtop, ⟨u, hu, huH⟩, hclosed⟩ := hH
  by_contra hcon
  apply hHtop
  rw [eq_top_iff, ← hS.gen, Subgroup.closure_le]
  intro y hy
  have hreach : Reach D u y := by
    by_contra h
    exact hcon ⟨u, hu, y, hy, h⟩
  have hS' : ∀ x ∈ {x | x ∈ D ∧ x ∈ H}, ∀ z ∈ D, Commute x z → z ∈ {x | x ∈ D ∧ x ∈ H} :=
    fun x hx z hz hxz => ⟨hz, hclosed x hx.1 hx.2 z hz hxz⟩
  exact (mem_of_reach hS' ⟨hu, huH⟩ hreach).2

theorem mem_compStab_of_reach (hS : Setup G D) {x y : G} (h : Reach D x y) :
    y ∈ compStab hS.normal x := by
  rw [mem_compStab_iff]
  have h1 : Reach D y (y * x * y⁻¹) := by
    have := reach_conj hS.normal y (reach_symm h)
    rwa [mul_inv_cancel_right] at this
  exact reach_trans h h1

theorem mem_compStab_iff_reach (hS : Setup G D) {x y : G} (hx : x ∈ D) (hy : y ∈ D) :
    y ∈ compStab hS.normal x ↔ Reach D x y :=
  ⟨reach_of_mem_compStab_of_odd hS.normal hS.oddT.isInvolutionSet hS.oddT.oddAcross hx hy,
    mem_compStab_of_reach hS⟩

theorem exists_subgroup_of_disconnected (hS : Setup G D) (hdisc : Disconnected D) :
    ∃ H : Subgroup G, H ≠ ⊤ ∧ (∃ u ∈ D, u ∈ H) ∧
      ∀ u ∈ D, u ∈ H → ∀ v ∈ D, Commute u v → v ∈ H := by
  obtain ⟨x, hx, -⟩ := id hdisc
  refine ⟨compStab hS.normal x,
    compStab_ne_top_of_odd hS.normal hS.oddT.isInvolutionSet hS.oddT.oddAcross hdisc hx,
    ⟨x, hx, mem_compStab_self hS.normal x⟩, fun u hu huH v hv huv => ?_⟩
  rw [mem_compStab_iff_reach hS hx hu] at huH
  exact mem_compStab_of_reach hS (reach_trans huH (reach_of_commute hu hv huv))

end CFSG.Timmesfeld.Bridge.Asc72
