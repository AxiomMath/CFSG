module

public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422S

private theorem not_three_dvd_card_filter {α : Type} [Fintype α] (f : α → ℕ)
    (hf : ∀ a, f a = 1 ∨ f a = 3) (hsum : ¬ 3 ∣ ∑ a, f a) :
    ¬ 3 ∣ (Finset.univ.filter fun a => f a = 1).card := by
  have h1' : ∀ a ∈ Finset.univ.filter (fun a => f a = 1), f a = 1 :=
    fun a ha => (Finset.mem_filter.mp ha).2
  have h2' : ∀ a ∈ Finset.univ.filter (fun a => ¬ f a = 1), f a = 3 :=
    fun a ha => (hf a).resolve_left (Finset.mem_filter.mp ha).2
  have h1 := Finset.sum_const_nat h1'
  have h2 := Finset.sum_const_nat h2'
  have h3 : ∑ a ∈ Finset.univ.filter (fun a => f a = 1), f a
      + ∑ a ∈ Finset.univ.filter (fun a => ¬ f a = 1), f a = ∑ a, f a :=
    Finset.sum_filter_add_sum_filter_not Finset.univ (fun a => f a = 1) f
  omega

private theorem transfer_ne_one_of_fixed {G : Type} [Group G] [Finite G] {P : Subgroup G}
    {A : Type} [CommGroup A] (ϕ : P →* A) {c : G} (hcP : c ∈ P) (hc3 : c ^ 3 = 1)
    (hϕ : ∀ (g : G) (h : g⁻¹ * c * g ∈ P), ϕ ⟨g⁻¹ * c * g, h⟩ = ϕ ⟨c, hcP⟩)
    (hPsyl : ¬ 3 ∣ P.index) (hx3 : ϕ ⟨c, hcP⟩ ^ 3 = 1) (hx1 : ϕ ⟨c, hcP⟩ ≠ 1) :
    MonoidHom.transfer ϕ c ≠ 1 := by
  haveI : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers c) (G ⧸ P))) :=
    Fintype.ofFinite _
  have hn : ∀ q : G ⧸ P, Function.minimalPeriod (c • ·) q = 1 ∨
      Function.minimalPeriod (c • ·) q = 3 := fun q =>
    (Nat.dvd_prime Nat.prime_three).mp
      (MulAction.pow_smul_eq_iff_minimalPeriod_dvd.mp (by rw [hc3, one_smul]))
  have hfac : ∀ q : Quotient (MulAction.orbitRel (Subgroup.zpowers c) (G ⧸ P)),
      ϕ ⟨q.out.out⁻¹ * c ^ Function.minimalPeriod (c • ·) q.out * q.out.out,
          QuotientGroup.out_conj_pow_minimalPeriod_mem P c q.out⟩ =
        if Function.minimalPeriod (c • ·) q.out = 1 then ϕ ⟨c, hcP⟩ else 1 := by
    intro q
    rcases hn q.out with h1 | h3
    · have hmem : q.out.out⁻¹ * c * q.out.out ∈ P := by
        have := QuotientGroup.out_conj_pow_minimalPeriod_mem P c q.out
        rwa [h1, pow_one] at this
      have e : (⟨q.out.out⁻¹ * c ^ Function.minimalPeriod (c • ·) q.out * q.out.out,
          QuotientGroup.out_conj_pow_minimalPeriod_mem P c q.out⟩ : P) =
          ⟨q.out.out⁻¹ * c * q.out.out, hmem⟩ :=
        Subtype.ext (by simp [h1])
      rw [e, if_pos h1]
      exact hϕ _ hmem
    · have e : (⟨q.out.out⁻¹ * c ^ Function.minimalPeriod (c • ·) q.out * q.out.out,
          QuotientGroup.out_conj_pow_minimalPeriod_mem P c q.out⟩ : P) = 1 :=
        Subtype.ext (by simp [h3, hc3])
      rw [e, map_one]
      simp [h3]
  have hsum : ¬ 3 ∣ ∑ q : Quotient (MulAction.orbitRel (Subgroup.zpowers c) (G ⧸ P)),
      Function.minimalPeriod (c • ·) q.out := by
    rw [← Subgroup.index_eq_sum_minimalPeriod P c]
    exact hPsyl
  have hk3 := not_three_dvd_card_filter
    (fun q : Quotient (MulAction.orbitRel (Subgroup.zpowers c) (G ⧸ P)) =>
      Function.minimalPeriod (c • ·) q.out)
    (fun q => hn q.out) hsum
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot ϕ c,
    Finset.prod_congr rfl (fun q _ => hfac q), Finset.prod_ite, Finset.prod_const_one, mul_one,
    Finset.prod_const]
  intro h
  apply hk3
  have hord := orderOf_dvd_of_pow_eq_one h
  rwa [orderOf_eq_prime hx3 hx1] at hord

theorem false_of_conj_mem_coset {G : Type} [Group G] [Finite G] (hG : IsSimpleGroup G)
    (hnc : ∃ a b : G, a * b ≠ b * a) {P N : Subgroup G}
    (hPsyl : ¬ 3 ∣ P.index) (hNP : N ≤ P) (hNn : (N.subgroupOf P).Normal)
    (hidx : Nat.card P = 3 * Nat.card N) {c : G} (hcP : c ∈ P) (hcN : c ∉ N)
    (hc3 : c ^ 3 = 1)
    (hconj : ∀ g : G, g⁻¹ * c * g ∈ P → c⁻¹ * (g⁻¹ * c * g) ∈ N) : False := by
  haveI := hNn
  have hQ : Nat.card (↥P ⧸ N.subgroupOf P) = 3 := by
    rw [← Subgroup.index_eq_card]
    have h1 := Subgroup.card_mul_index (N.subgroupOf P)
    have h2 : Nat.card (N.subgroupOf P) = Nat.card N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNP).toEquiv
    rw [h2, hidx] at h1
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥N))
    rw [h1, mul_comm]
  haveI : IsCyclic (↥P ⧸ N.subgroupOf P) := isCyclic_of_prime_card hQ
  letI : CommGroup (↥P ⧸ N.subgroupOf P) := IsCyclic.commGroup
  obtain ⟨ϕ, hϕdef⟩ : ∃ ϕ : P →* (↥P ⧸ N.subgroupOf P),
      ∀ x : P, ϕ x = (x : ↥P ⧸ N.subgroupOf P) :=
    ⟨QuotientGroup.mk' (N.subgroupOf P), fun _ => rfl⟩
  have hϕ : ∀ (g : G) (h : g⁻¹ * c * g ∈ P), ϕ ⟨g⁻¹ * c * g, h⟩ = ϕ ⟨c, hcP⟩ := by
    intro g h
    rw [hϕdef, hϕdef, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have e : (g⁻¹ * c * g)⁻¹ * c = (c⁻¹ * (g⁻¹ * c * g))⁻¹ := by group
    show (g⁻¹ * c * g)⁻¹ * c ∈ N
    rw [e]
    exact N.inv_mem (hconj g h)
  have hx3 : ϕ ⟨c, hcP⟩ ^ 3 = 1 := by
    rw [← map_pow ϕ]
    have h3 : (⟨c, hcP⟩ : P) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [h3, map_one]
  have hx1 : ϕ ⟨c, hcP⟩ ≠ 1 := by
    intro h
    rw [hϕdef] at h
    exact hcN (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h))
  have hτ := transfer_ne_one_of_fixed ϕ hcP hc3 hϕ hPsyl hx3 hx1
  have hker : (MonoidHom.transfer ϕ).ker = ⊥ := by
    rcases hG.eq_bot_or_eq_top_of_normal (MonoidHom.transfer ϕ).ker with h | h
    · exact h
    · have hc : c ∈ (MonoidHom.transfer ϕ).ker := by
        rw [h]
        exact Subgroup.mem_top c
      exact absurd (MonoidHom.mem_ker.mp hc) hτ
  have hinj := (MonoidHom.ker_eq_bot_iff _).mp hker
  obtain ⟨a, b, hab⟩ := hnc
  apply hab
  apply hinj
  rw [map_mul, map_mul]
  exact mul_comm _ _

end CFSG.RankThree.PartTwo.Sec14.Ronan1422S
