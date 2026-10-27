module

public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzG11G94

section Burnside

variable {G : Type*} [Group G] [Finite G]

theorem isSolvable_of_prime_divisors {p q : ℕ}
    (h : ∀ r : ℕ, r.Prime → r ∣ Nat.card G → r = p ∨ r = q) : Group.IsSolvable G := by
  classical
  refine CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
  have hsub : (Nat.card G).primeFactors ⊆ {p, q} := by
    intro r hr
    obtain ⟨hrp, hrd, -⟩ := Nat.mem_primeFactors.1 hr
    simpa using h r hrp hrd
  exact (Finset.card_le_card hsub).trans Finset.card_le_two

theorem isSolvable_of_card_eq_pow_mul_pow {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : Nat.card G = p ^ a * q ^ b) : Group.IsSolvable G := by
  refine isSolvable_of_prime_divisors (p := p) (q := q) fun r hr hrd => ?_
  rw [h] at hrd
  rcases (Nat.Prime.dvd_mul hr).1 hrd with h1 | h1
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr hp).1 (hr.dvd_of_dvd_pow h1))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr hq).1 (hr.dvd_of_dvd_pow h1))

theorem isSolvable_of_card_dvd_two_pow_mul_three_pow {a b : ℕ}
    (h : Nat.card G ∣ 2 ^ a * 3 ^ b) : Group.IsSolvable G := by
  refine isSolvable_of_prime_divisors (p := 2) (q := 3) fun r hr hrd => ?_
  rcases (Nat.Prime.dvd_mul hr).1 (hrd.trans h) with h1 | h1
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h1))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 (hr.dvd_of_dvd_pow h1))

theorem isSolvable_of_squarefree_card (h : Squarefree (Nat.card G)) : Group.IsSolvable G := by
  have : IsZGroup G := IsZGroup.of_squarefree h
  infer_instance

end Burnside

theorem prime_seven : Nat.Prime 7 := by norm_num

theorem squarefree_thirty : Squarefree (30 : ℕ) := by
  rw [Nat.squarefree_iff_nodup_primeFactorsList (by norm_num)]
  norm_num

theorem squarefree_forty_two : Squarefree (42 : ℕ) := by
  rw [Nat.squarefree_iff_nodup_primeFactorsList (by norm_num)]
  norm_num

theorem dvd_6720_cases : ∀ d < 61, d ∣ 6720 → d = 60 ∨ d = 30 ∨ d = 42 ∨ ∃ a < 7, ∃ b < 2,
    d = 2 ^ a * 3 ^ b ∨ d = 2 ^ a * 5 ^ b ∨ d = 2 ^ a * 7 ^ b ∨ d = 3 ^ a * 5 ^ b ∨
      d = 3 ^ a * 7 ^ b ∨ d = 5 ^ a * 7 ^ b := by
  decide +kernel

variable {H : Type*} [Group H] [Finite H]

theorem eq_sixty_of_not_isSolvable (hH : ¬ Group.IsSolvable H) (hle : Nat.card H ≤ 60)
    (hd : Nat.card H ∣ 6720) : Nat.card H = 60 := by
  rcases dvd_6720_cases _ (by omega) hd with h | h | h | ⟨a, -, b, -, h | h | h | h | h | h⟩
  · exact h
  · exact absurd (isSolvable_of_squarefree_card (by rw [h]; exact squarefree_thirty)) hH
  · exact absurd (isSolvable_of_squarefree_card (by rw [h]; exact squarefree_forty_two)) hH
  · exact absurd (isSolvable_of_card_eq_pow_mul_pow Nat.prime_two Nat.prime_three h) hH
  · exact absurd (isSolvable_of_card_eq_pow_mul_pow Nat.prime_two Nat.prime_five h) hH
  · exact absurd (isSolvable_of_card_eq_pow_mul_pow Nat.prime_two prime_seven h) hH
  · exact absurd (isSolvable_of_card_eq_pow_mul_pow Nat.prime_three Nat.prime_five h) hH
  · exact absurd (isSolvable_of_card_eq_pow_mul_pow Nat.prime_three prime_seven h) hH
  · exact absurd (isSolvable_of_card_eq_pow_mul_pow Nat.prime_five prime_seven h) hH

theorem card_eq_180_of_nonsolvable (Z : Subgroup H) (hZ : Nat.card Z = 3)
    (hZc : ∀ z ∈ Z, ∀ h : H, z * h = h * z) (hH : ¬ Group.IsSolvable H)
    (hle : Nat.card H ≤ 180) (hd : Nat.card H ∣ 20160) : Nat.card H = 180 := by
  have hZn : Z.Normal := ⟨fun z hz h => by
    rw [show h * z * h⁻¹ = z by rw [← hZc z hz h]; group]; exact hz⟩
  have hZs : Group.IsSolvable Z := Group.isSolvable_of_comm fun a b => Subtype.ext (hZc a.1 a.2 b.1)
  have hQ : ¬ Group.IsSolvable (H ⧸ Z) := by
    intro hQ
    exact hH (Group.isSolvable_of_ker_le_range Z.subtype (QuotientGroup.mk' Z)
      (by rw [QuotientGroup.ker_mk']; simp))
  have hcard : Nat.card H = Nat.card Z * Nat.card (H ⧸ Z) := by
    rw [mul_comm, ← Subgroup.index_eq_card, Subgroup.index_mul_card]
  rw [hZ] at hcard
  have h60 : Nat.card (H ⧸ Z) = 60 := by
    refine eq_sixty_of_not_isSolvable hQ (by omega) ?_
    have h3 : 3 * Nat.card (H ⧸ Z) ∣ 3 * 6720 := by
      rw [← hcard]; simpa using hd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h3
  rw [hcard, h60]

section Normalizer

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem mem_zpowers_cases_of_orderOf_three {w x : G} (hord : orderOf w = 3)
    (hx : x ∈ Subgroup.zpowers w) : x = 1 ∨ x = w ∨ x = w⁻¹ := by
  have hw3 : w ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one w
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have hk : w ^ k = w ^ (k % 3) := by
    have := zpow_mod_orderOf w k
    rw [hord] at this
    exact_mod_cast this.symm
  rw [hk]
  have h3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases h3 with h | h | h
  · left
    rw [h]
    simp
  · right
    left
    rw [h]
    simp
  · right
    right
    rw [h, zpow_two]
    exact (inv_eq_of_mul_eq_one_right ((pow_three w).symm.trans hw3)).symm

theorem eq_normalizer_zpowers_of_nonsolvable (hG : Nat.card G = 20160) {Γ : Subgroup G}
    {w a : G} (hord : orderOf w = 3) (hwΓ : w ∈ Γ) (haΓ : a ∈ Γ)
    (hnorm : ∀ γ ∈ Γ, γ * w * γ⁻¹ ∈ Subgroup.zpowers w) (haw : a * w * a⁻¹ = w⁻¹)
    (hns : ¬ Group.IsSolvable ↥Γ) (hcen : Nat.card (Subgroup.centralizer ({w} : Set G)) ≤ 180) :
    180 ∣ Nat.card ↥Γ ∧ Γ = Subgroup.normalizer (Subgroup.zpowers w : Set G) := by
  classical
  have hw3 : w ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one w
  have hw1 : w ≠ 1 := fun h => by rw [h, orderOf_one] at hord; omega
  set Cen : Subgroup G := Subgroup.centralizer ({w} : Set G) with hCen
  have hmemCen : ∀ x, x ∈ Cen ↔ x * w = w * x := fun x => Subgroup.mem_centralizer_singleton_iff
  have hdich : ∀ γ ∈ Γ, γ ∈ Cen ∨ γ * w * γ⁻¹ = w⁻¹ := by
    intro γ hγ
    rcases mem_zpowers_cases_of_orderOf_three hord (hnorm γ hγ) with h | h | h
    · exfalso
      apply hw1
      have : w = γ⁻¹ * (γ * w * γ⁻¹) * γ := by group
      rw [this, h]
      group
    · left
      rw [hmemCen]
      exact mul_inv_eq_iff_eq_mul.1 h
    · right
      exact h
  have hinvCen : ∀ x, x * w * x⁻¹ = w⁻¹ → a⁻¹ * x ∈ Cen := by
    intro x hx
    rw [hmemCen]
    have h1 : a⁻¹ * x * w * (a⁻¹ * x)⁻¹ = w := by
      calc a⁻¹ * x * w * (a⁻¹ * x)⁻¹ = a⁻¹ * (x * w * x⁻¹) * a := by group
        _ = a⁻¹ * w⁻¹ * a := by rw [hx]
        _ = a⁻¹ * (a * w * a⁻¹) * a := by rw [haw]
        _ = w := by group
    exact mul_inv_eq_iff_eq_mul.1 h1
  set Γ₀ : Subgroup ↥Γ := Cen.subgroupOf Γ with hΓ₀
  have hmemΓ₀ : ∀ γ : ↥Γ, γ ∈ Γ₀ ↔ (γ : G) ∈ Cen := fun γ => Iff.rfl
  have hΓ₀n : Γ₀.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hmemΓ₀] at hn ⊢
    have hnw : (n : G) * w = w * (n : G) := (hmemCen _).1 hn
    rcases hdich g g.2 with hg | hg
    · exact Cen.mul_mem (Cen.mul_mem hg hn) (Cen.inv_mem hg)
    · rw [hmemCen]
      have hgi : (g : G)⁻¹ * w * (g : G) = w⁻¹ := by
        have : (g : G)⁻¹ * w⁻¹ * (g : G) = w := by
          calc (g : G)⁻¹ * w⁻¹ * (g : G) = (g : G)⁻¹ * ((g : G) * w * (g : G)⁻¹) * (g : G) := by
                rw [hg]
            _ = w := by group
        calc (g : G)⁻¹ * w * (g : G) = ((g : G)⁻¹ * w⁻¹ * (g : G))⁻¹ := by group
          _ = w⁻¹ := by rw [this]
      have hgw : (g : G) * w⁻¹ * (g : G)⁻¹ = w := by
        have : ((g : G) * w * (g : G)⁻¹)⁻¹ = w := by rw [hg, inv_inv]
        simpa [mul_assoc] using this
      have hnwi : (n : G) * w⁻¹ = w⁻¹ * (n : G) := (Commute.inv_right hnw).eq
      calc (g : G) * (n : G) * (g : G)⁻¹ * w
          = (g : G) * (n : G) * ((g : G)⁻¹ * w * (g : G)) * (g : G)⁻¹ := by group
        _ = (g : G) * ((n : G) * w⁻¹) * (g : G)⁻¹ := by rw [hgi]; group
        _ = (g : G) * (w⁻¹ * (n : G)) * (g : G)⁻¹ := by rw [hnwi]
        _ = ((g : G) * w⁻¹ * (g : G)⁻¹) * ((g : G) * (n : G) * (g : G)⁻¹) := by group
        _ = w * ((g : G) * (n : G) * (g : G)⁻¹) := by rw [hgw]
  have hquot : ∀ q : ↥Γ ⧸ Γ₀, q = 1 ∨ q = QuotientGroup.mk ⟨a, haΓ⟩ := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H γ =>
      rcases hdich γ γ.2 with hγ | hγ
      · exact Or.inl ((QuotientGroup.eq_one_iff γ).2 hγ)
      · right
        have h1 : (γ : G)⁻¹ * a ∈ Cen := by
          have := Cen.inv_mem (hinvCen _ hγ)
          simpa using this
        rw [QuotientGroup.eq]
        exact h1
  have hqsolv : Group.IsSolvable (↥Γ ⧸ Γ₀) := by
    refine Group.isSolvable_of_comm fun x y => ?_
    rcases hquot x with rfl | rfl <;> rcases hquot y with rfl | rfl <;> simp
  have hΓ₀ns : ¬ Group.IsSolvable ↥Γ₀ := by
    intro h
    exact hns (Group.isSolvable_of_ker_le_range Γ₀.subtype (QuotientGroup.mk' Γ₀)
      (by rw [QuotientGroup.ker_mk']; simp))
  have hwΓ₀ : (⟨w, hwΓ⟩ : ↥Γ) ∈ Γ₀ := (hmemCen w).2 rfl
  let w₀ : ↥Γ₀ := ⟨⟨w, hwΓ⟩, hwΓ₀⟩
  have hw₀ord : orderOf w₀ = 3 := by
    have h1 : orderOf w₀ = orderOf (w₀ : ↥Γ) := (Subgroup.orderOf_coe w₀).symm
    have h2 : orderOf (w₀ : ↥Γ) = orderOf ((w₀ : ↥Γ) : G) := (Subgroup.orderOf_coe _).symm
    rw [h1, h2]
    exact hord
  have hcentral : ∀ z ∈ Subgroup.zpowers w₀, ∀ h : ↥Γ₀, z * h = h * z := by
    intro z hz h
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    have hc : Commute h w₀ := Subtype.ext (Subtype.ext ((hmemCen _).1 h.2))
    exact ((hc.zpow_right k).eq).symm
  have hinj : Function.Injective (fun h : ↥Γ₀ => (⟨((h : ↥Γ) : G), h.2⟩ : Cen)) := by
    intro h h' hh
    have h1 : ((h : ↥Γ) : G) = ((h' : ↥Γ) : G) := congrArg (fun x : Cen => (x : G)) hh
    exact Subtype.ext (Subtype.ext h1)
  have hle : Nat.card ↥Γ₀ ≤ 180 := (Nat.card_le_card_of_injective _ hinj).trans hcen
  have hdvd : Nat.card ↥Γ₀ ∣ 20160 := by
    have hinj' : Function.Injective (Γ.subtype.comp Γ₀.subtype) :=
      Γ.subtype_injective.comp Γ₀.subtype_injective
    rw [← hG]
    exact Subgroup.card_dvd_of_injective _ hinj'
  have h180 : Nat.card ↥Γ₀ = 180 := by
    refine card_eq_180_of_nonsolvable (Subgroup.zpowers w₀) ?_ hcentral hΓ₀ns hle hdvd
    rw [Nat.card_zpowers, hw₀ord]
  have hCenΓ : ∀ x ∈ Cen, x ∈ Γ := by
    have hbij := hinj.bijective_of_nat_card_le (by rw [h180]; exact hcen)
    intro x hx
    obtain ⟨h, hh⟩ := hbij.2 ⟨x, hx⟩
    have h1 : ((h : ↥Γ) : G) = x := congrArg (fun y : Cen => (y : G)) hh
    rw [← h1]
    exact (h : ↥Γ).2
  have hconj : ∀ γ ∈ Γ, ∀ h ∈ Subgroup.zpowers w, γ * h * γ⁻¹ ∈ Subgroup.zpowers w := by
    intro γ hγ h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    have := map_zpow (MulAut.conj γ) w k
    simp only [MulAut.conj_apply] at this
    rw [this]
    exact (Subgroup.zpowers w).zpow_mem (hnorm γ hγ) k
  refine ⟨?_, ?_⟩
  · have h1 : Nat.card ↥Γ₀ ∣ Nat.card ↥Γ := Subgroup.card_subgroup_dvd_card Γ₀
    rwa [h180] at h1
  · apply le_antisymm
    · intro γ hγ
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · exact hconj γ hγ h
      · intro hh
        have := hconj γ⁻¹ (Γ.inv_mem hγ) _ hh
        have e : γ⁻¹ * (γ * h * γ⁻¹) * γ⁻¹⁻¹ = h := by group
        rwa [e] at this
    · intro x hx
      rw [Subgroup.mem_normalizer_iff] at hx
      have hxz : x * w * x⁻¹ ∈ Subgroup.zpowers w :=
        (hx w).1 (Subgroup.mem_zpowers w)
      rcases mem_zpowers_cases_of_orderOf_three hord hxz with h | h | h
      · exfalso
        apply hw1
        have : w = x⁻¹ * (x * w * x⁻¹) * x := by group
        rw [this, h]
        group
      · exact hCenΓ x ((hmemCen x).2 (mul_inv_eq_iff_eq_mul.1 h))
      · have : x = a * (a⁻¹ * x) := by group
        rw [this]
        exact Γ.mul_mem haΓ (hCenΓ _ (hinvCen x h))

end Normalizer

end CFSG.Quasithin.SzG11G94
