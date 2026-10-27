module

public import CFSG.Timmesfeld.Special.Commutator

public section

namespace CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

namespace Special

theorem eq_one_of_odd_of_dvd_two_pow {n k : ℕ} (hn : Odd n) (h : n ∣ 2 ^ k) : n = 1 := by
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rfl
  · exact absurd hn (Nat.not_odd_iff_even.2 ((Nat.even_pow' hi.ne').2 even_two))

theorem eq_one_of_mem_of_isPGroup {Q : Subgroup G} (hQ : IsPGroup 2 Q) {g : G} (hg : g ∈ Q)
    (hodd : Odd (orderOf g)) : g = 1 := by
  obtain ⟨k, hk⟩ := hQ ⟨g, hg⟩
  have hk' : g ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  exact orderOf_eq_one_iff.mp (eq_one_of_odd_of_dvd_two_pow hodd (orderOf_dvd_of_pow_eq_one hk'))

theorem isPGroup_closure_pair_of_orderOf {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (h : orderOf (x * y) = 2 ∨ orderOf (x * y) = 4 ∨ orderOf (x * y) = 1) :
    IsPGroup 2 (Subgroup.closure ({x, y} : Set G)) := by
  refine isPGroup_two_closure_pair hx hy (k := 2) ?_
  have h4 : orderOf (x * y) ∣ 2 ^ 2 := by
    rcases h with h | h | h <;> rw [h] <;> norm_num
  exact orderOf_dvd_iff_pow_eq_one.mp h4

theorem mem_centralizer_singleton {x z : G} (h : Commute x z) : x ∈ Subgroup.centralizer {z} := by
  rw [Subgroup.mem_centralizer_iff]
  rintro g rfl
  exact h.symm.eq

end Special

open Special

theorem mem_map_pCore_of_mem_rootSet [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {H : Subgroup G} {x x' : G} (hx : x ∈ D)
    (hxQ : x ∈ (CFSG.pCore 2 H).map H.subtype) (hx' : x' ∈ rootSet D x) (hx'H : x' ∈ H) :
    x' ∈ (CFSG.pCore 2 H).map H.subtype := by
  obtain ⟨y, hyP, rfl⟩ := hxQ
  refine ⟨⟨x', hx'H⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, CFSG.BaerSuzuki.baer_suzuki_iff]
  intro h
  have hx'D : x' ∈ D := hx'.1
  have hcD : (h : G) * x' * (h : G)⁻¹ ∈ D := conj_mem_of_isClass hclass h hx'D
  have h1 : (⟨x', hx'H⟩ : H) * ⟨x', hx'H⟩ = 1 := Subtype.ext (hD.mul_self_eq_one hx'D)
  have h2 : (h * ⟨x', hx'H⟩ * h⁻¹) * (h * ⟨x', hx'H⟩ * h⁻¹) = 1 :=
    Subtype.ext (by simpa using hD.mul_self_eq_one hcD)
  have hord : orderOf (x' * ((h : G) * x' * (h : G)⁻¹)) =
      orderOf ((⟨x', hx'H⟩ : H) * (h * ⟨x', hx'H⟩ * h⁻¹)) := by
    rw [← Subgroup.orderOf_coe]
    simp
  rcases hD.orderOf_mul hx'D hcD with h24 | h24 | hodd
  · exact isPGroup_closure_pair_of_orderOf h1 h2 (Or.inl (hord ▸ h24))
  · exact isPGroup_closure_pair_of_orderOf h1 h2 (Or.inr (Or.inl (hord ▸ h24)))
  by_cases h1' : orderOf (x' * ((h : G) * x' * (h : G)⁻¹)) = 1
  · exact isPGroup_closure_pair_of_orderOf h1 h2 (Or.inr (Or.inr (hord ▸ h1')))
  exfalso
  have hnc : ¬ Commute x' ((h : G) * x' * (h : G)⁻¹) := by
    intro hc
    have h2' := orderOf_dvd_of_pow_eq_one ((commute_iff_mul_sq_eq_one (hD.mul_self_eq_one hx'D)
      (hD.mul_self_eq_one hcD)).1 hc)
    have hle := Nat.le_of_dvd (by norm_num) h2'
    obtain ⟨k, hk⟩ := hodd
    omega
  have hxT : (y : G) ∈ rootSet D x' := mem_rootSet_comm hx hx'
  have hxT' : (h : G) * (y : G) * (h : G)⁻¹ ∈ rootSet D ((h : G) * x' * (h : G)⁻¹) := by
    rw [rootSet_conj hclass]
    exact ⟨y, hxT, rfl⟩
  obtain ⟨hodd', hnc'⟩ := odd_orderOf_mul_of_mem_rootSet hD hx'D hcD hxT hxT' hodd hnc
  have hP := CFSG.BaerSuzuki.Helpers.pCore_isPGroup (G := H) 2
  have hmem : y * (h * y * h⁻¹) ∈ CFSG.pCore 2 H :=
    (CFSG.pCore 2 H).mul_mem hyP ((CFSG.BaerSuzuki.Helpers.pCore_normal 2).conj_mem y hyP h)
  have hQ : IsPGroup 2 ((CFSG.pCore 2 H).map H.subtype) := hP.map H.subtype
  have h1'' := eq_one_of_mem_of_isPGroup hQ ⟨_, hmem, rfl⟩ (by simpa using hodd')
  apply hnc'
  have : (y : G) * ((h : G) * (y : G) * (h : G)⁻¹) = 1 := by simpa using h1''
  have hinv := eq_inv_of_mul_eq_one_right this
  rw [hinv, hD.inv_eq (show (y : G) ∈ D from hx)]

theorem mem_map_pCore_centralizer [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {z x : G} (hz : z ∈ D) (hx : x ∈ D) (hxz : Commute x z)
    (hmul : x * z ∈ D ∨ x = z) :
    x ∈ (CFSG.pCore 2 (Subgroup.centralizer {z})).map (Subgroup.centralizer {z}).subtype := by
  set H := Subgroup.centralizer ({z} : Set G) with hH
  have hxH : x ∈ H := by
    rw [hH, Subgroup.mem_centralizer_iff]
    rintro g rfl
    exact hxz.symm.eq
  refine ⟨⟨x, hxH⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, CFSG.BaerSuzuki.baer_suzuki_iff]
  intro h
  have hhz : Commute (h : G) z := (Subgroup.mem_centralizer_iff.mp h.2 z rfl).symm
  have hcD : (h : G) * x * (h : G)⁻¹ ∈ D := conj_mem_of_isClass hclass h hx
  have h1 : (⟨x, hxH⟩ : H) * ⟨x, hxH⟩ = 1 := Subtype.ext (hD.mul_self_eq_one hx)
  have h2 : (h * ⟨x, hxH⟩ * h⁻¹) * (h * ⟨x, hxH⟩ * h⁻¹) = 1 :=
    Subtype.ext (by simpa using hD.mul_self_eq_one hcD)
  have hord : orderOf (x * ((h : G) * x * (h : G)⁻¹)) =
      orderOf ((⟨x, hxH⟩ : H) * (h * ⟨x, hxH⟩ * h⁻¹)) := by
    rw [← Subgroup.orderOf_coe]
    simp
  rcases hD.orderOf_mul hx hcD with h24 | h24 | hodd
  · exact isPGroup_closure_pair_of_orderOf h1 h2 (Or.inl (hord ▸ h24))
  · exact isPGroup_closure_pair_of_orderOf h1 h2 (Or.inr (Or.inl (hord ▸ h24)))
  by_cases h1' : orderOf (x * ((h : G) * x * (h : G)⁻¹)) = 1
  · exact isPGroup_closure_pair_of_orderOf h1 h2 (Or.inr (Or.inr (hord ▸ h1')))
  exfalso
  rcases hmul with hmul | rfl
  ·
    set u := x * ((h : G) * x * (h : G)⁻¹) with hu
    have hw : (h : G) * x * (h : G)⁻¹ * z ∈ D := by
      have : (h : G) * x * (h : G)⁻¹ * z = (h : G) * (x * z) * (h : G)⁻¹ := by
        rw [mul_assoc _ (h : G)⁻¹, hhz.inv_left.eq]
        group
      rw [this]
      exact conj_mem_of_isClass hclass h hmul
    have hcomm : Commute u z :=
      hxz.mul_left ((hhz.mul_left hxz).mul_left hhz.inv_left)
    have h2u := orderOf_mul_eq_two_mul_of_odd hcomm hodd (hD.orderOf_eq_two hz)
    have heq : x * ((h : G) * x * (h : G)⁻¹ * z) = u * z := by rw [hu, ← mul_assoc]
    have hpos : 0 < orderOf u := by
      obtain ⟨k, hk⟩ := hodd
      omega
    rcases hD.orderOf_mul hx hw with h' | h' | h' <;> rw [heq, h2u] at h'
    · omega
    · obtain ⟨k, hk⟩ := hodd
      omega
    · exact (Nat.not_odd_iff_even.2 (even_two_mul _)) h'
  · apply h1'
    rw [hhz.eq, mul_inv_cancel_right, hD.mul_self_eq_one hx, orderOf_one]

section SpecialPair

variable {d e : G}

theorem rootGroup_le_map_pCore_centralizer_left [Finite G]
    (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D) (hd : d ∈ D)
    (he : e ∈ D) (h4 : orderOf (d * e) = 4) :
    rootGroup D d ≤ (CFSG.pCore 2 (Subgroup.centralizer {(d * e) ^ 2})).map
      (Subgroup.centralizer {(d * e) ^ 2}).subtype := by
  obtain ⟨hz, hdz, -, -⟩ := sq_mem_of_orderOf_eq_four hD hd he h4
  have hdQ := mem_map_pCore_centralizer hclass hD hz hd hdz
    (Or.inl (mul_sq_mem_of_orderOf_eq_four hclass hD hd he h4))
  rw [rootGroup, Subgroup.closure_le]
  intro a ha
  exact mem_map_pCore_of_mem_rootSet hclass hD hd hdQ ha
    (mem_centralizer_singleton ((ha.2 _ hz).2 hdz))

theorem rootGroup_le_map_pCore_centralizer_right [Finite G]
    (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D) (hd : d ∈ D)
    (he : e ∈ D) (h4 : orderOf (d * e) = 4) :
    rootGroup D e ≤ (CFSG.pCore 2 (Subgroup.centralizer {(d * e) ^ 2})).map
      (Subgroup.centralizer {(d * e) ^ 2}).subtype := by
  have h4' : orderOf (e * d) = 4 := by rwa [orderOf_mul_comm_eq]
  have hsq := mul_sq_eq_mul_sq_comm (hD.mul_self_eq_one hd) (hD.mul_self_eq_one he) h4
  rw [hsq]
  exact rootGroup_le_map_pCore_centralizer_left hclass hD he hd h4'

theorem rootGroup_sq_le_map_pCore_centralizer [Finite G]
    (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D) (hd : d ∈ D)
    (he : e ∈ D) (h4 : orderOf (d * e) = 4) :
    rootGroup D ((d * e) ^ 2) ≤ (CFSG.pCore 2 (Subgroup.centralizer {(d * e) ^ 2})).map
      (Subgroup.centralizer {(d * e) ^ 2}).subtype := by
  obtain ⟨hz, -, -, -⟩ := sq_mem_of_orderOf_eq_four hD hd he h4
  have hzQ := mem_map_pCore_centralizer hclass hD hz hz (Commute.refl _) (Or.inr rfl)
  rw [rootGroup, Subgroup.closure_le]
  intro c hc
  exact mem_map_pCore_of_mem_rootSet hclass hD hz hzQ hc
    (mem_centralizer_singleton (commute_of_mem_rootSet hz hc (mem_rootSet_self hz)))

theorem sup_rootGroup_le_map_pCore_centralizer [Finite G]
    (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D) (hd : d ∈ D)
    (he : e ∈ D) (h4 : orderOf (d * e) = 4) :
    rootGroup D d ⊔ rootGroup D e ⊔ rootGroup D ((d * e) ^ 2) ≤
      (CFSG.pCore 2 (Subgroup.centralizer {(d * e) ^ 2})).map
        (Subgroup.centralizer {(d * e) ^ 2}).subtype :=
  sup_le (sup_le (rootGroup_le_map_pCore_centralizer_left hclass hD hd he h4)
    (rootGroup_le_map_pCore_centralizer_right hclass hD hd he h4))
    (rootGroup_sq_le_map_pCore_centralizer hclass hD hd he h4)

end SpecialPair

end CFSG.Timmesfeld
