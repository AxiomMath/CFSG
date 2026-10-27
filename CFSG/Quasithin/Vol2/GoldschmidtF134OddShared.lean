module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.QuasithinUnique CFSG.ComponentClassification.OuterAutomorphisms

theorem le_of_sylowTwo {G : Type*} [Group G] [Finite G] {S V H : Subgroup G} (hS : IsSylowTwoOf S H)
    (hSV : S ≤ V) (hVH : V ≤ H) (hV : IsPGroup 2 V) : V ≤ S := by
  have hmul := Subgroup.relIndex_mul_relIndex S V H hSV hVH
  have hSH : ¬ 2 ∣ S.relIndex H := hS.2.2
  have hodd : ¬ 2 ∣ S.relIndex V := fun h => hSH (hmul ▸ Dvd.dvd.mul_right h _)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hV
  have hdvd : S.relIndex V ∣ 2 ^ k := hk ▸ Subgroup.relIndex_dvd_card S V
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hj0 : j = 0 := by
    by_contra h
    exact hodd (hj ▸ dvd_pow_self 2 h)
  rw [hj0, pow_zero, Subgroup.relIndex_eq_one] at hj
  exact hj

theorem exists_inner_of_odd_outer {A : Type*} [Group A] {L : Subgroup A} {g : A}
    (hg : g ∈ Subgroup.normalizer (L : Set A)) (hodd : Odd (Nat.card (Outer ↥L)))
    (hg2 : ∃ k : ℕ, g ^ 2 ^ k = 1) :
    ∃ x : L, ∀ l : L, g * (l : A) * g⁻¹ = (x : A) * l * (x : A)⁻¹ := by
  obtain ⟨k, hk⟩ := hg2
  let φ : MulAut ↥L := L.normalizerMonoidHom ⟨g, hg⟩
  let π : MulAut ↥L →* Outer ↥L := QuotientGroup.mk' (inner ↥L)
  have hφ : φ ^ 2 ^ k = 1 := by
    have h1 : (⟨g, hg⟩ : Subgroup.normalizer (L : Set A)) ^ 2 ^ k = 1 := Subtype.ext hk
    change L.normalizerMonoidHom ⟨g, hg⟩ ^ 2 ^ k = 1
    rw [← map_pow, h1, map_one]
  have h1 : (π φ) ^ 2 ^ k = 1 := by rw [← map_pow, hφ, map_one]
  have h2 : orderOf (π φ) ∣ Nat.card (Outer ↥L) := orderOf_dvd_natCard _
  have h3 : orderOf (π φ) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (Outer ↥L)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have h4 : orderOf (π φ) = 1 := Nat.eq_one_of_dvd_coprimes hcop h3 h2
  obtain ⟨x, hx⟩ := (QuotientGroup.eq_one_iff φ).mp (orderOf_eq_one_iff.mp h4)
  refine ⟨x, fun l => ?_⟩
  have h5 := congrArg (fun ψ : MulAut ↥L => ((ψ l : L) : A)) hx
  simpa [φ, MulAut.conj_apply] using h5.symm

theorem fix_of_inner {A : Type*} [Group A] [Finite A] {L U : Subgroup A}
    (hZ : Subgroup.center L = ⊥) (hU : IsSylowTwoOf U L) {y g : A} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hyL : y ∈ L) (hyo : orderOf y = p)
    (hyU : y ∈ Subgroup.normalizer (U : Set A)) (hgU : g ∈ Subgroup.normalizer (U : Set A))
    (hgy : g ∈ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup A) : Set A))
    (hg2 : ∃ k : ℕ, g ^ 2 ^ k = 1) {x : L}
    (hx : ∀ l : L, g * (l : A) * g⁻¹ = (x : A) * l * (x : A)⁻¹) : g * y * g⁻¹ = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := hg2
  have hpow : ∀ n : ℕ, ∀ l : L,
      g ^ n * (l : A) * (g ^ n)⁻¹ = ((x ^ n : L) : A) * l * ((x ^ n : L) : A)⁻¹ := by
    intro n
    induction n with
    | zero => intro l; simp
    | succ n ih =>
      intro l
      have h1 := hx l
      have h2 := ih (x * l * x⁻¹)
      calc g ^ (n + 1) * (l : A) * (g ^ (n + 1))⁻¹
          = g ^ n * (g * (l : A) * g⁻¹) * (g ^ n)⁻¹ := by group
        _ = g ^ n * ((x : A) * l * (x : A)⁻¹) * (g ^ n)⁻¹ := by rw [h1]
        _ = ((x ^ n : L) : A) * ((x * l * x⁻¹ : L) : A) * ((x ^ n : L) : A)⁻¹ := by
          simpa using h2
        _ = ((x ^ (n + 1) : L) : A) * l * ((x ^ (n + 1) : L) : A)⁻¹ := by
          simp only [pow_succ, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
          group
  have hxa : x ^ 2 ^ a = 1 := by
    have hmem : x ^ 2 ^ a ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro l
      have h := hpow (2 ^ a) l
      rw [ha] at h
      apply Subtype.ext
      simp only [inv_one, mul_one, one_mul] at h
      simp only [Subgroup.coe_mul]
      calc (l : A) * ((x ^ 2 ^ a : L) : A)
          = (((x ^ 2 ^ a : L) : A) * l * ((x ^ 2 ^ a : L) : A)⁻¹) * ((x ^ 2 ^ a : L) : A) := by
            rw [← h]
        _ = ((x ^ 2 ^ a : L) : A) * l := by simp [mul_assoc]
    rw [hZ, Subgroup.mem_bot] at hmem
    exact hmem
  have hxU : (x : A) ∈ Subgroup.normalizer (U : Set A) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [← hx ⟨h, hU.1 hh⟩]
      exact (Subgroup.mem_normalizer_iff.mp hgU h).mp hh
    · intro hh
      have hL : h ∈ L := by
        have := L.mul_mem (L.mul_mem (L.inv_mem x.2) (hU.1 hh)) x.2
        rwa [show (x : A)⁻¹ * ((x : A) * h * (x : A)⁻¹) * x = h by group] at this
      rw [← hx ⟨h, hL⟩] at hh
      exact (Subgroup.mem_normalizer_iff.mp hgU h).mpr hh
  have hx2 : IsPGroup 2 (Subgroup.zpowers (x : A)) := by
    have hxa' : (x : A) ^ 2 ^ a = 1 := by
      rw [← SubgroupClass.coe_pow, hxa, OneMemClass.coe_one]
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hxa')
    exact IsPGroup.of_card (n := b) (by rw [Nat.card_zpowers, hb])
  have hsup := le_of_sylowTwo hU le_sup_right
    (sup_le (Subgroup.zpowers_le.mpr x.2) hU.1)
    (hx2.to_sup_of_normal_right' hU.2.1 (Subgroup.zpowers_le.mpr hxU))
  have hxU' : (x : A) ∈ U := hsup (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
  have hc1 : (x : A) * y * (x : A)⁻¹ * y⁻¹ ∈ Subgroup.zpowers y := by
    have h1 : g * y * g⁻¹ = (x : A) * y * (x : A)⁻¹ := hx ⟨y, hyL⟩
    have h2 : g * y * g⁻¹ ∈ Subgroup.zpowers y :=
      (Subgroup.mem_normalizer_iff.mp hgy y).mp (Subgroup.mem_zpowers y)
    rw [h1] at h2
    exact (Subgroup.zpowers y).mul_mem h2 ((Subgroup.zpowers y).inv_mem (Subgroup.mem_zpowers y))
  have hc2 : (x : A) * y * (x : A)⁻¹ * y⁻¹ ∈ U := by
    rw [show (x : A) * y * (x : A)⁻¹ * y⁻¹ = x * (y * (x : A)⁻¹ * y⁻¹) by group]
    exact U.mul_mem hxU' ((Subgroup.mem_normalizer_iff.mp hyU (x : A)⁻¹).mp (U.inv_mem hxU'))
  have hP : IsPGroup p (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyo, pow_one])
  have hdisj := IsPGroup.disjoint_of_ne p 2 hp2 (Subgroup.zpowers y) U hP hU.2.1
  have hc : (x : A) * y * (x : A)⁻¹ * y⁻¹ = 1 := Subgroup.disjoint_def.mp hdisj hc1 hc2
  rw [hx ⟨y, hyL⟩]
  exact mul_inv_eq_one.mp hc

end CFSG.Quasithin.H13.NQCore
