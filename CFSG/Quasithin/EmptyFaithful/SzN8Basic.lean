module

public import CFSG.Assembly.Defs
public import CFSG.Quasithin.Background.Ordering

public section

namespace CFSG.Quasithin

open scoped Pointwise

section Basic

variable {G : Type} [Group G]

theorem szN8_card_sup_mul_card_inf {X N : Subgroup G} (hXN : X ≤ Subgroup.normalizer (N : Set G)) :
    Nat.card (X ⊔ N : Subgroup G) * Nat.card (X ⊓ N : Subgroup G) = Nat.card X * Nat.card N := by
  have : (N.subgroupOf (X ⊔ N)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hXN
  have : (N.subgroupOf X).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hXN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient X N hXN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf X)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (X ⊔ N))
  have h3 : Nat.card (N.subgroupOf X) = Nat.card (X ⊓ N : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective X.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (N.subgroupOf (X ⊔ N)) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

theorem szN8_pow_cong {D C : Subgroup G} (hD : D ≤ Subgroup.normalizer (C : Set G)) {x p : G}
    (hx : x ∈ D) (hp : p ∈ D) (hxp : p⁻¹ * x ∈ C) (n : ℕ) : (p ^ n)⁻¹ * x ^ n ∈ C := by
  have : (C.subgroupOf D).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hD
  have h1 : ((⟨p, hp⟩ : ↥D) : ↥D ⧸ C.subgroupOf D) = ((⟨x, hx⟩ : ↥D) : ↥D ⧸ C.subgroupOf D) := by
    rw [QuotientGroup.eq]
    exact Subgroup.mem_subgroupOf.mpr (by simpa using hxp)
  have h2 : (((⟨p, hp⟩ : ↥D) ^ n : ↥D) : ↥D ⧸ C.subgroupOf D) =
      (((⟨x, hx⟩ : ↥D) ^ n : ↥D) : ↥D ⧸ C.subgroupOf D) := by
    rw [QuotientGroup.mk_pow, QuotientGroup.mk_pow, h1]
  have h3 := QuotientGroup.eq.mp h2
  have h4 := Subgroup.mem_subgroupOf.mp h3
  simpa using h4

end Basic

section Rank

variable {G : Type} [Group G] [Finite G]

theorem szN8_index_le_three {L P C : Subgroup G} (hP3 : IsPGroup 3 P) (hPe : ∀ x ∈ P, x ^ 3 = 1)
    (hPN : P ≤ Subgroup.normalizer (C : Set G)) (hinner : ∀ y ∈ P, ∃ x ∈ L, x⁻¹ * y ∈ C)
    (hLC : IsPGroup 2 ↥(L ⊓ C))
    (hrank : ∀ E : Subgroup G, E ≤ L → IsPGroup 3 E → (∀ x ∈ E, x ^ 3 = 1) → Nat.card E ≤ 3) :
    Nat.card P ≤ 3 * Nat.card ↥(P ⊓ C) := by
  classical
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let D : Subgroup G := P ⊔ C
  have hDN : D ≤ Subgroup.normalizer (C : Set G) := sup_le hPN Subgroup.le_normalizer
  have hDset : (D : Set G) = (P : Set G) * (C : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right P C hPN
  let E : Subgroup G := L ⊓ D
  have hkey : ∀ d ∈ D, ∃ e ∈ E, ∃ c ∈ C, d = e * c := by
    intro d hd
    have hd' : d ∈ (P : Set G) * (C : Set G) := hDset ▸ hd
    obtain ⟨p, hp, c₀, hc₀, rfl⟩ := hd'
    obtain ⟨x, hxL, hxc⟩ := hinner p hp
    refine ⟨x, ⟨hxL, ?_⟩, (x⁻¹ * p) * c₀, C.mul_mem hxc hc₀, by group⟩
    have hx : x = (p * c₀) * ((x⁻¹ * p) * c₀)⁻¹ := by group
    rw [hx]
    exact D.mul_mem hd (D.inv_mem (Subgroup.mem_sup_right (C.mul_mem hxc hc₀)))
  have hED : E ⊔ C = D := by
    refine le_antisymm (sup_le inf_le_right le_sup_right) fun d hd => ?_
    obtain ⟨e, he, c, hc, rfl⟩ := hkey d hd
    exact (E ⊔ C).mul_mem (Subgroup.mem_sup_left he) (Subgroup.mem_sup_right hc)
  have hEN : E ≤ Subgroup.normalizer (C : Set G) := inf_le_right.trans hDN
  have f1 := szN8_card_sup_mul_card_inf hPN
  have f2 := szN8_card_sup_mul_card_inf hEN
  rw [hED] at f2
  have hC0 : 0 < Nat.card C := Nat.card_pos
  have hmain : Nat.card P * Nat.card ↥(E ⊓ C) = Nat.card E * Nat.card ↥(P ⊓ C) := by
    apply Nat.eq_of_mul_eq_mul_right hC0
    calc Nat.card P * Nat.card ↥(E ⊓ C) * Nat.card C
        = (Nat.card P * Nat.card C) * Nat.card ↥(E ⊓ C) := by ring
      _ = (Nat.card D * Nat.card ↥(P ⊓ C)) * Nat.card ↥(E ⊓ C) := by rw [← f1]
      _ = (Nat.card D * Nat.card ↥(E ⊓ C)) * Nat.card ↥(P ⊓ C) := by ring
      _ = (Nat.card E * Nat.card C) * Nat.card ↥(P ⊓ C) := by rw [f2]
      _ = Nat.card E * Nat.card ↥(P ⊓ C) * Nat.card C := by ring
  obtain ⟨s, hs⟩ := IsPGroup.iff_card.mp hP3
  obtain ⟨r, hr⟩ := IsPGroup.iff_card.mp (hP3.to_inf_left (H := P) (K := C))
  have hEC2 : IsPGroup 2 ↥(E ⊓ C) :=
    hLC.to_le (inf_le_inf_right C inf_le_left)
  have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := IsPGroup.iff_card.mp hEC2
  have hrs : r ≤ s := by
    have hdvd : Nat.card ↥(P ⊓ C) ∣ Nat.card P := Subgroup.card_dvd_of_le inf_le_left
    rw [hr, hs] at hdvd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
  have hEcard : Nat.card E = 3 ^ (s - r) * 2 ^ u := by
    rw [hs, hu, hr] at hmain
    have h3r : 0 < 3 ^ r := by positivity
    apply Nat.eq_of_mul_eq_mul_right h3r
    calc Nat.card E * 3 ^ r = 3 ^ s * 2 ^ u := hmain.symm
      _ = 3 ^ (s - r) * 2 ^ u * 3 ^ r := by
        rw [show s = (s - r) + r by omega, pow_add]
        simp only [Nat.add_sub_cancel]
        ring
  obtain ⟨S⟩ : Nonempty (Sylow 3 ↥E) := inferInstance
  have hScard : Nat.card (S : Subgroup ↥E) = 3 ^ (s - r) := by
    rw [S.card_eq_multiplicity, hEcard, Nat.factorization_mul (by positivity) (by positivity),
      Finsupp.add_apply, Nat.factorization_pow, Nat.factorization_pow]
    simp [Nat.Prime.factorization_self Nat.prime_three,
      Nat.factorization_eq_zero_of_not_dvd (show ¬ 3 ∣ 2 by norm_num)]
  let S' : Subgroup G := (S : Subgroup ↥E).map E.subtype
  have hS'E : S' ≤ E := Subgroup.map_subtype_le _
  have hS'p : IsPGroup 3 ↥S' := S.isPGroup'.map E.subtype
  have hS'card : Nat.card ↥S' = 3 ^ (s - r) := by
    rw [Subgroup.card_map_of_injective E.subtype_injective, hScard]
  have hS'e : ∀ x ∈ S', x ^ 3 = 1 := by
    intro x hx
    have hxE : x ∈ E := hS'E hx
    have hxD : x ∈ D := hxE.2
    have hxD' : x ∈ (P : Set G) * (C : Set G) := hDset ▸ hxD
    obtain ⟨p, hp, c, hc, rfl⟩ := hxD'
    have hcong := szN8_pow_cong hDN (x := p * c) (p := p) hxD (Subgroup.mem_sup_left hp)
      (by simpa using hc) 3
    rw [hPe p hp, inv_one, one_mul] at hcong
    have hx3S : (p * c) ^ 3 ∈ S' := S'.pow_mem hx 3
    have hx3L : (p * c) ^ 3 ∈ L ⊓ C := ⟨(hS'E.trans inf_le_left) hx3S, hcong⟩
    obtain ⟨a, ha⟩ := hS'p ⟨_, hx3S⟩
    obtain ⟨b, hb⟩ := hLC ⟨_, hx3L⟩
    have ha' : ((p * c) ^ 3) ^ (3 ^ a) = 1 := by simpa using congrArg Subtype.val ha
    have hb' : ((p * c) ^ 3) ^ (2 ^ b) = 1 := by simpa using congrArg Subtype.val hb
    have h1 : orderOf ((p * c) ^ 3) ∣ 3 ^ a := orderOf_dvd_of_pow_eq_one ha'
    have h2 : orderOf ((p * c) ^ 3) ∣ 2 ^ b := orderOf_dvd_of_pow_eq_one hb'
    have h3 : orderOf ((p * c) ^ 3) ∣ Nat.gcd (3 ^ a) (2 ^ b) := Nat.dvd_gcd h1 h2
    have h4 : Nat.gcd (3 ^ a) (2 ^ b) = 1 :=
      Nat.Coprime.pow a b (by norm_num : Nat.Coprime 3 2)
    rw [h4] at h3
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  have hle3 := hrank S' (hS'E.trans inf_le_left) hS'p hS'e
  rw [hS'card] at hle3
  have hsr : s - r ≤ 1 := by
    by_contra h
    push Not at h
    have : 3 ^ 2 ≤ 3 ^ (s - r) := Nat.pow_le_pow_right (by norm_num) h
    omega
  rw [hs, hr]
  calc 3 ^ s = 3 ^ (s - r + r) := by congr 1; omega
    _ = 3 ^ (s - r) * 3 ^ r := pow_add _ _ _
    _ ≤ 3 ^ 1 * 3 ^ r := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hsr)
    _ = 3 * 3 ^ r := by norm_num

end Rank

end CFSG.Quasithin
