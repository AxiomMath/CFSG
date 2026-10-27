module

public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4Lift

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

section Abstract

variable {H : Type*} [Group H] [Finite H]

theorem eq_one_of_pgroup_of_coprime {P Q : Subgroup H} (hP : IsPGroup 3 P)
    (hQ : Nat.Coprime 3 (Nat.card Q)) {x : H} (hxP : x ∈ P) (hxQ : x ∈ Q) : x = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hP ⟨x, hxP⟩
  have h1 : orderOf x ∣ 3 ^ k := by
    have : orderOf (⟨x, hxP⟩ : P) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
    rwa [Subgroup.orderOf_mk] at this
  have h2 : orderOf x ∣ Nat.card Q := by
    have : orderOf (⟨x, hxQ⟩ : Q) ∣ Nat.card Q := orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk] at this
  have h3 : Nat.Coprime (3 ^ k) (Nat.card Q) := hQ.pow_left k
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes h3 h1 h2)

theorem sylow_lift_pgroup (Q : Subgroup H) [Q.Normal] (hQ : Nat.Coprime 3 (Nat.card Q))
    (T : Subgroup (H ⧸ Q)) (hT3 : IsPGroup 3 T) (D : Subgroup H)
    (hD : ∀ t ∈ T, ∃ c ∈ D, (QuotientGroup.mk c : H ⧸ Q) = t)
    (hDT : ∀ c ∈ D, (QuotientGroup.mk c : H ⧸ Q) ∈ T) (c₀ : H) (hc₀D : c₀ ∈ D)
    (hc₀3 : IsPGroup 3 (Subgroup.zpowers c₀)) :
    ∃ P : Subgroup H, P ≤ D ∧ c₀ ∈ P ∧ IsPGroup 3 P ∧ Nat.card P = Nat.card T ∧
      P.map (QuotientGroup.mk' Q) = T := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let c' : ↥D := ⟨c₀, hc₀D⟩
  have hz : IsPGroup 3 (Subgroup.zpowers c') := by
    obtain ⟨k, hk⟩ := hc₀3 ⟨c₀, Subgroup.mem_zpowers c₀⟩
    have hk' : c₀ ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hord : orderOf c' ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hk'))
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hord
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  obtain ⟨S, hS⟩ := hz.exists_le_sylow
  let P : Subgroup H := (S : Subgroup ↥D).map D.subtype
  have hPD : P ≤ D := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hPcard : Nat.card P = Nat.card S := Subgroup.card_map_of_injective D.subtype_injective
  have hPp : IsPGroup 3 P := S.2.map D.subtype
  have hc₀P : c₀ ∈ P := ⟨c', hS (Subgroup.mem_zpowers c'), rfl⟩
  have hinj : Function.Injective (fun x : P => (QuotientGroup.mk' Q x.1 : H ⧸ Q)) := by
    intro x y hxy
    have hmem : (x.1)⁻¹ * y.1 ∈ Q := QuotientGroup.eq.mp hxy
    have hP' : (x.1)⁻¹ * y.1 ∈ P := P.mul_mem (P.inv_mem x.2) y.2
    have := eq_one_of_pgroup_of_coprime hPp hQ hP' hmem
    exact Subtype.ext (inv_mul_eq_one.mp this)
  have hle : P.map (QuotientGroup.mk' Q) ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    exact hDT x (hPD hx)
  have hsurj : Function.Surjective
      (((QuotientGroup.mk' Q).comp D.subtype).codRestrict T (fun c => hDT c c.2)) := by
    rintro ⟨t, ht⟩
    obtain ⟨c, hc, hct⟩ := hD t ht
    exact ⟨⟨c, hc⟩, Subtype.ext hct⟩
  have hTD : Nat.card T ∣ Nat.card D := Subgroup.card_dvd_of_surjective hsurj
  obtain ⟨k, hk⟩ := hT3.exists_card_eq
  have hTP : Nat.card T ≤ Nat.card P := by
    rw [hPcard, Sylow.card_eq_multiplicity S]
    have hDne : Nat.card D ≠ 0 := Nat.card_pos.ne'
    have : 3 ^ k ∣ Nat.card D := hk ▸ hTD
    exact hk ▸ Nat.le_of_dvd (by positivity)
      (pow_dvd_pow 3 ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hDne).mp this))
  have hmapcard : Nat.card P ≤ Nat.card (P.map (QuotientGroup.mk' Q)) := by
    refine Nat.card_le_card_of_injective
      (fun x : P => (⟨QuotientGroup.mk' Q x.1, Subgroup.mem_map_of_mem _ x.2⟩ :
        ↥(P.map (QuotientGroup.mk' Q)))) ?_
    intro x y hxy
    exact hinj (congrArg Subtype.val hxy)
  have hTle : Nat.card T ≤ Nat.card (P.map (QuotientGroup.mk' Q)) := hTP.trans hmapcard
  have hmapeq : P.map (QuotientGroup.mk' Q) = T :=
    Subgroup.eq_of_le_of_card_ge hle hTle
  refine ⟨P, hPD, hc₀P, hPp, ?_, hmapeq⟩
  rw [hmapeq] at hmapcard
  omega

end Abstract

section Lift

variable {G : Type} [Group G] [Finite G]

theorem cq_lift_pgroup {U : Subgroup G} {b : G} (hb : b ∈ Nor U) (hb3 : b ^ 3 = 1)
    (T : Subgroup (CQ U)) (hT : ∀ t ∈ T, cqβ U b hb t = t) (hT3 : IsPGroup 3 T)
    (c₀ : ↥(CenS U)) (hc₀b : (c₀ : G) ∈ Cen b) (hc₀3 : IsPGroup 3 (Subgroup.zpowers c₀))
    (hc₀ : (QuotientGroup.mk c₀ : CQ U) ∈ T) :
    ∃ T' : Subgroup G, T' ≤ Cen b ⊓ CenS U ∧ (c₀ : G) ∈ T' ∧ IsPGroup 3 T' ∧
      Nat.card T' = Nat.card T ∧ cqImg U T' = T := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : (pPrimeCore 3 ↥(CenS U)).Normal := pPrimeCore_normal
  let D : Subgroup ↥(CenS U) :=
    T.comap (QuotientGroup.mk' (pPrimeCore 3 ↥(CenS U))) ⊓ (Cen b).subgroupOf (CenS U)
  have hDmem : ∀ c : ↥(CenS U), c ∈ D ↔
      (QuotientGroup.mk c : CQ U) ∈ T ∧ (c : G) ∈ Cen b := fun c => Iff.rfl
  obtain ⟨P, hPD, hc₀P, hPp, hcard, hmap⟩ := sylow_lift_pgroup (pPrimeCore 3 ↥(CenS U))
    pPrimeCore_coprime_card T hT3 D
    (fun t ht => by
      obtain ⟨c, hcb, hct⟩ := cq_lift_fixed hb hb3 (hT t ht)
      exact ⟨c, (hDmem c).mpr ⟨hct ▸ ht, hcb⟩, hct⟩)
    (fun c hc => ((hDmem c).mp hc).1) c₀ ((hDmem c₀).mpr ⟨hc₀, hc₀b⟩) hc₀3
  refine ⟨P.map (CenS U).subtype, ?_, ⟨c₀, hc₀P, rfl⟩, hPp.map _, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨((hDmem x).mp (hPD hx)).2, x.2⟩
  · rw [Subgroup.card_map_of_injective (CenS U).subtype_injective, hcard]
  · have : (P.map (CenS U).subtype).subgroupOf (CenS U) = P := by
      ext x
      constructor
      · intro hx
        obtain ⟨y, hy, hyx⟩ := hx
        have : y = x := Subtype.ext hyx
        exact this ▸ hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    unfold cqImg
    rw [this]
    exact hmap

end Lift

end CFSG.RankThree.PartTwo.Sec21.FF79
