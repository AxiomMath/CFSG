module

public import CFSG.Quasithin.EmptyFaithful.S146D2
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2711

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G] {n : ℕ} {P : Subgroup G}

theorem normalizer_odd_inner {L : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥L) {X : Type} [Group X]
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* X) (hX : CFSG.Quasithin.OddInner X) {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) (hodd : Odd (orderOf x)) :
    ∃ l ∈ L, l⁻¹ * x ∈ Subgroup.centralizer (L : Set G) := by
  have h1 : orderOf
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥L
        (L.normalizerMonoidHom ⟨x, hx⟩)) ∣
      orderOf (⟨x, hx⟩ : Subgroup.normalizer (L : Set G)) :=
    orderOf_map_dvd ((CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥L).comp
      L.normalizerMonoidHom) ⟨x, hx⟩
  rw [Subgroup.orderOf_mk] at h1
  obtain ⟨k, hk⟩ := CFSG.Quasithin.OddInner.of_mulEquiv e.symm hX _ (hodd.of_dvd_nat h1)
  exact CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711.exists_inner_of_quot hq hx
    ⟨k, hk.symm⟩

theorem le_normalizer_of_inner {L : Subgroup G}
    (hin : ∀ x ∈ P, ∃ l ∈ L, l⁻¹ * x ∈ Subgroup.centralizer (L : Set G)) :
    P ≤ Subgroup.normalizer (L : Set G) := by
  intro x hx
  obtain ⟨l, hl, hc⟩ := hin x hx
  have hx' : x = l * (l⁻¹ * x) := by group
  rw [hx']
  exact Subgroup.mul_mem _ (Subgroup.le_normalizer hl)
    (Subgroup.centralizer_le_normalizer (L : Set G) hc)

theorem ker_normalizerMonoidHom_comp_inclusion {L : Subgroup G}
    (hPN : P ≤ Subgroup.normalizer (L : Set G)) :
    (L.normalizerMonoidHom.comp (Subgroup.inclusion hPN)).ker =
      (P ⊓ Subgroup.centralizer (L : Set G)).subgroupOf P := by
  ext x
  have h1 : (L.normalizerMonoidHom.comp (Subgroup.inclusion hPN)) x = 1 ↔
      (x : G) ∈ Subgroup.centralizer (L : Set G) := by
    have := Subgroup.ext_iff.1 L.normalizerMonoidHom_ker (Subgroup.inclusion hPN x)
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf] at this
    exact this
  rw [MonoidHom.mem_ker, h1, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun hc => ⟨x.2, hc⟩, fun hc => hc.2⟩

theorem range_normalizerMonoidHom_comp_inclusion_le_conj {L : Subgroup G}
    (hPN : P ≤ Subgroup.normalizer (L : Set G))
    (hin : ∀ x ∈ P, ∃ l ∈ L, l⁻¹ * x ∈ Subgroup.centralizer (L : Set G)) :
    (L.normalizerMonoidHom.comp (Subgroup.inclusion hPN)).range ≤
      (MulAut.conj : ↥L →* MulAut ↥L).range := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨l, hl, hc⟩ := hin x x.2
  refine ⟨⟨l, hl⟩, ?_⟩
  ext y
  have hcy : (y : G) * (l⁻¹ * x) = (l⁻¹ * x) * y :=
    Subgroup.mem_centralizer_iff.1 hc y y.2
  have hxc : (x : G) = l * (l⁻¹ * x) := by group
  show l * (y : G) * l⁻¹ = (x : G) * (y : G) * (x : G)⁻¹
  calc l * (y : G) * l⁻¹ = l * ((y : G) * (l⁻¹ * x)) * (l⁻¹ * x)⁻¹ * l⁻¹ := by group
    _ = l * ((l⁻¹ * x) * y) * (l⁻¹ * x)⁻¹ * l⁻¹ := by rw [hcy]
    _ = (x : G) * (y : G) * (x : G)⁻¹ := by group

theorem ker_conj_eq_center (L : Subgroup G) :
    (MulAut.conj : ↥L →* MulAut ↥L).ker = Subgroup.center ↥L := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro h x
    have := congrArg (fun φ : MulAut ↥L => φ x) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc x * g = (g * x * g⁻¹) * g := by rw [this]
      _ = g * x := by group
  · intro h
    apply MulEquiv.ext
    intro x
    simp only [MulAut.conj_apply, MulAut.one_apply]
    calc g * x * g⁻¹ = x * g * g⁻¹ := by rw [h x]
      _ = x := by group

theorem card_range_conj_eq_card_quotient_center (L : Subgroup G) :
    Nat.card (MulAut.conj : ↥L →* MulAut ↥L).range =
      Nat.card (↥L ⧸ Subgroup.center ↥L) := by
  have h1 := Subgroup.card_ker_mul_card_range (MulAut.conj : ↥L →* MulAut ↥L)
  rw [ker_conj_eq_center L] at h1
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L)
  have hpos : 0 < Nat.card (Subgroup.center ↥L) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [h1, h2, mul_comm]

theorem card_le_of_inner {L : Subgroup G} (hP : IsPGroup 3 ↥P)
    (hin : ∀ x ∈ P, ∃ l ∈ L, l⁻¹ * x ∈ Subgroup.centralizer (L : Set G)) {k : ℕ}
    (hk : ¬ 3 ^ (k + 1) ∣ Nat.card (↥L ⧸ Subgroup.center ↥L)) :
    Nat.card ↥P ≤ Nat.card ↥(P ⊓ Subgroup.centralizer (L : Set G)) * 3 ^ k := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPN : P ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_inner hin
  let ρ : ↥P →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hPN)
  have hker : ρ.ker = (P ⊓ Subgroup.centralizer (L : Set G)).subgroupOf P :=
    ker_normalizerMonoidHom_comp_inclusion hPN
  have hrange : ρ.range ≤ (MulAut.conj : ↥L →* MulAut ↥L).range :=
    range_normalizerMonoidHom_comp_inclusion_le_conj hPN hin
  have hcardP : Nat.card ρ.ker * Nat.card ρ.range = Nat.card ↥P :=
    Subgroup.card_ker_mul_card_range ρ
  have hrange3 : IsPGroup 3 ρ.range :=
    hP.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 hrange3
  have hcardInn : Nat.card (MulAut.conj : ↥L →* MulAut ↥L).range =
      Nat.card (↥L ⧸ Subgroup.center ↥L) := card_range_conj_eq_card_quotient_center L
  have hdvd : Nat.card ρ.range ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := by
    have := Subgroup.card_dvd_of_le hrange
    rwa [hcardInn] at this
  have hjk : j ≤ k := by
    by_contra hlt
    have hlt := not_le.1 hlt
    apply hk
    rw [hj] at hdvd
    exact (pow_dvd_pow 3 hlt).trans hdvd
  have hkercard : Nat.card ρ.ker = Nat.card ↥(P ⊓ Subgroup.centralizer (L : Set G)) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : P ⊓ _ ≤ P)).toEquiv
  rw [← hcardP, hkercard, hj]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hjk)

theorem card_sylow_of_cover {L T : Subgroup G} (hT : IsSylowOf 3 T L)
    (hz : Nat.card (Subgroup.center ↥L) = 3) {k : ℕ}
    (hk : 3 ^ k ∣ Nat.card (↥L ⧸ Subgroup.center ↥L))
    (hk' : ¬ 3 ^ (k + 1) ∣ Nat.card (↥L ⧸ Subgroup.center ↥L)) : Nat.card ↥T = 3 ^ (k + 1) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [hT.card_eq]
  have hm0 : Nat.card (↥L ⧸ Subgroup.center ↥L) ≠ 0 := Nat.card_pos.ne'
  have hcard : Nat.card ↥L = 3 * Nat.card (↥L ⧸ Subgroup.center ↥L) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L), hz, mul_comm]
  have h1 : k ≤ (Nat.card (↥L ⧸ Subgroup.center ↥L)).factorization 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hm0).1 hk
  have h2 : ¬ k + 1 ≤ (Nat.card (↥L ⧸ Subgroup.center ↥L)).factorization 3 := fun h =>
    hk' ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hm0).2 h)
  rw [hcard, Nat.factorization_mul (by norm_num) hm0]
  simp only [Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_three,
    Finsupp.single_eq_same]
  congr 1
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326
