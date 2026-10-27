module

public import CFSG.RankThree.PartTwo.Sec14.Item148StepQuot

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422S

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem pow_eq_of_mul_eq_mul_pow_prime {p j m u c : ℕ} (hp : p.Prime) (hu : ¬ p ∣ u)
    (hc : ¬ p ∣ c) (h : p ^ j * u = c * p ^ m) : j = m := by
  rcases lt_trichotomy j m with hjm | hjm | hjm
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_lt hjm
    have h' : p ^ j * u = p ^ j * (c * p ^ (t + 1)) := by rw [h]; ring
    have hu' : u = c * p ^ (t + 1) := Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos j) h'
    have hdvd : p ∣ u := by
      rw [hu']
      exact Dvd.dvd.mul_left (dvd_pow_self p (by omega)) c
    exact absurd hdvd hu
  · exact hjm
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_lt hjm
    have h' : p ^ m * (p ^ (t + 1) * u) = p ^ m * c := by
      calc p ^ m * (p ^ (t + 1) * u) = p ^ (m + t + 1) * u := by ring
        _ = c * p ^ m := h
        _ = p ^ m * c := by ring
    have hc' : p ^ (t + 1) * u = c := Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos m) h'
    have hdvd : p ∣ c := by
      rw [← hc']
      exact Dvd.dvd.mul_right (dvd_pow_self p (by omega)) u
    exact absurd hdvd hc

section LiftP

variable {A Y : Subgroup G} [(ker148 A Y).Normal]

theorem exists_lift_isPGroup_three148 (hA3 : IsPGroup 3 A)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    {P' : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)} (hP' : IsPGroup 3 P')
    (hAP' : img148 A Y A ≤ P') :
    ∃ P : Subgroup G, A ≤ P ∧ P ≤ Y ⊔ A ∧ IsPGroup 3 P ∧ img148 A Y P = P' ∧
      Nat.card P = Nat.card P' ∧
      ∀ x ∈ P, ∀ y ∈ P, ∀ (hx : x ∈ Y ⊔ A) (hy : y ∈ Y ⊔ A),
        QuotientGroup.mk' (ker148 A Y) ⟨x, hx⟩ =
          QuotientGroup.mk' (ker148 A Y) ⟨y, hy⟩ → x = y := by
  have hle : pPrimeCoreOf 3 Y ≤ Y ⊔ A := (pPrimeCoreOf_le 3 Y).trans le_sup_left
  have hcardK : Nat.card ↥(ker148 A Y) = Nat.card ↥(pPrimeCoreOf 3 Y) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hK3 : ¬ 3 ∣ Nat.card ↥(ker148 A Y) := by
    rw [hcardK]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 Y)
  set Q : Subgroup ↥(Y ⊔ A) := P'.comap (QuotientGroup.mk' (ker148 A Y)) with hQdef
  have hQmem : ∀ g : ↥(Y ⊔ A), g ∈ Q ↔ QuotientGroup.mk' (ker148 A Y) g ∈ P' := fun g => by
    rw [hQdef, Subgroup.mem_comap]
  have hQcard : Nat.card ↥Q = Nat.card ↥(ker148 A Y) * Nat.card ↥P' :=
    QuotientGroup.card_preimage_mk (ker148 A Y) (P' : Set (↥(Y ⊔ A) ⧸ ker148 A Y))
  obtain ⟨m, hm⟩ := hP'.exists_card_eq
  have hAQ : A.subgroupOf (Y ⊔ A) ≤ Q := fun x hx =>
    (hQmem x).mpr (hAP' (Subgroup.mem_map_of_mem (QuotientGroup.mk' (ker148 A Y)) hx))
  have hS1 : IsPGroup 3 (A.subgroupOf (Y ⊔ A)) := hA3.comap_subtype
  have hS0 : IsPGroup 3 ((A.subgroupOf (Y ⊔ A)).subgroupOf Q) := hS1.comap_subtype
  obtain ⟨T, hTS⟩ := hS0.exists_le_sylow
  obtain ⟨j, hj⟩ := T.isPGroup'.exists_card_eq
  have hTidx : ¬ 3 ∣ (T : Subgroup ↥Q).index := Sylow.not_dvd_index T
  have hidx : 3 ^ j * (T : Subgroup ↥Q).index = Nat.card ↥(ker148 A Y) * 3 ^ m := by
    rw [← hj, ← hm, ← hQcard]
    exact Subgroup.card_mul_index _
  have hjm : j = m := pow_eq_of_mul_eq_mul_pow_prime Nat.prime_three hTidx hK3 hidx
  have hTcard : Nat.card ↥(T : Subgroup ↥Q) = Nat.card ↥P' := by
    rw [hj, hjm, hm]
  obtain ⟨P₁, hP₁⟩ : ∃ P₁ : Subgroup ↥(Y ⊔ A), P₁ = (T : Subgroup ↥Q).map Q.subtype :=
    ⟨_, rfl⟩
  have hP₁Q : P₁ ≤ Q := by
    rw [hP₁]
    exact Subgroup.map_subtype_le _
  have hP₁card : Nat.card ↥P₁ = Nat.card ↥P' := by
    rw [hP₁, Subgroup.card_map_of_injective Q.subtype_injective]
    exact hTcard
  obtain ⟨P, hPdef⟩ : ∃ P : Subgroup G, P = P₁.map (Y ⊔ A).subtype := ⟨_, rfl⟩
  have hmemP : ∀ u : ↥(Y ⊔ A), u ∈ P₁ → (u : G) ∈ P := fun u hu => by
    rw [hPdef]
    exact Subgroup.mem_map_of_mem _ hu
  have hPcard : Nat.card ↥P = Nat.card ↥P₁ := by
    rw [hPdef]
    exact Subgroup.card_map_of_injective (Y ⊔ A).subtype_injective
  have hPp : IsPGroup 3 P := IsPGroup.of_card (n := m) (by rw [hPcard, hP₁card, hm])
  have hPYA : P ≤ Y ⊔ A := by
    rw [hPdef]
    rintro _ ⟨u, -, rfl⟩
    exact u.2
  have hAP : A ≤ P := by
    intro a ha
    have haY : a ∈ Y ⊔ A := Subgroup.mem_sup_right ha
    have hxA : (⟨a, haY⟩ : ↥(Y ⊔ A)) ∈ A.subgroupOf (Y ⊔ A) := Subgroup.mem_subgroupOf.mpr ha
    have hxQ : (⟨a, haY⟩ : ↥(Y ⊔ A)) ∈ Q := hAQ hxA
    have hxS : (⟨⟨a, haY⟩, hxQ⟩ : ↥Q) ∈ (A.subgroupOf (Y ⊔ A)).subgroupOf Q :=
      Subgroup.mem_subgroupOf.mpr hxA
    have hxP₁ : (⟨a, haY⟩ : ↥(Y ⊔ A)) ∈ P₁ := by
      rw [hP₁]
      exact Subgroup.mem_map_of_mem Q.subtype (hTS hxS)
    exact hmemP _ hxP₁
  have hP_ker : ∀ g ∈ P, g ∈ pPrimeCoreOf 3 Y → g = 1 := by
    intro g hg hgN
    obtain ⟨k, hk⟩ := hPp ⟨g, hg⟩
    have hk' : g ^ 3 ^ k = 1 := congrArg Subtype.val hk
    exact eq_one_of_pow_three_pow_eq_one148 (coprime_card_pPrimeCoreOf 3 Y) hgN hk'
  have hPsub : P.subgroupOf (Y ⊔ A) = P₁ := by
    ext u
    rw [Subgroup.mem_subgroupOf, hPdef, Subgroup.mem_map]
    constructor
    · rintro ⟨v, hv, hvu⟩
      rwa [Subtype.ext hvu] at hv
    · intro hu
      exact ⟨u, hu, rfl⟩
  have hinj : ∀ x ∈ P₁, QuotientGroup.mk' (ker148 A Y) x = 1 → x = 1 := by
    intro x hx hx1
    exact Subtype.ext (hP_ker _ (hmemP x hx) (mk'_ker148_eq_one_iff.mp hx1))
  have hPimg : img148 A Y P = P' := by
    show (P.subgroupOf (Y ⊔ A)).map (QuotientGroup.mk' (ker148 A Y)) = P'
    rw [hPsub]
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.map_le_iff_le_comap]
      exact hP₁Q
    · exact le_of_eq (by rw [card_map_eq_of_ker148 hinj, hP₁card])
  refine ⟨P, hAP, hPYA, hPp, hPimg, ?_, ?_⟩
  · rw [hPcard, hP₁card]
  · intro x hxP y hyP hxY hyY hxy
    have hmem : x⁻¹ * y ∈ pPrimeCoreOf 3 Y := mk'_ker148_eq_iff.mp hxy
    exact inv_mul_eq_one.mp (hP_ker _ (P.mul_mem (P.inv_mem hxP) hyP) hmem)

end LiftP

end CFSG.RankThree.PartTwo.Sec14.Ronan1422S
