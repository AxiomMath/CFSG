module

public import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13

theorem eq_sup_of_card_nine' {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L : Subgroup G} (hD : Sec13Data G A c L) (h9 : Nat.card (A ⊓ L : Subgroup G) = 9)
    (hcL : c ∉ L) : A = Subgroup.zpowers c ⊔ (A ⊓ L) := by
  have hcB : c ∉ A ⊓ L := fun h => hcL (Subgroup.mem_inf.mp h).2
  set S := Subgroup.zpowers c ⊔ (A ⊓ L) with hSdef
  have hSA : S ≤ A := sup_le (Subgroup.zpowers_le.mpr hD.mem_A) inf_le_left
  have hBS : A ⊓ L ≤ S := le_sup_right
  have h1 : 9 ∣ Nat.card S := by
    rw [← h9]
    exact Subgroup.card_dvd_of_le hBS
  have h2 : Nat.card S ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hD.card_eq]
    exact Subgroup.card_dvd_of_le hSA
  have h3 : Nat.card S ≠ 9 := by
    intro h
    have hAL : A ⊓ L = S := Subgroup.eq_of_le_of_card_ge hBS (by rw [h, h9])
    apply hcB
    rw [hAL]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
  obtain ⟨k, hk, hSk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h2
  have h27 : Nat.card S = 27 := by
    rw [hSk] at h1 h3 ⊢
    interval_cases k
    · exact absurd h1 (by decide)
    · exact absurd h1 (by decide)
    · exact (h3 (by norm_num)).elim
    · norm_num
  exact (Subgroup.eq_of_le_of_card_ge hSA (by rw [h27, hD.card_eq])).symm

theorem normalizer_A_le_normalizer_L {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L : Subgroup G} (hD : Sec13Data G A c L) (h9 : Nat.card (A ⊓ L : Subgroup G) = 9)
    (hcL : c ∉ L)
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have hnot : ¬ (A ⊓ L : Subgroup G) ≤ Subgroup.zpowers c := by
    intro hle
    have h3 := Subgroup.card_dvd_of_le hle
    rw [h9, hD.card_zpowers] at h3
    norm_num at h3
  obtain ⟨d, hdAL, hdc⟩ := SetLike.not_le_iff_exists.mp hnot
  have hdA : d ∈ A := (Subgroup.mem_inf.mp hdAL).1
  have hdL : d ∈ L := (Subgroup.mem_inf.mp hdAL).2
  intro g hg
  have hgi : g ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
      Subgroup.normalizer (A : Set G) := ⟨hW hg, hg⟩
  exact normalizer_inf_le_of_mem hD.mem_thetaComponentsAt hD.le_normalizer
    hD.sectionCentralizer_eq hdA hdL hdc hgi

theorem inf_thetaQuotCentralizer_eq {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L : Subgroup G} (hD : Sec13Data G A c L) :
    A ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers c := by
  have hnorm : ∀ {l : G}, l ∈ L → ∀ {t : G}, t ∈ inSubgroup (aschbacherSolvableCore 3) L →
      l * t * l⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
    intro l hl t ht
    have hN : (aschbacherSolvableCore 3 L).Normal := by
      haveI := Sec4.aschbacherSolvableCore_characteristic L
      infer_instance
    unfold inSubgroup at ht ⊢
    obtain ⟨t', ht', rfl⟩ := Subgroup.mem_map.mp ht
    refine Subgroup.mem_map.mpr ⟨(⟨l, hl⟩ : L) * t' * (⟨l, hl⟩ : L)⁻¹, hN.conj_mem t' ht' _, ?_⟩
    simp
  ext x
  constructor
  · intro hx
    obtain ⟨hxA, hxq⟩ := Subgroup.mem_inf.mp hx
    rw [Sec6.mem_thetaQuotCentralizer_iff] at hxq
    obtain ⟨-, hxθ⟩ := hxq
    have hx' : x ∈ Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) := by
      show x ∈ A ∧ ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ (aschbacherSolvableCore 3 L).map L.subtype
      refine ⟨hxA, fun l hl => ?_⟩
      have h1 := hnorm hl (hxθ l hl)
      have e : l * (l⁻¹ * (x * l * x⁻¹)) * l⁻¹ = x * l * x⁻¹ * l⁻¹ := by group
      rw [e] at h1
      exact h1
    rw [hD.sectionCentralizer_eq] at hx'
    exact hx'
  · intro hx
    have hxA : x ∈ A := Subgroup.zpowers_le.mpr hD.mem_A hx
    refine Subgroup.mem_inf.mpr ⟨hxA, ?_⟩
    rw [Sec6.mem_thetaQuotCentralizer_iff]
    refine ⟨hD.le_normalizer hxA, fun l hl => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hlc : Commute l c := Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer hl)
    have hcomm : Commute (c ^ k) l := hlc.symm.zpow_left k
    have e : c ^ k * l * (c ^ k)⁻¹ = l := by
      rw [mul_inv_eq_iff_eq_mul]
      exact hcomm.eq
    rw [e, inv_mul_cancel]
    exact Subgroup.one_mem _

theorem mem_of_pow_three_of_commute {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L : Subgroup G} (hD : Sec13Data G A c L) {g : G} (hg : g ^ 3 = 1)
    (hcomm : ∀ a ∈ A, a * g = g * a) : g ∈ A := by
  have hB : CFSG.Assembly.IsElemAbelian 3 (A ⊔ Subgroup.zpowers g) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hD.isElemAbelian (CFSG.Open.isElemAbelian_zpowers hg)
      (fun a ha b hb => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
        exact ((show Commute a g from hcomm a ha).zpow_right k).eq)
  have hBA : A ⊔ Subgroup.zpowers g = A := hD.eq_of_le hB le_sup_left
  have hgB : g ∈ A ⊔ Subgroup.zpowers g := Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
  rw [hBA] at hgB
  exact hgB

theorem commute_of_mem_thetaQuotCentralizer {G : Type*} [Group G] [Finite G] {L Q : Subgroup G}
    (hΘ : Q ⊓ inSubgroup (aschbacherSolvableCore 3) L = ⊥) {b q : G} (hbL : b ∈ L) (hbQ : b ∈ Q)
    (hqQ : q ∈ Q) (hq : q ∈ Sec4.thetaQuotCentralizer L) : b * q = q * b := by
  rw [Sec6.mem_thetaQuotCentralizer_iff] at hq
  have hθ : b⁻¹ * (q * b * q⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) L := hq.2 b hbL
  have hQ : b⁻¹ * (q * b * q⁻¹) ∈ Q :=
    Q.mul_mem (Q.inv_mem hbQ) (Q.mul_mem (Q.mul_mem hqQ hbQ) (Q.inv_mem hqQ))
  have hmem : b⁻¹ * (q * b * q⁻¹) ∈ Q ⊓ inSubgroup (aschbacherSolvableCore 3) L :=
    Subgroup.mem_inf.mpr ⟨hQ, hθ⟩
  rw [hΘ, Subgroup.mem_bot] at hmem
  have h2 : b = q * b * q⁻¹ := inv_mul_eq_one.mp hmem
  calc b * q = q * b * q⁻¹ * q := by rw [← h2]
    _ = q * b := by group

end CFSG.RankThree.PartTwo.Sec13.F135Last
