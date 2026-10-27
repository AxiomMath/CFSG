module

public import CFSG.RankThree.PartOne.S11b.Sec109
import CFSG.RankThree.PartOne.S10.SectionTenFiveNormalPCoreWitness
import CFSG.GroupTheory.HyperplaneGeneration
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG
open scoped commutatorElement

namespace Sec109

variable {G : Type} [Group G] [Finite G]

theorem exists_hyperplane_not_commute {p : ℕ} [Fact p.Prime] {A Q : Subgroup G}
    [IsElementaryAbelian p A] (hAQ : A ≤ normalizer (Q : Set G)) (hQp : ¬ p ∣ Nat.card Q)
    {c : G} (hc : c ∈ A) (hQc : ⁅Q, zpowers c⁆ ≠ ⊥) :
    ∃ H : Subgroup A, H.index = p ∧
      ∃ q ∈ Q, (∀ h : A, h ∈ H → (h : G) * q = q * h) ∧ c * q ≠ q * c := by
  classical
  by_contra hno
  push Not at hno
  have hc1 : c ≠ 1 := by
    rintro rfl
    exact hQc (by simp)
  have : Nontrivial A := ⟨⟨⟨c, hc⟩, 1, fun h => hc1 (congrArg Subtype.val h)⟩⟩
  let : MulDistribMulAction A Q := Subgroup.conjMulDistribMulActionOfLeNormalizer A Q hAQ
  have hgen := SolvableHall.coprime_hyperplane_generation (p := p) (A := A) (H := Q) hQp
  have hle : (⨆ (B' : Subgroup A) (_ : B'.index = p), fixedPointSubgroup B' Q) ≤
      (centralizer ({c} : Set G)).subgroupOf Q := by
    refine iSup₂_le fun B' hB' q hq => ?_
    rw [mem_subgroupOf, mem_centralizer_singleton_iff]
    have hq' : ∀ h : A, h ∈ B' → (h : G) * q * (h : G)⁻¹ = q := fun h hh =>
      congrArg Subtype.val (hq ⟨h, hh⟩)
    have := hno B' hB' q q.2 fun h hh => by
      have h1 := hq' h hh
      calc (h : G) * q = (h : G) * q * (h : G)⁻¹ * h := by group
        _ = q * h := by rw [h1]
    exact this.symm
  have hcomm : ∀ x : Q, x * c = c * x := by
    intro x
    have hx : x ∈ (⊤ : Subgroup Q) := mem_top x
    rw [← hgen] at hx
    have h2 := hle hx
    rw [mem_subgroupOf, mem_centralizer_singleton_iff] at h2
    exact h2
  apply hQc
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx y hy
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  exact ((Commute.zpow_left (show Commute c x from (hcomm ⟨x, hx⟩).symm) k)).eq

omit [Finite G] in
theorem le_normalizer_commutator_of_le_normalizers {N X Y : Subgroup G}
    (hX : N ≤ normalizer (X : Set G)) (hY : N ≤ normalizer (Y : Set G)) :
    N ≤ normalizer ((⁅X, Y⁆ : Subgroup G) : Set G) := by
  intro h hh
  rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hX hh), mem_normalizer_iff_map_conj_eq.mp (hY hh)]

theorem witnessExists : WitnessExists := by
  intro G _ _ p A c L B n hcfg
  classical
  have hS := hcfg.setup
  have hp : p.Prime := sectionTenSetup_prime hS
  have hAe : IsElementaryAbelian p A := hS.2.2.2.2.2.2.1
  have hAcard : Nat.card A = p ^ 3 := hS.2.2.2.2.2.2.2.1
  have hp7 : p = 7 := hcfg.p_eq
  have : Fact p.Prime := ⟨hp⟩
  have hcA := hcfg.c_mem
  obtain ⟨-, -, -, Q, hQ2, hAQ, -, -, hQne, -⟩ :=
    section_ten_five_normal_p_core_two_group_witness_frontier G p A hS c hcA hcfg.c_ne_one
  have hQp : ¬ p ∣ Nat.card Q := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ2
    rw [hk]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
    omega
  obtain ⟨H, hHidx, q, hqQ, hqH, hqc⟩ := exists_hyperplane_not_commute hAQ hQp hcA hQne
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩)
  let H' : Subgroup G := H.map A.subtype
  let Q1 : Subgroup G := Q ⊓ centralizer (H' : Set G)
  have hQ1Q : Q1 ≤ Q := inf_le_left
  have hcentH' : ∀ x ∈ H', ∀ s ∈ Q1, x * s = s * x := fun x hx s hs =>
    mem_centralizer_iff.mp hs.2 x hx
  have hfwd : ∀ a ∈ A, ∀ x ∈ Q1, a * x * a⁻¹ ∈ Q1 := by
    intro a ha x hx
    refine ⟨(mem_normalizer_iff.mp (hAQ ha) x).mp hx.1, mem_centralizer_iff.mpr ?_⟩
    intro y hy
    obtain ⟨y', hy', rfl⟩ := mem_map.mp hy
    have hya : Commute (y' : G) a := hAcomm y' y'.2 a ha
    have hyx : Commute (y' : G) x := hcentH' y' (mem_map.mpr ⟨y', hy', rfl⟩) x hx
    exact ((hya.mul_right hyx).mul_right hya.inv_right).eq
  have hAQ1 : A ≤ normalizer (Q1 : Set G) := by
    intro a ha
    rw [mem_normalizer_iff]
    intro x
    refine ⟨hfwd a ha x, fun hx => ?_⟩
    have h1 := hfwd a⁻¹ (A.inv_mem ha) _ hx
    have e : a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ = x := by group
    rwa [e] at h1
  have hAz : A ≤ normalizer ((zpowers c : Subgroup G) : Set G) := by
    have hfix : ∀ g ∈ A, ∀ h ∈ zpowers c, g * h * g⁻¹ = h := by
      intro g hg h hh
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
      have hcg : Commute (c ^ k) g := Commute.zpow_left (hAcomm c hcA g hg) k
      calc g * c ^ k * g⁻¹ = c ^ k * g * g⁻¹ := by rw [← hcg.eq]
        _ = c ^ k := by group
    intro a ha
    rw [mem_normalizer_iff]
    intro h
    refine ⟨fun hh => by rw [hfix a ha h hh]; exact hh, fun hh => ?_⟩
    have h1 := hfix a⁻¹ (A.inv_mem ha) _ hh
    have e : a⁻¹ * (a * h * a⁻¹) * a⁻¹⁻¹ = h := by group
    rw [e] at h1
    rw [h1]
    exact hh
  have hzQ1 : zpowers c ≤ normalizer (Q1 : Set G) := zpowers_le.mpr (hAQ1 hcA)
  have hSle : ⁅Q1, zpowers c⁆ ≤ Q1 := Subgroup.le_normalizer_iff_commutator_le_left.mp hzQ1
  have hqQ1 : q ∈ Q1 := ⟨hqQ, mem_centralizer_iff.mpr fun x hx => by
    obtain ⟨y', hy', rfl⟩ := mem_map.mp hx
    exact hqH y' hy'⟩
  have hBA : B ≤ A := by
    rw [hcfg.B_eq]
    exact inf_le_left
  have hB₀card : Nat.card (B.subgroupOf A) = 49 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBA).toEquiv]
    exact hcfg.B_card
  have hAcard' : Nat.card A = 343 := by
    rw [hAcard, hp7]
    norm_num
  have hB₀idx : (B.subgroupOf A).index = 7 := by
    have h := (B.subgroupOf A).card_mul_index
    rw [hB₀card, hAcard'] at h
    omega
  have hinfidx : ((B.subgroupOf A) ⊓ H).index ≤ 49 := by
    have h : ((B.subgroupOf A) ⊓ H).index ≤ (B.subgroupOf A).index * H.index :=
      Subgroup.index_inf_le
    rw [hB₀idx, hHidx, hp7] at h
    exact h
  have hinfcard : 1 < Nat.card ↥((B.subgroupOf A) ⊓ H) := by
    have h := ((B.subgroupOf A) ⊓ H).card_mul_index
    rw [hAcard'] at h
    by_contra hle
    push Not at hle
    have h2 : Nat.card ↥((B.subgroupOf A) ⊓ H) * ((B.subgroupOf A) ⊓ H).index ≤ 1 * 49 :=
      Nat.mul_le_mul hle hinfidx
    omega
  have : Nontrivial ↥((B.subgroupOf A) ⊓ H) := Finite.one_lt_card_iff_nontrivial.mp hinfcard
  obtain ⟨⟨x, hxB, hxH⟩, hx1⟩ := exists_ne (1 : ↥((B.subgroupOf A) ⊓ H))
  have hbH' : (x : G) ∈ H' := mem_map.mpr ⟨x, hxH, rfl⟩
  refine ⟨(x : G), ⁅Q1, zpowers c⁆, ?_⟩
  exact
    { b_mem := mem_subgroupOf.mp hxB
      b_ne_one := fun h => hx1 (Subtype.ext (Subtype.ext h))
      S_le := fun s hs => by
        rw [mem_centralizer_singleton_iff]
        exact (hcentH' (x : G) hbH' s (hSle hs)).symm
      S_ne_bot := by
        intro hbot
        have h1 : ⁅q, c⁆ ∈ ⁅Q1, zpowers c⁆ := commutator_mem_commutator hqQ1 (mem_zpowers c)
        rw [hbot, mem_bot, commutatorElement_def] at h1
        apply hqc
        calc c * q = (q * c * q⁻¹ * c⁻¹)⁻¹ * (q * c) := by group
          _ = q * c := by rw [h1]; simp
      S_two := hQ2.to_le (hSle.trans hQ1Q)
      S_norm := le_normalizer_commutator_of_le_normalizers hAQ1 hAz
      S_comm := by
        have hpow : c ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian c hcA
        have : IsElementaryAbelian p (zpowers c) := IsElementaryAbelian.zpowers_of_pow_eq_one hpow
        have hpg : IsPGroup p (zpowers c) := IsElementaryAbelian.isPGroup p _
        have hcompl : ¬ p ∣ Nat.card Q1 := fun h => hQp (h.trans (Subgroup.card_dvd_of_le hQ1Q))
        exact (CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent p hp
          (zpowers c) Q1 hpg hcompl hzQ1).symm }

end Sec109

end CFSG.RankThree.PartOne
