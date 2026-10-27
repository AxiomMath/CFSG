module

public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionAction
public import CFSG.RankThree.PartOne.S9.OddCore.TorsionQD32

public section

namespace CFSG.RankThree.PartOne.OddCore37

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne.Torsion37
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_normalizer_center {R : Subgroup G} {a : G} (ha : a ∈ Subgroup.normalizer (R : Set G)) :
    a ∈ Subgroup.normalizer ((inSubgroup Subgroup.center R : Subgroup G) : Set G) := by
  have key : ∀ b ∈ Subgroup.normalizer (R : Set G), ∀ x ∈ inSubgroup Subgroup.center R,
      b * x * b⁻¹ ∈ inSubgroup Subgroup.center R := by
    rintro b hb _ ⟨z, hz, rfl⟩
    have hbR : b * (z : G) * b⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.1 hb z).1 z.2
    have hz' : z ∈ Subgroup.center ↥R := hz
    refine ⟨⟨b * z * b⁻¹, hbR⟩, ?_, rfl⟩
    show _ ∈ Subgroup.center ↥R
    rw [Subgroup.mem_center_iff]
    intro y
    have hy : b⁻¹ * (y : G) * b ∈ R := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hb) (y : G)).1 y.2
      simpa using this
    have hzc : (b⁻¹ * (y : G) * b) * (z : G) = (z : G) * (b⁻¹ * (y : G) * b) :=
      congrArg Subtype.val (Subgroup.mem_center_iff.1 hz' ⟨b⁻¹ * y * b, hy⟩)
    apply Subtype.ext
    change (y : G) * (b * z * b⁻¹) = b * z * b⁻¹ * y
    calc (y : G) * (b * z * b⁻¹) = b * ((b⁻¹ * y * b) * z) * b⁻¹ := by group
      _ = b * (z * (b⁻¹ * y * b)) * b⁻¹ := by rw [hzc]
      _ = b * z * b⁻¹ * y := by group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key a ha x, fun h => ?_⟩
  have := key a⁻¹ (inv_mem ha) _ h
  simpa [mul_assoc] using this

variable [Finite G]

theorem eq_two_or_thirtytwo {c : ℕ} (hdvd : c ∣ 32) (hmod : c ≡ 2 [MOD 5]) : c = 2 ∨ c = 32 := by
  have hle : c ≤ 32 := Nat.le_of_dvd (by norm_num) hdvd
  unfold Nat.ModEq at hmod
  interval_cases c <;> omega

theorem irreducible_of_qd32 {A R : Subgroup G} (hA : Nat.card A = 5)
    (hRA : A ≤ Subgroup.normalizer (R : Set G)) (hcomm : ⁅R, A⁆ = R)
    (hR : Nonempty (R ≃* QD32)) :
    ∀ Y : Subgroup G, inSubgroup Subgroup.center R ≤ Y → Y ≤ R →
      A ≤ Subgroup.normalizer (Y : Set G) →
      Y = inSubgroup Subgroup.center R ∨ Y = R := by
  intro Y hZY hYR hAY
  obtain ⟨hext, hR32, -⟩ := qd32_facts hR
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hZcard : Nat.card (inSubgroup Subgroup.center R) = 2 := by
    rw [inSubgroup, Subgroup.card_map_of_injective R.subtype_injective]
    exact hext.2.2.2
  have hRne : R ≠ ⊥ := by
    intro h
    have h1 : Nat.card R = 1 := by rw [h, Subgroup.card_bot]
    omega
  have hcyc : IsCyclic A := isCyclic_of_prime_card hA
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  set a : G := (g : G) with ha
  have haA : a ∈ A := g.2
  have ha5 : a ^ 5 = 1 := by
    have h := pow_card_eq_one' (x := g)
    rw [hA] at h
    exact congrArg Subtype.val h
  have haR : a ∈ Subgroup.normalizer (R : Set G) := hRA haA
  have haY : a ∈ Subgroup.normalizer (Y : Set G) := hAY haA
  have haZ : a ∈ Subgroup.normalizer ((inSubgroup Subgroup.center R : Subgroup G) : Set G) :=
    mem_normalizer_center haR
  have hnot : ¬ R ≤ Subgroup.centralizer ({a} : Set G) := by
    intro hRc
    have hAc : A ≤ Subgroup.centralizer (R : Set G) := by
      intro x hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨x, hx⟩)
      have hxk : x = a ^ k := by
        have := congrArg Subtype.val hk
        simpa using this.symm
      rw [hxk, Subgroup.mem_centralizer_iff]
      intro r hr
      have hcr : r * a = a * r := Subgroup.mem_centralizer_singleton_iff.1 (hRc hr)
      exact (Commute.zpow_right (show Commute r a from hcr) k).eq
    have hbot : ⁅R, A⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 hAc
    exact hRne (by rw [← hcomm, hbot])
  set C : Subgroup G := R ⊓ Subgroup.centralizer ({a} : Set G) with hC
  have hCmod : 32 ≡ Nat.card C [MOD 5] := by
    have := card_modEq_card_inf_centralizer R haR ha5
    rwa [hR32] at this
  have hCle : C ≤ R := inf_le_left
  have hCcard : Nat.card C = 2 := by
    rcases eq_two_or_thirtytwo (hR32 ▸ Subgroup.card_dvd_of_le hCle) hCmod.symm with h | h
    · exact h
    · exfalso
      have hCR : C = R := Subgroup.eq_of_le_of_card_ge hCle (by rw [h, hR32])
      exact hnot (hCR ▸ inf_le_right)
  have hZC : inSubgroup Subgroup.center R ≤ C := by
    have hZR : inSubgroup Subgroup.center R ≤ R := Subgroup.map_subtype_le _
    have hm := card_modEq_card_inf_centralizer (inSubgroup Subgroup.center R) haZ ha5
    rw [hZcard] at hm
    have hZcen : Nat.card (inSubgroup Subgroup.center R ⊓ Subgroup.centralizer ({a} : Set G) :
        Subgroup G) ∣ 2 := hZcard ▸ Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card (inSubgroup Subgroup.center R ⊓ Subgroup.centralizer ({a} : Set G) :
        Subgroup G) = 2 := by
      obtain ⟨c, hc⟩ : ∃ c, c = Nat.card (inSubgroup Subgroup.center R ⊓
          Subgroup.centralizer ({a} : Set G) : Subgroup G) := ⟨_, rfl⟩
      rw [← hc] at hZcen hm ⊢
      have hle : c ≤ 2 := Nat.le_of_dvd (by norm_num) hZcen
      unfold Nat.ModEq at hm
      interval_cases c <;> omega
    have heq : inSubgroup Subgroup.center R ⊓ Subgroup.centralizer ({a} : Set G) =
        inSubgroup Subgroup.center R :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h2, hZcard])
    intro z hz
    have hz' : z ∈ inSubgroup Subgroup.center R ⊓ Subgroup.centralizer ({a} : Set G) := by
      rw [heq]
      exact hz
    exact ⟨hZR hz, hz'.2⟩
  have hCZ : C = inSubgroup Subgroup.center R :=
    (Subgroup.eq_of_le_of_card_ge hZC (by rw [hCcard, hZcard])).symm
  have hYmod := card_modEq_card_inf_centralizer Y haY ha5
  have hYC : Y ⊓ Subgroup.centralizer ({a} : Set G) = inSubgroup Subgroup.center R := by
    apply le_antisymm
    · rintro y ⟨hyY, hyc⟩
      have : y ∈ C := ⟨hYR hyY, hyc⟩
      exact hCZ ▸ this
    · intro z hz
      exact ⟨hZY hz, (hZC hz).2⟩
  rw [hYC, hZcard] at hYmod
  rcases eq_two_or_thirtytwo (hR32 ▸ Subgroup.card_dvd_of_le hYR) hYmod with h | h
  · left
    exact (Subgroup.eq_of_le_of_card_ge hZY (by rw [h, hZcard])).symm
  · right
    exact Subgroup.eq_of_le_of_card_ge hYR (by rw [h, hR32])

end CFSG.RankThree.PartOne.OddCore37
