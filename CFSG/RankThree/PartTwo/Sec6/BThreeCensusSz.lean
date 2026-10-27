module

public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusTools
import CFSG.RankThree.PartOne.KE.SuzukiFinal
import CFSG.RankThree.PartTwo.KFacts.AutSzOrderThree
import CFSG.CharacterTheory.Burnside
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.FieldAut

public section

namespace CFSG.RankThree.PartTwo.Sec6.BThreeCensus

open CFSG.Blueprint CFSG.LieType.Ree
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut)

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem eq_one_of_mem_inner_of_pow_three (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {β : MulAut (suzukiGroup a K)} (hβ : β ^ 3 = 1)
    (hinn : β ∈ inner (suzukiGroup a K)) : β = 1 := by
  obtain ⟨g, rfl⟩ := hinn
  have hfin : Finite (suzukiGroup a K) := (suzuki_simple ha hK).1
  have hg3 : g ^ 3 = 1 := by
    have h1 : MulAut.conj (g ^ 3) = 1 := by rw [map_pow]; exact hβ
    have h2 : g ^ 3 ∈ Subgroup.center (suzukiGroup a K) := by
      rw [Subgroup.mem_center_iff]
      intro x
      have := congrArg (fun φ : MulAut (suzukiGroup a K) => φ x) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc x * g ^ 3 = g ^ 3 * x * (g ^ 3)⁻¹ * g ^ 3 := by rw [this]
        _ = g ^ 3 * x := by group
    rw [CFSG.RankThree.PartOne.KE.suzuki_center_eq_bot ha hK, Subgroup.mem_bot] at h2
    exact h2
  have hg1 : g = 1 := by
    have h1 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hg3
    have h2 : orderOf g ∣ Nat.card (suzukiGroup a K) := orderOf_dvd_natCard g
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact orderOf_eq_one_iff.mp h
    · exact absurd (h ▸ h2) (KFacts.not_three_dvd_card_suzukiGroup hK)
  rw [hg1, map_one]

theorem isSimpleGroup_or_isSolvable_fixed (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {β : MulAut (suzukiGroup a K)} (hβ : β ^ 3 = 1)
    {C : Subgroup (suzukiGroup a K)} (hC : ∀ z, z ∈ C ↔ β z = z) :
    IsSimpleGroup C ∨ Group.IsSolvable C := by
  obtain ⟨hfin, -, hsimple⟩ := suzuki_simple ha hK
  by_cases hinn : β ∈ inner (suzukiGroup a K)
  · have hβ1 := eq_one_of_mem_inner_of_pow_three ha hK hβ hinn
    have hCtop : C = ⊤ := by
      ext z
      simp [hC z, hβ1]
    left
    exact ((MulEquiv.subgroupCongr hCtop).trans Subgroup.topEquiv).isSimpleGroup
  · have hβo : orderOf β = 3 := orderOf_eq_prime hβ fun h => hinn (h ▸ one_mem _)
    obtain ⟨σ, h, b, k, _, _, -, hbp, hk, hconj, ⟨ef⟩⟩ :=
      CFSG.RankThree.PartOne.KE.suzukiPrimeFieldCosetDescent a ha K hK 3 Nat.prime_three
        (by norm_num) β hβo hinn
    set c : MulAut (suzukiGroup a K) := MulAut.conj h with hc
    set Fix := (szFieldAut a K σ).toMonoidHom.eqLocus (MonoidHom.id _) with hFix
    have hmap : C.map c.toMonoidHom = Fix := by
      ext y
      rw [Subgroup.mem_map]
      have key : ∀ x, β x = x ↔ szFieldAut a K σ (c x) = c x := by
        intro x
        rw [← hconj]
        simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
        exact ⟨fun hx => by rw [hx], fun hx => c.injective hx⟩
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ((key x).mp ((hC x).mp hx))
      · intro hy
        refine ⟨c.symm y, (hC _).mpr ((key _).mpr ?_), by simp⟩
        rw [MulEquiv.apply_symm_apply]
        exact hy
    set eC : C ≃* suzukiGroup b k :=
      ((C.equivMapOfInjective c.toMonoidHom c.injective).trans
        (MulEquiv.subgroupCongr hmap)).trans ef with heC
    rcases Nat.eq_zero_or_pos b with hb0 | hb1
    · right
      subst hb0
      have hcard : Nat.card (suzukiGroup 0 k) = 2 ^ 2 * 5 ^ 1 := by
        rw [suzuki_order hk]
        norm_num
      have : Fintype (suzukiGroup 0 k) := Fintype.ofFinite _
      have hs : Group.IsSolvable (suzukiGroup 0 k) :=
        CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (p := 2) (q := 5)
          (a := 2) (b := 1) Nat.prime_two (by norm_num) (by norm_num)
          (by rw [← Nat.card_eq_fintype_card, hcard])
      exact Group.isSolvable_of_isSolvable_injective (f := eC.toMonoidHom) eC.injective
    · left
      have : IsSimpleGroup (suzukiGroup b k) := (suzuki_simple hb1 hk).2.2
      exact eC.isSimpleGroup

theorem threePrimeB3_suzukiGroup (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) : ThreePrimeB3 (suzukiGroup a K) := by
  intro β hβ C Y R hC hYC hsn hYp _ hRY hRn hRs _
  exact commutator_eq_bot_of_isSimpleGroup_or_isSolvable
    (isSimpleGroup_or_isSolvable_fixed ha hK hβ hC) hYC hsn hYp hRY hRn hRs

theorem threePrimeB3_of_suzukiModel {Q : Type} [Group Q] {p f : ℕ}
    (h : SuzukiModel Q p f) : ThreePrimeB3 Q := by
  obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := h
  exact threePrimeB3_of_mulEquiv e (threePrimeB3_suzukiGroup ha hK)

end CFSG.RankThree.PartTwo.Sec6.BThreeCensus
