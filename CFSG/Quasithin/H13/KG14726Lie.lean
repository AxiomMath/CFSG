module

public import CFSG.Quasithin.H13.KG14726Core
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinear

public noncomputable section

namespace CFSG.Quasithin.H13.KG14726

open Subgroup

section Forms

variable {Y : Type*} [Group Y]

theorem ConstrainedAt.of_isCharacteristicP [Finite Y] {z : Y}
    (h : CFSG.IsCharacteristicP 2 (centralizer ({z} : Set Y))) : ConstrainedAt z := by
  set C : Subgroup Y := centralizer ({z} : Set Y) with hCdef
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨(CFSG.pCore 2 C).map C.subtype, CFSG.pCore_isPGroup.map _, map_subtype_le _, ?_, ?_⟩
  · intro c hc q hq
    obtain ⟨q', hq', rfl⟩ := hq
    exact ⟨⟨c, hc⟩ * q' * ⟨c, hc⟩⁻¹, (CFSG.pCore_normal (p := 2) (G := C)).conj_mem _ hq' _,
      rfl⟩
  · intro c hc hcQ
    have hmem : (⟨c, hc⟩ : C) ∈ centralizer ((CFSG.pCore 2 C : Subgroup C) : Set C) := by
      rw [mem_centralizer_iff]
      intro q hq
      exact Subtype.ext (hcQ q ⟨q, hq, rfl⟩).symm
    exact ⟨⟨c, hc⟩, h hmem, rfl⟩

end Forms

section Linear

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OutcomeLocal CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.UnbalancedCatalog.EvenLinearSL

theorem involutionConstrained_projectiveSL {f n : ℕ} (hf : 1 ≤ f) (hn : 2 ≤ n)
    {k : Type*} [Field k] (hk : Nat.card k = 2 ^ f) :
    InvolutionConstrained (projectiveSL n k) := by
  classical
  intro t ht
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : CharP k 2 := finite_field_prime_power_characteristic Nat.prime_two hf hk
  have : NeZero n := ⟨by omega⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (SpecialLinearGroup (Fin n) k) := inferInstance
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨s, rfl, hs⟩ := exists_sl_lift t htt
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at ht
    exact absurd ht (by norm_num)
  set U := flagKernel (dispRange s) (dispKer s) (dispRange_le_dispKer hs) with hUdef
  set Q := U.map (proj n k) with hQdef
  have hlift : ∀ c ∈ centralizer ({proj n k s} : Set (projectiveSL n k)),
      ∃ A : SpecialLinearGroup (Fin n) k, proj n k A = c ∧ A * s = s * A := by
    intro c hc
    obtain ⟨A, rfl⟩ := proj_surjective n k c
    exact ⟨A, rfl, commute_of_proj_commute hs (mem_centralizer_singleton_iff.mp hc)⟩
  have hQC : Q ≤ centralizer ({proj n k s} : Set (projectiveSL n k)) := by
    rintro _ ⟨u, hu, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, commute_of_mem_flagKernel hs hu]
  have hQp : IsPGroup 2 Q := isPGroup_flagKernel.map (proj n k)
  have hnorm : ∀ c ∈ centralizer ({proj n k s} : Set (projectiveSL n k)), ∀ q ∈ Q,
      c * q * c⁻¹ ∈ Q := by
    intro c hc q hq
    obtain ⟨A, rfl, hAs⟩ := hlift c hc
    obtain ⟨u, hu, rfl⟩ := hq
    exact ⟨A * u * A⁻¹, conj_mem_flagKernel hs hAs hu, by rw [map_mul, map_mul, map_inv]⟩
  refine ⟨Q, hQp, hQC, hnorm, fun c hc hcQ => ?_⟩
  obtain ⟨A, rfl, hAs⟩ := hlift c hc
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · obtain rfl : n = 2 := by omega
    exact ⟨A, mem_flagKernel_of_commute_two hs hs1 hAs, rfl⟩
  · exact mem_map_flagKernel_of_commute hn3 hf hk (dispRange_ne_bot hs1)
      (dispRange_le_dispKer hs) (dispKer_ne_top hs1)
      fun u hu => hcQ _ ⟨u, hu, rfl⟩

theorem scalars_two_eq_bot {F : Type*} [Field F] [CharP F 2] : scalars 2 F = ⊥ := by
  rw [scalars_eq_center]
  ext g
  rw [mem_bot, Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, hr, hg⟩
    have hr2 : r ^ 2 = 1 := by simpa using hr
    have h : (r + 1) ^ 2 = 0 := by
      rw [CharTwo.add_sq, hr2, one_pow, CharTwo.add_self_eq_zero]
    have h1 : r + 1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp h
    have hr1 : r = 1 := by
      calc r = -1 := eq_neg_of_add_eq_zero_left h1
        _ = 1 := CharTwo.neg_eq 1
    subst hr1
    apply Subtype.ext
    rw [← hg]
    simp
  · rintro rfl
    exact ⟨1, by simp, by simp⟩

end Linear

end CFSG.Quasithin.H13.KG14726

end
