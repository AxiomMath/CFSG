module

public import CFSG.Foundations.Basic
public import CFSG.Assembly.OrderReductions.RegularCore

public section

namespace CFSG.ShultStronglyClosedTI

variable {G : Type*} [Group G]

theorem primeComplementGrowth_mem_normalizer_of_conjugate_eq
    (V : Subgroup G) (z : G) (hVz : conjugate V z = V) :
    z ∈ Subgroup.normalizer (V : Set G) := by
  have hinv : z⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hVz
  exact inv_inv z ▸ (Subgroup.normalizer (V : Set G)).inv_mem hinv

theorem primeComplementGrowth_normalizer_action_involutive
    (V : Subgroup G) (z : G) (hz : orderOf z = 2)
    (hnorm : z ∈ Subgroup.normalizer (V : Set G)) :
    Function.Involutive (V.normalizerMonoidHom ⟨z, hnorm⟩) := by
  intro v
  apply Subtype.ext
  simp only [Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hzsq : z * z = 1 := by
    simpa only [hz, pow_two] using pow_orderOf_eq_one z
  rw [inv_eq_self_of_orderOf_eq_two hz]
  calc
    z * (z * (v : G) * z) * z = (z * z) * (v : G) * (z * z) := by group
    _ = (v : G) := by rw [hzsq, one_mul, mul_one]

variable [Finite G]

theorem primeComplementGrowth_prime_part_spec (p : ℕ) [Fact p.Prime]
    (n : ℕ) (hn : n ≠ 0) :
    CFSG.OrderReductions.PrimePart.primePart p n ∣ n ∧
      ∀ k : ℕ, p ^ k ∣ n →
        p ^ k ≤ CFSG.OrderReductions.PrimePart.primePart p n := by
  have hp : p.Prime := Fact.out
  refine ⟨(hp.pow_dvd_iff_le_factorization hn).mpr le_rfl, ?_⟩
  intro k hk
  exact Nat.pow_le_pow_right hp.pos ((hp.pow_dvd_iff_le_factorization hn).mp hk)

theorem primeComplementGrowth_exists_invariant_sylow
    (p : ℕ) [Fact p.Prime] (V J : Subgroup G) (hVJ : V ≤ J)
    (hJodd : Odd (Nat.card J)) (z : G) (hz : orderOf z = 2)
    (hVz : conjugate V z = V)
    (hpart : CFSG.OrderReductions.PrimePart.primePart p (Nat.card V) =
      CFSG.OrderReductions.PrimePart.primePart p (Nat.card J)) :
    ∃ P : Sylow p J,
      (P : Subgroup J).map J.subtype ≤ V ∧
      z ∈ Subgroup.normalizer ((P : Subgroup J).map J.subtype : Set G) := by
  have hnorm := primeComplementGrowth_mem_normalizer_of_conjugate_eq V z hVz
  have hVodd : Odd (Nat.card V) := hJodd.of_dvd_nat (Subgroup.card_dvd_of_le hVJ)
  obtain ⟨PV, hPV⟩ :=
    CFSG.OrderReductions.InvariantSylow.exists_invariant_sylow_of_odd p hVodd
      (V.normalizerMonoidHom ⟨z, hnorm⟩)
      (primeComplementGrowth_normalizer_action_involutive V z hz hnorm)
  let H : Subgroup G := (PV : Subgroup V).map V.subtype
  have hHV : H ≤ V := Subgroup.map_subtype_le _
  have hcard : Nat.card H =
      CFSG.OrderReductions.PrimePart.primePart p (Nat.card J) :=
    (CFSG.OrderReductions.PrimePart.sylow_map_card_eq_primePart p V PV).trans hpart
  obtain ⟨P, hP⟩ := CFSG.OrderReductions.PrimePart.exists_sylow_image_of_card
    p H J (hHV.trans hVJ) hcard
  refine ⟨P, hP ▸ hHV, ?_⟩
  rw [hP]
  exact CFSG.OrderReductions.TwoPointSylow.normalizes_image_of_invariant V z hnorm
    (PV : Subgroup V) hPV

omit [Finite G] in
theorem primeComplementGrowth_normalizer_le_characteristic_image_normalizer
    (J : Subgroup G) (A : Subgroup J) [A.Characteristic] :
    Subgroup.normalizer (J : Set G) ≤
      Subgroup.normalizer (A.map J.subtype : Set G) := by
  intro g hg
  exact CFSG.OrderReductions.RegularCore.characteristic_pair_image_normalizes J A g hg

omit [Finite G] in
theorem primeComplementGrowth_normal_of_normalizer_generation
    (J A : Subgroup G) (z : G)
    (hgen : Subgroup.closure ((Subgroup.normalizer (J : Set G) : Set G) ∪ {z}) = ⊤)
    (hnorm : Subgroup.normalizer (J : Set G) ≤ Subgroup.normalizer (A : Set G))
    (hz : z ∈ Subgroup.normalizer (A : Set G)) : A.Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  rw [← hgen]
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases hg with hg | hg
  · exact hnorm hg
  · rw [Set.mem_singleton_iff] at hg
    exact hg ▸ hz

end CFSG.ShultStronglyClosedTI
