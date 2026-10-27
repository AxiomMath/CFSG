module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixNBar
import CFSG.LinearAlgebra.TwoGroupNormalizerGL
import CFSG.Quasithin.Background.F617Bridge
import CFSG.Adapters.LieModelOrders
import CFSG.ClassicalInvolution.Models.UnitaryPairs.RootSU2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixNBar

open Subgroup CFSG.Blueprint CFSG.Open

theorem isPGroup_two_scalars_statedSL_two {K : Type} [Field K] :
    IsPGroup 2 ((StatedScalars (Fin 2) K).subgroupOf (StatedSL 2 K)) := by
  intro g
  have hmem : ((g : StatedSL 2 K) : GL (Fin 2) K) ∈
      (Matrix.GeneralLinearGroup.scalar (Fin 2)).range :=
    Subgroup.mem_subgroupOf.1 g.2
  obtain ⟨c, hc⟩ := hmem
  have hdet : Matrix.GeneralLinearGroup.det ((g : StatedSL 2 K) : GL (Fin 2) K) = 1 :=
    Units.ext (CFSG.Open.StatedAPI.det_of_mem_statedSL (g : StatedSL 2 K).property)
  rw [← hc, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at hdet
  have hg2 : ((g : StatedSL 2 K) : GL (Fin 2) K) ^ 2 = 1 := by
    rw [← hc, ← map_pow, hdet, map_one]
  refine ⟨1, ?_⟩
  rw [pow_one]
  exact Subtype.ext (Subtype.ext (by simpa using hg2))

theorem eq_one_of_mem_scalars_statedSL_three {K : Type} [Field K] [Finite K] {q : ℕ}
    (hK : Nat.card K = q) (hq : q % 3 = 2) {g : StatedSL 3 K}
    (hg : g ∈ (StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K)) : g = 1 := by
  have hmem : (g : GL (Fin 3) K) ∈ (Matrix.GeneralLinearGroup.scalar (Fin 3)).range :=
    Subgroup.mem_subgroupOf.1 hg
  obtain ⟨c, hc⟩ := hmem
  have hdet : Matrix.GeneralLinearGroup.det (g : GL (Fin 3) K) = 1 :=
    Units.ext (CFSG.Open.StatedAPI.det_of_mem_statedSL g.property)
  rw [← hc, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at hdet
  have hcq : c ^ (Nat.card K - 1) = 1 := by
    have h := pow_card_eq_one' (x := c)
    rwa [Nat.card_units] at h
  have hcop : Nat.Coprime 3 (Nat.card K - 1) := by
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 ?_
    rw [hK]
    intro h3
    have hmod : q = 3 * (q / 3) + 2 := by
      have h := Nat.div_add_mod q 3
      omega
    obtain ⟨k, hk⟩ := h3
    omega
  have hc1 : c = 1 := (pow_eq_one_iff_of_coprime hcop).1 ⟨hdet, hcq⟩
  apply Subtype.ext
  show (g : GL (Fin 3) K) = 1
  rw [← hc, hc1, map_one]

theorem eq_one_of_mem_scalars_statedSU_three {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 3 = 1)
    {g : StatedSU 3 (p ^ f) K}
    (hg : g ∈ (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (p ^ f) K)) : g = 1 := by
  have hmem : (g : GL (Fin 3) K) ∈ (Matrix.GeneralLinearGroup.scalar (Fin 3)).range :=
    Subgroup.mem_subgroupOf.1 hg
  obtain ⟨c, hc⟩ := hmem
  have hmemSU : Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ StatedSU 3 (p ^ f) K := by
    rw [hc]
    exact g.property
  obtain ⟨hc3, hcq⟩ :=
    (((CFSG.LinearGroups.unitary_scalar_kernel hp hK (n := 3) (by norm_num)).2.1 c).1 hmemSU)
  have hcop : Nat.Coprime 3 (p ^ f + 1) := by
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 ?_
    intro h3
    have hm : (p ^ f + 1) % 3 = 2 := by
      rw [Nat.add_mod, hq]
    have hmod : p ^ f + 1 = 3 * ((p ^ f + 1) / 3) + 2 := by
      have h := Nat.div_add_mod (p ^ f + 1) 3
      omega
    obtain ⟨k, hk⟩ := h3
    omega
  have hc1 : c = 1 := (pow_eq_one_iff_of_coprime hcop).1 ⟨hc3, hcq⟩
  apply Subtype.ext
  show (g : GL (Fin 3) K) = 1
  rw [← hc, hc1, map_one]

theorem mem_centralizer_of_isPGroup_two_of_quotient {X H K : Type} [Group X] [Group H]
    [Field K] [Finite K] {d r : ℕ} (h2 : (2 : K) ≠ 0) (hd : 2 ≤ d) (hr : r.Prime)
    (hdr : d * d < r) (ι : H →* GL (Fin d) K) (hι : Function.Injective ι)
    {N : Subgroup H} [N.Normal] (hN : IsPGroup 2 N) (e : X ≃* H ⧸ N)
    {a : X} (ha : a ^ r = 1) {Q : Subgroup X} (hQ : IsPGroup 2 Q)
    (haQ : a ∈ normalizer (Q : Set X)) : a ∈ centralizer (Q : Set X) := by
  refine CFSG.LinearAlgebra.TwoGroupNormalizerGL.mem_centralizer_of_isPGroup_two_of_lift
    h2 hd hr hdr ι hι (e.symm.toMonoidHom.comp (QuotientGroup.mk' N)) ?_ ?_ ha hQ haQ
  · exact e.symm.surjective.comp (QuotientGroup.mk'_surjective N)
  · have hker : (e.symm.toMonoidHom.comp (QuotientGroup.mk' N)).ker = N := by simp
    rw [hker]
    exact hN

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem mem_centralizer_of_isPGroup_two_of_lieModel_odd {p f r : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2)
    (hX : LieModel X .PSL 2 p f ∨ (p ^ f % 3 = 2 ∧ LieModel X .PSL 3 p f) ∨
      (p ^ f % 3 = 1 ∧ LieModel X .PSU 3 p f))
    (hr : r.Prime) (h9 : 9 < r) {a : X} (ha : a ^ r = 1) {Q : Subgroup X}
    (hQ : IsPGroup 2 Q) (haQ : a ∈ normalizer (Q : Set X)) :
    a ∈ centralizer (Q : Set X) := by
  have : Fact p.Prime := ⟨hp⟩
  rcases hX with h2 | ⟨hmod, h3⟩ | ⟨hmod, h3⟩
  · have hf : 1 ≤ f := h2.admissible.2.1
    obtain ⟨-, K, hfield, hfinite, hcard, ⟨e⟩⟩ :=
      h2.statedClassicalModel_of_ne_zero (by norm_num : (2 : ℕ) ≠ 0)
    let : Field K := hfield
    let : Finite K := hfinite
    have : CharP K p :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hcard
    have h2K : (2 : K) ≠ 0 := CFSG.ClassicalInvolution.Models.two_ne_zero_of_charP_ne_two hp2
    exact mem_centralizer_of_isPGroup_two_of_quotient h2K (d := 2) (r := r) (by norm_num) hr
      (by omega) (Subgroup.subtype (StatedSL 2 K)) (Subgroup.subtype_injective _)
      (isPGroup_two_scalars_statedSL_two (K := K)) e ha hQ haQ
  · have hf : 1 ≤ f := h3.admissible.2.1
    obtain ⟨-, K, hfield, hfinite, hcard, ⟨e⟩⟩ :=
      h3.statedClassicalModel_of_ne_zero (by norm_num : (3 : ℕ) ≠ 0)
    let : Field K := hfield
    let : Finite K := hfinite
    have : CharP K p :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hcard
    have h2K : (2 : K) ≠ 0 := CFSG.ClassicalInvolution.Models.two_ne_zero_of_charP_ne_two hp2
    have hN : IsPGroup 2 ((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K)) := by
      have hsub : Subsingleton ↥((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K)) := by
        constructor
        intro g g'
        apply Subtype.ext
        rw [eq_one_of_mem_scalars_statedSL_three hcard hmod g.2,
          eq_one_of_mem_scalars_statedSL_three hcard hmod g'.2]
      exact @IsPGroup.of_subsingleton 2 _ _ hsub
    exact mem_centralizer_of_isPGroup_two_of_quotient h2K (d := 3) (r := r) (by norm_num) hr
      (by omega) (Subgroup.subtype (StatedSL 3 K)) (Subgroup.subtype_injective _) hN e ha hQ haQ
  · have hf : 1 ≤ f := h3.admissible.2.1
    obtain ⟨-, K, hfield, hfinite, hcard, ⟨e⟩⟩ :=
      h3.statedClassicalModel_of_ne_zero (by norm_num : (3 : ℕ) ≠ 0)
    let : Field K := hfield
    let : Finite K := hfinite
    have hcard' : Nat.card K = p ^ (2 * f) := by
      rw [hcard, ← pow_mul, Nat.mul_comm]
    have : CharP K p :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
        (by omega) hcard'
    have h2K : (2 : K) ≠ 0 := CFSG.ClassicalInvolution.Models.two_ne_zero_of_charP_ne_two hp2
    have hN : IsPGroup 2 ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (p ^ f) K)) := by
      have hsub : Subsingleton ↥((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (p ^ f) K)) := by
        constructor
        intro g g'
        apply Subtype.ext
        rw [eq_one_of_mem_scalars_statedSU_three hp hcard hmod g.2,
          eq_one_of_mem_scalars_statedSU_three hp hcard hmod g'.2]
      exact @IsPGroup.of_subsingleton 2 _ _ hsub
    exact mem_centralizer_of_isPGroup_two_of_quotient h2K (d := 3) (r := r) (by norm_num) hr
      (by omega) (Subgroup.subtype (StatedSU 3 (p ^ f) K)) (Subgroup.subtype_injective _)
      hN e ha hQ haQ

omit [Finite X] in
theorem barTwo_of_lieModel_odd [IsSimpleGroup X] {p f r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hX : LieModel X .PSL 2 p f ∨ (p ^ f % 3 = 2 ∧ LieModel X .PSL 3 p f) ∨
      (p ^ f % 3 = 1 ∧ LieModel X .PSU 3 p f))
    (hr : r.Prime) (h11 : 11 ≤ r) {A : Subgroup X} (hA : Nat.card A = r) : BarTwo A := by
  have hr9 : 9 < r := by omega
  refine ⟨inferInstance, ?_, ?_⟩
  · rcases hX with h2 | ⟨-, h3⟩ | ⟨-, h3⟩
    · left
      have hf : 1 ≤ f := h2.admissible.2.1
      refine ⟨p, f, hp, hp2, ?_, CFSG.Quasithin.F617.isL2_of_lieModel_PSL_two h2⟩
      by_contra hle
      have hle' : p ^ f ≤ 5 := by omega
      have hpge : 3 ≤ p := by have := hp.two_le; omega
      have hcases : p ^ f = 3 ∨ p ^ f = 5 := by
        rcases Nat.lt_or_ge f 2 with hflt | hfge
        · have hfeq : f = 1 := by omega
          have hple : p ≤ 5 := by simpa [hfeq] using hle'
          interval_cases p
          · exact Or.inl (by simp [hfeq])
          · norm_num at hp
          · exact Or.inr (by simp [hfeq])
        · exfalso
          have h9' : 9 ≤ p ^ f := by
            calc (9 : ℕ) = 3 ^ 2 := by norm_num
              _ ≤ p ^ 2 := pow_le_pow_left' hpge 2
              _ ≤ p ^ f := pow_le_pow_right' (by omega : 1 ≤ p) hfge
          omega
      have hcardX : Nat.card X = 12 ∨ Nat.card X = 60 := by
        have hc := h2.card_eq_lieOrd (by norm_num : (2 : ℕ) ≠ 0)
        rcases hcases with h | h
        · left
          rw [hc, h]
          decide
        · right
          rw [hc, h]
          decide
      have hrvd : r ∣ Nat.card X := by
        have h := Subgroup.card_dvd_of_le (le_top : A ≤ (⊤ : Subgroup X))
        rwa [Subgroup.card_top, hA] at h
      rcases hcardX with hX12 | hX60
      · have hr12 : r ∣ 12 := hX12 ▸ hrvd
        have hdvd : r ∣ 2 ^ 2 * 3 := by
          simpa [show (12 : ℕ) = 2 ^ 2 * 3 by norm_num] using hr12
        rcases hr.dvd_mul.1 hdvd with h | h3
        · have h2' : r ∣ 2 := hr.dvd_of_dvd_pow h
          have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h2'
          omega
        · have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h3
          omega
      · have hr60 : r ∣ 60 := hX60 ▸ hrvd
        have hdvd : r ∣ 2 ^ 2 * 3 * 5 := by
          simpa [show (60 : ℕ) = 2 ^ 2 * 3 * 5 by norm_num] using hr60
        rcases hr.dvd_mul.1 hdvd with h | h5
        · rcases hr.dvd_mul.1 h with h | h3
          · have h2' : r ∣ 2 := hr.dvd_of_dvd_pow h
            have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h2'
            omega
          · have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h3
            omega
        · have := (Nat.prime_dvd_prime_iff_eq hr (by norm_num : Nat.Prime 5)).1 h5
          omega
    · exact Or.inr ⟨p, f, hp, hp2, Or.inl h3⟩
    · exact Or.inr ⟨p, f, hp, hp2, Or.inr h3⟩
  · intro Q hQ hAQ
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    have har : a ^ r = 1 := by
      have h1 : orderOf a ∣ Nat.card ↥A := Subgroup.orderOf_dvd_natCard A ha
      rw [hA] at h1
      exact (orderOf_dvd_iff_pow_eq_one).1 h1
    exact mem_centralizer_of_isPGroup_two_of_lieModel_odd hp hp2 hX hr hr9 har hQ (hAQ ha)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixNBar
