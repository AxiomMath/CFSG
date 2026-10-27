module

public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
import CFSG.RankThree.PartTwo.KFacts.KS14MultCore
import CFSG.RankThree.PartOne.MultRes.ON
import CFSG.Sporadic.ON.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec14.HJRes148

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank

theorem isPGroup_two_of_central {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]
    {Z : Subgroup K} [Z.Normal] (hZc : Z ≤ Subgroup.center K)
    (h : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card Z → ¬ p ^ 2 ∣ Nat.card (K ⧸ Z)) :
    IsPGroup 2 Z := by
  refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd
    (Nat.card_pos (α := Z)).ne' fun {q} hq hqd => ?_)
  by_contra hq2
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨⟨z, hzZ⟩, hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) q hqd
  have hzo : orderOf z = q := by
    rw [← hz, Subgroup.orderOf_mk]
  have hZ'c : Subgroup.zpowers z ≤ Subgroup.center K := Subgroup.zpowers_le.mpr (hZc hzZ)
  have : (Subgroup.zpowers z).Normal := Subgroup.normal_of_le_center hZ'c
  have hZ' : Subgroup.zpowers z = ⊥ :=
    KFacts.KS14.eq_bot_of_isPerfect_of_sylow_comm hZ'c fun p hp hpZ' P => by
      have hpq : p = q := by
        rw [Nat.card_zpowers, hzo] at hpZ'
        exact (Nat.prime_dvd_prime_iff_eq hp hq).mp hpZ'
      subst hpq
      exact KFacts.KS14.sylow_comm_of_not_sq_dvd hZc (h p hp hq2 hqd) P
  have hz1 : z = 1 := by
    have : z ∈ Subgroup.zpowers z := Subgroup.mem_zpowers z
    rwa [hZ', Subgroup.mem_bot] at this
  rw [hz1, orderOf_one] at hzo
  exact hq.one_lt.ne hzo

theorem pCore_two_eq_theta {K : Type*} [Group K] [Finite K]
    (h2 : IsPGroup 2 (aschbacherSolvableCore 3 K)) :
    CFSG.pCore 2 K = aschbacherSolvableCore 3 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hθc, -, hmax, -⟩ :=
    solvable_prime_complement_core_characterization (H := K) Nat.prime_three
  have hθn : (aschbacherSolvableCore 3 K).Normal := Subgroup.normal_of_characteristic _
  refine le_antisymm ?_ (le_sSup ⟨hθn, h2⟩)
  have hp : IsPGroup 2 (CFSG.pCore 2 K) := CFSG.pCore_isPGroup
  refine hmax _ CFSG.pCore_normal ?_ ?_
  · have : Group.IsNilpotent (CFSG.pCore 2 K) := hp.isNilpotent
    infer_instance
  · intro h3
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    rw [hk] at h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega

theorem not_sq_dvd_sixty {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ^ 2 ∣ 60 := by
  intro hd
  have hle : p ^ 2 ≤ 60 := Nat.le_of_dvd (by norm_num) hd
  have hp8 : p < 8 := by
    by_contra h
    have : 8 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left (not_lt.mp h) 2
    omega
  interval_cases p <;> revert hp hp2 hd <;> norm_num

theorem a5Type_of_central {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]
    (hθc : aschbacherSolvableCore 3 K ≤ Subgroup.center K)
    (hA5 : Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* alternatingGroup (Fin 5))) :
    IsQuasisimple K ∧ Nonempty (K ⧸ CFSG.pCore 2 K ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨φ⟩ := hA5
  set θ := aschbacherSolvableCore 3 K with hθ
  have hθn : θ.Normal := Subgroup.normal_of_le_center hθc
  have hcard : Nat.card (K ⧸ θ) = 60 := by
    rw [Nat.card_congr φ.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  have h2 : IsPGroup 2 θ := isPGroup_two_of_central hθc fun p hp hp2 _ => by
    rw [hcard]
    exact not_sq_dvd_sixty hp hp2
  have hO2 := pCore_two_eq_theta h2
  refine ⟨?_, ⟨(QuotientGroup.quotientMulEquivOfEq hO2).trans φ⟩⟩
  have hA5q : IsQuasisimple (alternatingGroup (Fin 5)) := by
    have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    refine (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup ?_).1
    refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
      ⟨Equiv.swap 1 2 * Equiv.swap 2 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
      fun h => ?_⟩
    have := congrArg Subtype.val h
    revert this
    decide
  have hq : IsQuasisimple (K ⧸ θ) := CFSG.LocalCores.isQuasisimple_of_mulEquiv φ.symm hA5q
  exact (CFSG.LocalCores.isQuasisimple_iff_of_surjective inferInstance (QuotientGroup.mk' θ)
    (QuotientGroup.mk'_surjective θ) (by rwa [QuotientGroup.ker_mk'])).mpr hq

theorem not_sq_dvd_card_ON {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hp7 : p ≠ 7) :
    ¬ p ^ 2 ∣ 460815505920 := by
  intro hd
  have hpN : p ∣ 460815505920 := (dvd_pow_self p two_ne_zero).trans hd
  by_cases h5 : p = 5
  · subst h5; norm_num at hd
  by_cases h11 : p = 11
  · subst h11; norm_num at hd
  by_cases h19 : p = 19
  · subst h19; norm_num at hd
  by_cases h31 : p = 31
  · subst h31; norm_num at hd
  have hc : ∀ q : ℕ, q.Prime → q ≠ p → Nat.Coprime p q := fun q hq hqp =>
    (Nat.coprime_primes hp hq).mpr (Ne.symm hqp)
  have hcop : Nat.Coprime p (2 ^ 9 * 3 ^ 4 * 5 * 7 ^ 3 * 11 * 19 * 31) := by
    refine Nat.Coprime.mul_right (Nat.Coprime.mul_right (Nat.Coprime.mul_right
      (Nat.Coprime.mul_right (Nat.Coprime.mul_right (Nat.Coprime.mul_right ?_ ?_) ?_) ?_) ?_) ?_)
      ?_
    · exact Nat.Coprime.pow_right _ (hc 2 Nat.prime_two (by omega))
    · exact Nat.Coprime.pow_right _ (hc 3 Nat.prime_three (by omega))
    · exact hc 5 (by norm_num) (Ne.symm h5)
    · exact Nat.Coprime.pow_right _ (hc 7 (by norm_num) (Ne.symm hp7))
    · exact hc 11 (by norm_num) (Ne.symm h11)
    · exact hc 19 (by norm_num) (Ne.symm h19)
    · exact hc 31 (by norm_num) (Ne.symm h31)
  have h1 := Nat.Coprime.eq_one_of_dvd hcop (by norm_num at hpN ⊢; exact hpN)
  exact hp.one_lt.ne' h1

theorem not_dvd_card_center_of_ON
    {K : Type} [Group K] [Finite K] [Group.IsPerfect K]
    (e : K ⧸ Subgroup.center K ≃* CFSG.Blueprint.NativeSporadic.ON) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) : ¬ p ∣ Nat.card (Subgroup.center K) := by
  intro hpZ
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨N, hNn, π, hperf, -, hsurj, hker, hpg, hne⟩ :=
    CFSG.RankThree.PartOne.Mult.exists_central_p_extension (K := K) hpZ
  have : Group.IsPerfect (K ⧸ N) := hperf
  apply hne
  by_cases hp7 : p = 7
  · subst hp7
    exact CFSG.RankThree.PartOne.MultRes.sporadicKernelTrivial_on_seven (K ⧸ N)
      (K ⧸ Subgroup.center K) π ⟨e⟩ hsurj hker hpg
  · have hcardQ : Nat.card ((K ⧸ N) ⧸ π.ker) = 460815505920 := by
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hsurj).toEquiv,
        Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.ON.card_ON_eq
    refine KFacts.KS14.eq_bot_of_isPerfect_of_not_sq_dvd hker fun q hq hqk => ?_
    have hqp : q = p := by
      obtain ⟨k, hk⟩ := hpg.exists_card_eq
      rw [hk] at hqk
      exact (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hqk)
    subst hqp
    rw [hcardQ]
    exact not_sq_dvd_card_ON hq hp3 hp7

theorem onType_of_central
    {K : Type} [Group K] [Finite K] [Group.IsPerfect K]
    (hθc : aschbacherSolvableCore 3 K ≤ Subgroup.center K)
    (hON : Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) CFSG.Blueprint.NativeSporadic.ON) :
    IsQuasisimple K ∧ Sec4.IsTripleCover (K ⧸ CFSG.pCore 2 K) CFSG.Blueprint.NativeSporadic.ON := by
  set θ := aschbacherSolvableCore 3 K with hθ
  have hθn : θ.Normal := Subgroup.normal_of_le_center hθc
  obtain ⟨hZ3, ⟨eT⟩⟩ := hON
  have hONs : IsSimpleGroup CFSG.Blueprint.NativeSporadic.ON := CFSG.Sporadic.ON.isSimpleGroup_ON
  have hTp : Group.IsPerfect (K ⧸ θ) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective θ)
  have hTs : IsSimpleGroup ((K ⧸ θ) ⧸ Subgroup.center (K ⧸ θ)) := eT.isSimpleGroup
  have hnc : ∃ a b : (K ⧸ θ) ⧸ Subgroup.center (K ⧸ θ), a * b ≠ b * a := by
    by_contra hcomm
    push Not at hcomm
    have : IsMulCommutative CFSG.Blueprint.NativeSporadic.ON :=
      ⟨⟨fun a b => by simpa using congrArg eT (hcomm (eT.symm a) (eT.symm b))⟩⟩
    have hprime := Group.is_simple_iff_prime_card.mp hONs
    rw [CFSG.Sporadic.ON.card_ON_eq] at hprime
    norm_num at hprime
  have hTq : IsQuasisimple (K ⧸ θ) := ⟨hTp, hTs, hnc⟩
  have hKq : IsQuasisimple K :=
    (CFSG.LocalCores.isQuasisimple_iff_of_surjective inferInstance (QuotientGroup.mk' θ)
      (QuotientGroup.mk'_surjective θ) (by rwa [QuotientGroup.ker_mk'])).mpr hTq
  have hc := (CFSG.LocalCores.quasisimple_central_quotient hKq θ hθc).2.2
  let eK : K ⧸ Subgroup.center K ≃* CFSG.Blueprint.NativeSporadic.ON :=
    ((QuotientGroup.quotientQuotientEquivQuotient θ (Subgroup.center K) hθc).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hc).symm).trans eT
  obtain ⟨-, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := K) Nat.prime_three
  have h2 : IsPGroup 2 θ := by
    refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd
      (Nat.card_pos (α := θ)).ne' fun {q} hq hqd => ?_)
    have hqZ : q ∣ Nat.card (Subgroup.center K) := hqd.trans (Subgroup.card_dvd_of_le hθc)
    have hq3 : q ≠ 3 := by
      rintro rfl
      exact hθ3 hqd
    by_contra hq2
    have hq4 : 3 < q := by
      have := hq.two_le
      omega
    exact not_dvd_card_center_of_ON eK hq hq4 hqZ
  have hO2 := pCore_two_eq_theta h2
  refine ⟨hKq, ?_⟩
  have e2 : K ⧸ CFSG.pCore 2 K ≃* K ⧸ θ := QuotientGroup.quotientMulEquivOfEq hO2
  obtain ⟨hcard', ⟨eT'⟩⟩ : Sec4.IsTripleCover (K ⧸ θ) CFSG.Blueprint.NativeSporadic.ON :=
    ⟨hZ3, ⟨eT⟩⟩
  have hcen : (Subgroup.center (K ⧸ CFSG.pCore 2 K)).map e2.toMonoidHom =
      Subgroup.center (K ⧸ θ) := Subgroup.map_center_eq e2
  refine ⟨?_, ⟨(QuotientGroup.congr _ _ e2 hcen).trans eT'⟩⟩
  rw [← hcard', ← hcen, Subgroup.card_map_of_injective e2.injective]

end CFSG.RankThree.PartTwo.Sec14.HJRes148
