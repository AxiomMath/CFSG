module

public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RankOneAutomorphisms

public section

namespace CFSG.RankThree.GroupTheory

open CFSG.OrderReductions.FrattiniAutomorphisms

theorem card_frattini_quotient_le_four_of_pRank_le_one {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) (hrank : pRank 2 P ≤ 1) : Nat.card (P ⧸ frattini P) ≤ 4 := by
  rcases (CFSG.LocalAnalysis.ComponentInitial.pgroup_rank_one_classification Nat.prime_two
    hP).mp hrank with hcyc | ⟨-, n, -, ⟨e⟩⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Fact (IsPGroup 2 P) := ⟨hP⟩
    have : IsCyclic (P ⧸ frattini P) :=
      isCyclic_of_surjective (QuotientGroup.mk' (frattini P)) (QuotientGroup.mk'_surjective _)
    have hexp : Monoid.exponent (P ⧸ frattini P) ∣ 2 := by
      apply Monoid.exponent_dvd_of_forall_pow_eq_one
      intro x
      induction x using QuotientGroup.induction_on with
      | H y =>
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
        exact CFSG.pth_power_mem_frattini_of_isPGroup y
    rw [← IsCyclic.exponent_eq_card]
    exact (Nat.le_of_dvd (by decide) hexp).trans (by decide)
  · let φ : QuaternionGroup (2 ^ (n - 2)) →* P := e.symm.toMonoidHom
    have hφ : Function.Surjective φ := e.symm.surjective
    let ψ := (QuotientGroup.mk' (frattini P)).comp φ
    have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hφ
    have hker : frattini (QuaternionGroup (2 ^ (n - 2))) ≤ ψ.ker := by
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
      exact frattini_le_comap_frattini_of_surjective hφ
    exact (Nat.card_le_card_of_surjective _
      (QuotientGroup.lift_surjective_of_surjective _ ψ hψ hker)).trans
      (CFSG.ProperTwoGeneratedCore.quaternion_frattini_quotient_card_le_four (n - 2))

theorem eq_two_or_eq_three_of_prime_dvd_24 {q : ℕ} (hq : q.Prime) (h : q ∣ 24) :
    q = 2 ∨ q = 3 := by
  have h' : q ≤ 24 := Nat.le_of_dvd (by norm_num) h
  interval_cases q <;> simp_all (config := { decide := true })

theorem prime_dvd_card_mulAut_of_pRank_le_one {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) (hrank : pRank 2 P ≤ 1) {q : ℕ} (hq : q.Prime)
    (hdvd : q ∣ Nat.card (MulAut P)) : q = 2 ∨ q = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := quotientAutomorphism (frattini P)
  have hker : IsPGroup 2 φ.ker := (CFSG.GroupTheory.frattini_automorphism_kernel hP).2
  have hcard : Nat.card (MulAut P) = Nat.card φ.ker * Nat.card φ.range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hinj : Function.Injective (MulAut.toPerm (P ⧸ frattini P)) := fun σ τ h =>
    MulEquiv.ext fun x => congrArg (fun f : Equiv.Perm (P ⧸ frattini P) => f x) h
  have hrange : Nat.card φ.range ∣ 24 := by
    refine (Subgroup.card_subgroup_dvd_card _).trans
      ((Subgroup.card_dvd_of_injective _ hinj).trans ?_)
    rw [Nat.card_perm]
    exact Nat.factorial_dvd_factorial (card_frattini_quotient_le_four_of_pRank_le_one hP hrank)
  rw [hcard] at hdvd
  rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | h
  · obtain ⟨k, hk⟩ := hker.exists_card_eq
    rw [hk] at h
    exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h))
  · exact eq_two_or_eq_three_of_prime_dvd_24 hq (h.trans hrange)

theorem two_le_pRank_of_nontrivial_action {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {A R : Type*}
    [Group A] [Group R] [Finite A] [Finite R] [MulDistribMulAction A R] (hA : IsPGroup p A)
    (hR : IsPGroup 2 R) (hnontriv : ∃ a : A, ∃ x : R, a • x ≠ x) : 2 ≤ pRank 2 R := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hlt
  obtain ⟨a, x, hax⟩ := hnontriv
  set σ := MulDistribMulAction.toMulAut A R a
  have hσ : σ ≠ 1 := fun h => hax (by
    have := congrArg (fun τ : MulAut R => τ x) h
    exact this)
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hA a
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (hk ▸ orderOf_map_dvd _ a : orderOf σ ∣ p ^ k)
  rcases j with _ | j
  · exact hσ (orderOf_eq_one_iff.mp (by rw [hj, pow_zero]))
  · have hpdvd : p ∣ Nat.card (MulAut R) :=
      (hj ▸ dvd_pow_self p j.succ_ne_zero : p ∣ orderOf σ).trans (orderOf_dvd_natCard σ)
    rcases prime_dvd_card_mulAut_of_pRank_le_one hR (by omega) hp hpdvd with h | h <;> omega

theorem rank_one_two_group_automorphism_prime_support :
    (∀ (P : Type*) [Group P] [Finite P], IsPGroup 2 P → pRank 2 P ≤ 1 →
      ∀ q : ℕ, q.Prime → q ∣ Nat.card (MulAut P) → q = 2 ∨ q = 3) ∧
    ∀ (p : ℕ) (A R : Type*) [Group A] [Group R] [Finite A] [Finite R]
      [MulDistribMulAction A R], p.Prime → 3 < p → IsPGroup p A → IsPGroup 2 R →
      (∃ a : A, ∃ x : R, a • x ≠ x) → 2 ≤ pRank 2 R :=
  ⟨fun _ _ _ hP hrank _ hq hdvd => prime_dvd_card_mulAut_of_pRank_le_one hP hrank hq hdvd,
    fun _ _ _ _ _ _ _ _ hp hp3 hA hR hnontriv =>
      two_le_pRank_of_nontrivial_action hp hp3 hA hR hnontriv⟩

end CFSG.RankThree.GroupTheory
