module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.HopfPrimaryBridge
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeSporAlt

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster

open CFSG.RankThree.PerfectCover CFSG.AGLEmbedding

section Iff

variable {X : Type} [Group X] [Finite X] [Group.IsPerfect X] {p : ℕ} [Fact p.Prime]

omit [Group.IsPerfect X] in
theorem kernelTrivialAt_of_not_dvd_card_hopfMultiplier
    (h : ¬ p ∣ Nat.card (hopfMultiplier X)) : KernelTrivialAt X p := by
  intro E _ _ _ π hπ hC hp
  have hd := card_ker_dvd_card_hopfMultiplier π hπ hC
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exact Subgroup.eq_bot_of_card_eq _ (by rw [hk, pow_zero])
  · exact absurd ((dvd_pow_self p hk0.ne').trans (hk ▸ hd)) h

theorem not_dvd_card_hopfMultiplier_of_kernelTrivialAt (h : KernelTrivialAt X p) :
    ¬ p ∣ Nat.card (hopfMultiplier X) := by
  intro hd
  have := finite_hopfMultiplier (inferInstance : Group.IsPerfect X)
  have hM : Nat.card (hopfMultiplier X) ≠ 0 := Nat.card_pos.ne'
  obtain ⟨E, _, _, _, π, hπ, hC, hp, hcard⟩ :=
    exists_perfect_central_pCover_card_ker_eq_primary_part (X := X) p
  have hv : 1 ≤ (Nat.card (hopfMultiplier X)).factorization p :=
    (Nat.Prime.dvd_iff_one_le_factorization Fact.out hM).1 hd
  have hbot := h E π hπ hC hp
  rw [hbot, Subgroup.card_bot] at hcard
  have : 1 < p ^ (Nat.card (hopfMultiplier X)).factorization p :=
    Nat.one_lt_pow (by omega) (Fact.out : p.Prime).one_lt
  omega

theorem kernelTrivialAt_iff_not_dvd_card_hopfMultiplier :
    KernelTrivialAt X p ↔ ¬ p ∣ Nat.card (hopfMultiplier X) :=
  ⟨not_dvd_card_hopfMultiplier_of_kernelTrivialAt, kernelTrivialAt_of_not_dvd_card_hopfMultiplier⟩

end Iff

section Transport

theorem primaryCentralKernelOrder_of_mulEquiv {X Y : Type} [Group X] [Group Y] (f : X ≃* Y)
    {p k : ℕ} (h : PrimaryCentralKernelOrder Y p k) : PrimaryCentralKernelOrder X p k := by
  have hk : ∀ {E : Type} [Group E] (π : E →* X), (f.toMonoidHom.comp π).ker = π.ker :=
    fun π => MonoidHom.ker_comp_of_injective π f.toMonoidHom f.injective
  obtain ⟨hup, E, _, _, _, π, hπ, hC, hp, hcard⟩ := h
  refine ⟨fun E' _ _ _ π' hπ' hC' hp' => ?_, E, inferInstance, inferInstance, inferInstance,
    f.symm.toMonoidHom.comp π, ?_, ?_, ?_, ?_⟩
  · have := hup E' (f.toMonoidHom.comp π') (f.surjective.comp hπ') (by rw [hk]; exact hC')
      (by rw [hk]; exact hp')
    rwa [hk] at this
  · exact f.symm.surjective.comp hπ
  · rw [MonoidHom.ker_comp_of_injective π f.symm.toMonoidHom f.symm.injective]; exact hC
  · rw [MonoidHom.ker_comp_of_injective π f.symm.toMonoidHom f.symm.injective]; exact hp
  · rw [MonoidHom.ker_comp_of_injective π f.symm.toMonoidHom f.symm.injective]; exact hcard

theorem card_hopfMultiplier_congr {X Y : Type} [Group X] [Group Y] [Finite X]
    [Group.IsPerfect X] (f : X ≃* Y) :
    Nat.card (hopfMultiplier X) = Nat.card (hopfMultiplier Y) := by
  have : Finite Y := Finite.of_equiv X f.toEquiv
  have : Group.IsPerfect Y := Group.IsPerfect.ofSurjective (f := f.toMonoidHom) f.surjective
  have hX := finite_hopfMultiplier (inferInstance : Group.IsPerfect X)
  have hY := finite_hopfMultiplier (inferInstance : Group.IsPerfect Y)
  have hXn : Nat.card (hopfMultiplier X) ≠ 0 := Nat.card_pos.ne'
  have hYn : Nat.card (hopfMultiplier Y) ≠ 0 := Nat.card_pos.ne'
  refine Nat.eq_of_factorization_eq hXn hYn fun p => ?_
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    have h1 := primaryCentralKernelOrder_of_card_hopfMultiplier_eq (X := Y) rfl p
    exact (primaryCentralKernelOrder_iff.1 (primaryCentralKernelOrder_of_mulEquiv f h1))
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

theorem kernelTrivialAt_iff_of_mulEquiv {X Y : Type} [Group X] [Group Y] (f : X ≃* Y) (p : ℕ) :
    KernelTrivialAt X p ↔ KernelTrivialAt Y p := by
  have key : ∀ {X Y : Type} [Group X] [Group Y] (f : X ≃* Y),
      KernelTrivialAt Y p → KernelTrivialAt X p := by
    intro X Y _ _ f h E _ _ _ π hπ hC hp
    have hk := MonoidHom.ker_comp_of_injective π f.toMonoidHom f.injective
    have := h E (f.toMonoidHom.comp π) (f.surjective.comp hπ) (by rw [hk]; exact hC)
      (by rw [hk]; exact hp)
    rwa [hk] at this
  exact ⟨key f.symm, key f⟩

end Transport

section Sporadic

open CFSG.Blueprint

theorem kernelTrivialAt_carrier_of_sporadicKernelTrivial {s : TauCeti.SporadicName} {p : ℕ}
    (h : ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (S : Type) [Group S]
      (π : E →* S), NativeSporadic.IsSporadic S s → Function.Surjective π →
        π.ker ≤ Subgroup.center E → IsPGroup p π.ker → π.ker = ⊥) :
    KernelTrivialAt (NativeSporadic.Carrier s) p :=
  fun E _ _ _ π hπ hC hp => h E (NativeSporadic.Carrier s) π ⟨MulEquiv.refl _⟩ hπ hC hp

end Sporadic

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster
