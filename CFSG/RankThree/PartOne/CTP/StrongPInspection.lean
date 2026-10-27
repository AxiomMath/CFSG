module

public import CFSG.RankThree.PartOne.CTP.StrongPClassification
public import CFSG.RankThree.GroupTheory.SteinbergCEAlternatingDegreeThirteen

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.RankThree.PartOne (IsStronglyPEmbedded IsSylowOf omegaOne)
open CFSG.RankThree.PartOne.Census3 (IsoLie TheoremThreeHyp)
open CFSG.RankThree.GroupTheory
  (alternating_central_covers_degree_thirteen_force_two_local_three_rank_four)

section Omega

variable {H : Type*} [Group H] {p : ℕ}

theorem omegaOne_le (P : Subgroup H) : omegaOne p P ≤ P :=
  (Subgroup.closure_le P).mpr fun _ hx => hx.1

theorem omegaOne_eq_of_pow_eq_one {P : Subgroup H} (h : ∀ x ∈ P, x ^ p = 1) :
    omegaOne p P = P :=
  le_antisymm (omegaOne_le P) fun _ hx => Subgroup.subset_closure ⟨hx, h _ hx⟩

theorem isElementaryAbelian_of_subgroup {A : Type*} [Group A] [IsElementaryAbelian p A]
    (K : Subgroup A) : IsElementaryAbelian p ↥K := by
  refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => Subtype.ext ?_
  have hx : (x : A) ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p A) x
  simpa using hx

theorem exists_elementaryAbelian_sq_le [Fact p.Prime] [Finite H] {A : Subgroup H}
    [IsElementaryAbelian p ↥A] (hdvd : p ^ 2 ∣ Nat.card A) :
    ∃ E : Subgroup H, E ≤ A ∧ IsElementaryAbelian p ↥E ∧ Nat.card E = p ^ 2 := by
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime p hdvd
  have : IsElementaryAbelian p ↥K := isElementaryAbelian_of_subgroup K
  refine ⟨K.map A.subtype, ?_, CFSG.IsElementaryAbelian.map A.subtype, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rw [Subgroup.card_map_of_injective A.subtype_injective, hK]

end Omega

theorem extSPEHyp_of_classification (hC : StronglyPEmbeddedClassification)
    (hFi22 : Census3.ExcludedIndex (.sporadic .Fi22)) :
    ∀ p : ℕ, p.Prime → 5 ≤ p →
      ∀ (H : Type) [Group H] [Finite H] (S : Subgroup H), S.Normal → TheoremThreeHyp ↥S →
        Subgroup.centralizer (S : Set H) = ⊥ →
        ∀ Y : Subgroup H, IsStronglyPEmbedded p Y →
          ∀ P : Subgroup H, IsSylowOf p P ⊤ → IsElementaryAbelian p (omegaOne p P) →
            (Nat.card (omegaOne p P) = p ^ 2 ∨ Nat.card (omegaOne p P) = p ^ 3) →
            (∃ q : TauCeti.PrimePower, q.p = p ∧ (q.exponent = 2 ∨ q.exponent = 3) ∧
              IsoLie ↥S (.A 1 q)) ∨
            (p = 5 ∧ (Nonempty (↥S ≃* alternatingGroup (Fin 10)) ∨ IsoLie ↥S .tits ∨
              IsoLie ↥S (.suzuki 2))) := by
  intro p hp hp5 H _ _ S hSn hSh hSc Y hY P hP hab hcard
  have : Fact p.Prime := ⟨hp⟩
  have hm2 : ∃ E : Subgroup H, E ≤ P ∧ IsElementaryAbelian p ↥E ∧ Nat.card E = p ^ 2 := by
    have hdvd : p ^ 2 ∣ Nat.card (omegaOne p P) := by
      rcases hcard with h | h
      · exact dvd_of_eq h.symm
      · rw [h]
        exact pow_dvd_pow p (by norm_num)
    obtain ⟨E, hEA, hEab, hEc⟩ :=
      exists_elementaryAbelian_sq_le (p := p) (A := omegaOne p P) hdvd
    exact ⟨E, hEA.trans (omegaOne_le P), hEab, hEc⟩
  rcases hC p hp hp5 H S hSn hSh hSc Y hY P hP hm2 with
    ⟨q, hqp, hq2, hiso, hPab, hPcard⟩ | ⟨q, hqp, hiso, hexp, hnc⟩ | halt | ⟨hp5', hiso⟩ |
    ⟨hp5', hiso⟩ | ⟨hp5', hiso, hexp, hnc⟩ | ⟨hp5', hiso⟩ | ⟨hp11, hiso, hexp, hnc⟩
  ·
    left
    have hΩ : omegaOne p P = P := omegaOne_eq_of_pow_eq_one fun x hx =>
      elemPow_eq_one_of_isElementaryAbelian (A := P) x hx
    rw [hΩ, hPcard, TauCeti.PrimePower.card_def, hqp] at hcard
    refine ⟨q, hqp, ?_, hiso⟩
    have hpq : p ^ q.exponent = p ^ 2 ∨ p ^ q.exponent = p ^ 3 := by simpa using hcard
    rcases hpq with h | h
    · exact Or.inl (Nat.pow_right_injective hp.two_le h)
    · exact Or.inr (Nat.pow_right_injective hp.two_le h)
  ·
    exfalso
    apply hnc
    have hΩ : omegaOne p P = P := omegaOne_eq_of_pow_eq_one hexp
    rw [hΩ] at hab
    exact hab.toIsMulCommutative
  ·
    right
    obtain ⟨e⟩ := halt
    have h12 : 2 * p ≤ 12 := by
      let π : (⊤ : Subgroup ↥S) →* alternatingGroup (Fin (2 * p)) :=
        e.toMonoidHom.comp Subgroup.topEquiv.toMonoidHom
      have hinj : Function.Injective π := e.injective.comp Subgroup.topEquiv.injective
      have hZ : π.ker ≤ Subgroup.center (⊤ : Subgroup ↥S) := by
        intro x hx
        rw [(MonoidHom.ker_eq_bot_iff π).mpr hinj, Subgroup.mem_bot] at hx
        rw [hx]
        exact Subgroup.one_mem _
      have hbound := alternating_central_covers_degree_thirteen_force_two_local_three_rank_four
        π (e.surjective.comp Subgroup.topEquiv.surjective) hZ
      exact hbound.2.2.1 hSh.twoLocalOddRank_le
    have hp5'' : p = 5 := by
      have h6 : p ≤ 6 := by omega
      interval_cases p
      · rfl
      · exact absurd hp (by norm_num)
    subst hp5''
    exact ⟨rfl, Or.inl ⟨e⟩⟩
  · exact Or.inr ⟨hp5', Or.inr (Or.inr hiso)⟩
  · exact Or.inr ⟨hp5', Or.inr (Or.inl hiso)⟩
  · exfalso
    apply hnc
    have hΩ : omegaOne p P = P := omegaOne_eq_of_pow_eq_one hexp
    rw [hΩ] at hab
    exact hab.toIsMulCommutative
  ·
    exfalso
    obtain ⟨e⟩ := hiso
    have h4 := hFi22 ↥S hSh.isSimpleGroup hSh.nonabelian e
    have h3 := hSh.twoLocalOddRank_le
    omega
  · exfalso
    apply hnc
    have hΩ : omegaOne p P = P := omegaOne_eq_of_pow_eq_one hexp
    rw [hΩ] at hab
    exact hab.toIsMulCommutative

end CFSG.RankThree.PartOne.CTP
