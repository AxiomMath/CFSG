module

public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster

open CFSG.RankThree.PerfectCover

section Basic

variable {X : Type} [Group X]

theorem card_ker_dvd_card_hopfMultiplier [Finite X] {E : Type} [Group E] [Finite E]
    [Group.IsPerfect E] (π : E →* X) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) :
    Nat.card π.ker ∣ Nat.card (hopfMultiplier X) := by
  have hX : Group.IsPerfect X := Group.IsPerfect.ofSurjective hπ
  have := finite_hopfMultiplier hX
  rw [← map_hopfMultiplier_hopfLift π hπ hC]
  exact Subgroup.card_map_dvd (H := hopfMultiplier X) (hopfLift π hπ hC)

theorem isMulCommutative_hopfMultiplier [Group.IsPerfect X] :
    IsMulCommutative (hopfMultiplier X) :=
  ⟨⟨fun a b => Subtype.ext (Subgroup.mem_center_iff.1 (hopfMultiplier_le_center b.2) a)⟩⟩

end Basic

section Covers

variable {X : Type} [Group X] [Finite X] [Group.IsPerfect X]

theorem exists_perfect_central_cover_card_ker_eq_index (N₀ : Subgroup (hopfMultiplier X)) :
    ∃ (E : Type) (_ : Group E) (_ : Finite E) (_ : Group.IsPerfect E) (π : E →* X),
      Function.Surjective π ∧ π.ker ≤ Subgroup.center E ∧ Nat.card π.ker = N₀.index := by
  have : Finite (HopfCover X) := finite_hopfCover inferInstance
  have : Group.IsPerfect (HopfCover X) := hopfCover_isPerfect
  have hMc : hopfMultiplier X ≤ Subgroup.center (HopfCover X) := hopfMultiplier_le_center
  let N : Subgroup (HopfCover X) := N₀.map (hopfMultiplier X).subtype
  have hNM : N ≤ hopfMultiplier X := Subgroup.map_subtype_le N₀
  have : N.Normal := Subgroup.normal_of_le_center (hNM.trans hMc)
  let πK : HopfCover X ⧸ N →* X := QuotientGroup.lift N (hopfCoverMap X) hNM
  have hπK : Function.Surjective πK := by
    intro s
    obtain ⟨d, rfl⟩ := hopfCoverMap_surjective (S := X) s
    exact ⟨QuotientGroup.mk d, rfl⟩
  have hkerK : πK.ker = (hopfMultiplier X).map (QuotientGroup.mk' N) :=
    QuotientGroup.ker_lift _ _ _
  have hcK : πK.ker ≤ Subgroup.center (HopfCover X ⧸ N) := by
    rw [hkerK]
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    induction g using QuotientGroup.induction_on with
    | H g =>
      have h := congrArg (QuotientGroup.mk' N) (Subgroup.mem_center_iff.1 (hMc hz) g)
      simpa using h
  refine ⟨HopfCover X ⧸ N, inferInstance, inferInstance, inferInstance, πK, hπK, hcK, ?_⟩
  rw [hkerK]
  let f : hopfMultiplier X →* HopfCover X ⧸ N :=
    (QuotientGroup.mk' N).comp (hopfMultiplier X).subtype
  have hf : f.ker = N₀ := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact Subgroup.mem_map_iff_mem (hopfMultiplier X).subtype_injective
  have hr : (hopfMultiplier X).map (QuotientGroup.mk' N) = f.range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hr, ← Subgroup.index_ker, hf]

theorem exists_perfect_central_pCover_card_ker_eq_primary_part (p : ℕ) [Fact p.Prime] :
    ∃ (E : Type) (_ : Group E) (_ : Finite E) (_ : Group.IsPerfect E) (π : E →* X),
      Function.Surjective π ∧ π.ker ≤ Subgroup.center E ∧ IsPGroup p π.ker ∧
        Nat.card π.ker = p ^ (Nat.card (hopfMultiplier X)).factorization p := by
  have := finite_hopfMultiplier (inferInstance : Group.IsPerfect X)
  have : IsMulCommutative (hopfMultiplier X) := isMulCommutative_hopfMultiplier
  obtain P : Sylow p (hopfMultiplier X) := default
  have hPn : (P : Subgroup (hopfMultiplier X)).Normal := Subgroup.normal_of_isMulCommutative _
  have hcop : Nat.Coprime (Nat.card (P : Subgroup (hopfMultiplier X)))
      (P : Subgroup (hopfMultiplier X)).index := by
    rw [P.card_eq_multiplicity]
    exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 P.not_dvd_index)
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  obtain ⟨E, _, _, _, π, hπ, hC, hcard⟩ := exists_perfect_central_cover_card_ker_eq_index H
  have hidx : H.index = p ^ (Nat.card (hopfMultiplier X)).factorization p := by
    rw [hH.index_eq_card]
    exact P.card_eq_multiplicity
  rw [hidx] at hcard
  exact ⟨E, inferInstance, inferInstance, inferInstance, π, hπ, hC, IsPGroup.of_card hcard, hcard⟩

theorem card_ker_dvd_primary_part {p : ℕ} [Fact p.Prime] {E : Type} [Group E] [Finite E]
    [Group.IsPerfect E] (π : E →* X) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hp : IsPGroup p π.ker) :
    Nat.card π.ker ∣ p ^ (Nat.card (hopfMultiplier X)).factorization p := by
  have := finite_hopfMultiplier (inferInstance : Group.IsPerfect X)
  have hM : Nat.card (hopfMultiplier X) ≠ 0 := Nat.card_pos.ne'
  have hd := card_ker_dvd_card_hopfMultiplier π hπ hC
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  rw [hk] at hd ⊢
  exact pow_dvd_pow p ((Nat.Prime.pow_dvd_iff_le_factorization Fact.out hM).1 hd)

end Covers

section Cells

variable (X : Type) [Group X]

@[expose] def PrimaryCentralKernelOrder (p k : ℕ) : Prop :=
  (∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* X), Function.Surjective π →
      π.ker ≤ Subgroup.center E → IsPGroup p π.ker → Nat.card π.ker ∣ p ^ k) ∧
    ∃ (E : Type) (_ : Group E) (_ : Finite E) (_ : Group.IsPerfect E) (π : E →* X),
      Function.Surjective π ∧ π.ker ≤ Subgroup.center E ∧ IsPGroup p π.ker ∧
        Nat.card π.ker = p ^ k

variable {X}

theorem primaryCentralKernelOrder_iff [Finite X] [Group.IsPerfect X] {p : ℕ} [Fact p.Prime]
    {k : ℕ} :
    PrimaryCentralKernelOrder X p k ↔ (Nat.card (hopfMultiplier X)).factorization p = k := by
  have hM : Nat.card (hopfMultiplier X) ≠ 0 := by
    have := finite_hopfMultiplier (inferInstance : Group.IsPerfect X)
    exact Nat.card_pos.ne'
  constructor
  · rintro ⟨hup, E, _, _, _, π, hπ, hC, hp, hcard⟩
    have h1 : k ≤ (Nat.card (hopfMultiplier X)).factorization p := by
      have := card_ker_dvd_card_hopfMultiplier π hπ hC
      rw [hcard] at this
      exact (Nat.Prime.pow_dvd_iff_le_factorization Fact.out hM).1 this
    obtain ⟨E', _, _, _, π', hπ', hC', hp', hcard'⟩ :=
      exists_perfect_central_pCover_card_ker_eq_primary_part (X := X) p
    have h2 := hup E' π' hπ' hC' hp'
    rw [hcard'] at h2
    have := (Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt).1 h2
    omega
  · rintro rfl
    refine ⟨fun E _ _ _ π hπ hC hp => card_ker_dvd_primary_part π hπ hC hp, ?_⟩
    exact exists_perfect_central_pCover_card_ker_eq_primary_part (X := X) p

theorem card_hopfMultiplier_eq_of_primaryCentralKernelOrder [Finite X] [Group.IsPerfect X]
    {n : ℕ} (hn : n ≠ 0)
    (h : ∀ (p : ℕ) [Fact p.Prime], PrimaryCentralKernelOrder X p (n.factorization p)) :
    Nat.card (hopfMultiplier X) = n := by
  have hM : Nat.card (hopfMultiplier X) ≠ 0 := by
    have := finite_hopfMultiplier (inferInstance : Group.IsPerfect X)
    exact Nat.card_pos.ne'
  refine Nat.eq_of_factorization_eq hM hn fun p => ?_
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    exact primaryCentralKernelOrder_iff.1 (h p)
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

theorem primaryCentralKernelOrder_of_card_hopfMultiplier_eq [Finite X] [Group.IsPerfect X]
    {n : ℕ} (hn : Nat.card (hopfMultiplier X) = n) (p : ℕ) [Fact p.Prime] :
    PrimaryCentralKernelOrder X p (n.factorization p) :=
  primaryCentralKernelOrder_iff.2 (by rw [hn])

end Cells

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster
