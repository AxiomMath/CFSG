module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qi

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.ABGLocalTools
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem uc22p22qn_derivedSeries_eq_bot {Q : Type*} [Group Q] [Finite Q] [Group.IsSolvable Q] {n : ℕ}
    (hn : Nat.card Q ≤ n) : derivedSeries Q n = ⊥ := by
  have key : ∀ k : ℕ, derivedSeries Q k = ⊥ ∨ Nat.card (derivedSeries Q k) + k ≤ Nat.card Q := by
    intro k
    induction k with
    | zero =>
      right
      simp [derivedSeries_zero]
    | succ k ih =>
      by_cases hbot : derivedSeries Q k = ⊥
      · left
        rw [derivedSeries_succ, hbot]
        simp
      · right
        have hk : Nat.card (derivedSeries Q k) + k ≤ Nat.card Q := ih.resolve_left hbot
        have hlt : derivedSeries Q (k + 1) < derivedSeries Q k := by
          rw [derivedSeries_succ]
          exact Group.IsSolvable.commutator_lt_of_ne_bot hbot
        have := Subgroup.card_lt_of_lt hlt
        omega
  have h1 : derivedSeries Q (Nat.card Q) = ⊥ := by
    rcases key (Nat.card Q) with h | h
    · exact h
    · have := Nat.card_pos (α := derivedSeries Q (Nat.card Q))
      omega
  exact le_bot_iff.1 ((derivedSeries_antitone Q hn).trans h1.le)

theorem uc22p22qn_infty_le {X E : Subgroup G} [hn : (E.subgroupOf X).Normal]
    (hsolv : Group.IsSolvable (↥X ⧸ E.subgroupOf X)) : UC6.inftyOf X ≤ E := by
  let π : ↥X →* ↥X ⧸ E.subgroupOf X := QuotientGroup.mk' (E.subgroupOf X)
  have hcard : Nat.card (↥X ⧸ E.subgroupOf X) ≤ Nat.card ↥X :=
    Nat.card_le_card_of_surjective π (QuotientGroup.mk'_surjective _)
  have hbot : derivedSeries (↥X ⧸ E.subgroupOf X) (Nat.card ↥X) = ⊥ :=
    uc22p22qn_derivedSeries_eq_bot hcard
  have hle : derivedSeries ↥X (Nat.card ↥X) ≤ E.subgroupOf X := by
    intro x hx
    have h1 : π x ∈ derivedSeries (↥X ⧸ E.subgroupOf X) (Nat.card ↥X) :=
      map_derivedSeries_le_derivedSeries π _ ⟨x, hx, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    exact (QuotientGroup.eq_one_iff (N := E.subgroupOf X) x).1 h1
  calc UC6.inftyOf X = (derivedSeries ↥X (Nat.card ↥X)).map X.subtype := rfl
    _ ≤ (E.subgroupOf X).map X.subtype := Subgroup.map_mono hle
    _ ≤ E := by
      rintro _ ⟨y, hy, rfl⟩
      exact hy

theorem uc22p22qn_le_infty {X E : Subgroup G} (hEX : E ≤ X) (hperf : ⁅E, E⁆ = E) : E ≤ UC6.inftyOf X := by
  have hcomm : ⁅E.subgroupOf X, E.subgroupOf X⁆ = E.subgroupOf X := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hEX, hperf]
  have key : ∀ k : ℕ, E.subgroupOf X ≤ derivedSeries ↥X k := by
    intro k
    induction k with
    | zero => exact le_top
    | succ k ih =>
      rw [derivedSeries_succ]
      calc E.subgroupOf X = ⁅E.subgroupOf X, E.subgroupOf X⁆ := hcomm.symm
        _ ≤ ⁅derivedSeries ↥X k, derivedSeries ↥X k⁆ := Subgroup.commutator_mono ih ih
  calc E = (E.subgroupOf X).map X.subtype := (Subgroup.map_subgroupOf_eq_of_le hEX).symm
    _ ≤ (derivedSeries ↥X (Nat.card ↥X)).map X.subtype := Subgroup.map_mono (key _)
    _ = UC6.inftyOf X := rfl

theorem uc22p22qn_isPerfect_of_simple {K : Type*} [Group K] [IsSimpleGroup K] (hnc : ¬ IsMulCommutative K) :
    Group.IsPerfect K := by
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator K) with h | h
  · exfalso
    apply hnc
    refine ⟨⟨fun a b => ?_⟩⟩
    have h1 : ⁅a, b⁆ ∈ commutator K := by
      rw [_root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  · exact h

theorem uc22p22qn_quot_solvable {p : ℕ} [Fact p.Prime] {X E S : Subgroup G} (hEX : E ≤ X)
    [hn : (E.subgroupOf X).Normal] (hS : IsSylowOf p S E)
    (hsolv : Group.IsSolvable ↥(X ⊓ normalizer (S : Set G))) :
    Group.IsSolvable (↥X ⧸ E.subgroupOf X) := by
  have hXE : X ≤ normalizer (E : Set G) := (Subgroup.normal_subgroupOf_iff_le_normalizer hEX).1 hn
  have hfr : ∀ x ∈ X, ∃ e ∈ E, e⁻¹ * x ∈ normalizer (S : Set G) := by
    intro x hx
    have hxE' := hXE hx
    have hEmap : E.map (MulAut.conj x).toMonoidHom = E :=
      uc22p22qi_map_eq_of_conj_mem (M := X) (K := E) (fun k hk y hy =>
        (mem_normalizer_iff.1 (hXE hk) y).1 hy) hx
    set S' : Subgroup G := S.map (MulAut.conj x).toMonoidHom with hS'
    have hS'E : IsSylowOf p S' E := by
      rw [isSylowOf_iff] at hS ⊢
      obtain ⟨hle, hpg, hrel⟩ := hS
      refine ⟨?_, hpg.of_equiv (Subgroup.equivMapOfInjective _ _ (MulAut.conj x).injective), ?_⟩
      · rw [← hEmap]
        exact Subgroup.map_mono hle
      · rw [← hEmap, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj x).injective]
        exact hrel
    obtain ⟨e, he, hk⟩ := hS.exists_mem_conj hS'E
    refine ⟨e, he, uc22p22qk_mem_normalizer fun s hs => ?_⟩
    have h1 : x * s * x⁻¹ ∈ S' := ⟨s, hs, rfl⟩
    have h2 := (hk _).1 h1
    simpa [mul_assoc] using h2
  let ρ : ↥(X ⊓ normalizer (S : Set G)) →* ↥X ⧸ E.subgroupOf X :=
    (QuotientGroup.mk' (E.subgroupOf X)).comp (Subgroup.inclusion inf_le_left)
  have hρ : Function.Surjective ρ := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (E.subgroupOf X) q
    obtain ⟨e, he, hen⟩ := hfr x x.2
    have heX : e ∈ X := hEX he
    refine ⟨⟨e⁻¹ * x, X.mul_mem (X.inv_mem heX) x.2, hen⟩, ?_⟩
    change QuotientGroup.mk' (E.subgroupOf X) (⟨e⁻¹ * x, X.mul_mem (X.inv_mem heX) x.2⟩ : ↥X) = _
    have h1 : (⟨e⁻¹ * x, X.mul_mem (X.inv_mem heX) x.2⟩ : ↥X) = ⟨e, heX⟩⁻¹ * x := rfl
    rw [h1, map_mul, map_inv]
    have h2 : QuotientGroup.mk' (E.subgroupOf X) (⟨e, heX⟩ : ↥X) = 1 :=
      (QuotientGroup.eq_one_iff (N := E.subgroupOf X) _).2 he
    rw [h2, inv_one, one_mul]
  haveI := hsolv
  exact Group.isSolvable_of_surjective hρ

end CFSG.LocalAnalysis.UniquenessCase.UC22
