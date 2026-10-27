module

public import CFSG.RankThree.PartOne.S11d.LayerLink

public section

namespace CFSG.RankThree.PartOne.FOC

open Subgroup CFSG

theorem isComponentOf_subgroupOf_eq_commutator {T : Type} [Group T] [Finite T] {C E : Subgroup T}
    (hq : CFSG.IsQuasisimple ↥(commutator ↥C)) (hE : IsComponentOf C E) :
    E.subgroupOf C = commutator ↥C := by
  have hC' : CFSG.IsComponent (E.subgroupOf C) := isComponent_subgroupOf_of_isComponentOf hE
  have hD : CFSG.IsComponent (commutator ↥C) :=
    ⟨hq, (inferInstance : (commutator ↥C).Normal).isSubnormal⟩
  have hperf : ⁅E.subgroupOf C, E.subgroupOf C⁆ = E.subgroupOf C := by
    have h1 : (commutator ↥(E.subgroupOf C)).map (E.subgroupOf C).subtype =
        ⁅E.subgroupOf C, E.subgroupOf C⁆ := by
      rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    have h2 : commutator ↥(E.subgroupOf C) = ⊤ := hC'.1.1.commutator_eq_top
    rw [h2, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
    exact h1.symm
  have hle : E.subgroupOf C ≤ commutator ↥C := by
    rw [_root_.commutator_def]
    calc E.subgroupOf C = ⁅E.subgroupOf C, E.subgroupOf C⁆ := hperf.symm
      _ ≤ ⁅(⊤ : Subgroup ↥C), ⊤⁆ := Subgroup.commutator_mono le_top le_top
  rcases CFSG.LocalCores.distinct_components_commute hC' hD with h | h
  · exact h
  · exfalso
    have hbot : E.subgroupOf C = ⊥ := by
      refine le_bot_iff.mp ?_
      calc E.subgroupOf C = ⁅E.subgroupOf C, E.subgroupOf C⁆ := hperf.symm
        _ ≤ ⁅E.subgroupOf C, commutator ↥C⁆ := Subgroup.commutator_mono le_rfl hle
        _ = ⊥ := h
    have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hC'.1
    rw [hbot] at hnt
    exact not_nontrivial_iff_subsingleton.mpr
      (inferInstance : Subsingleton (⊥ : Subgroup ↥C)) hnt

theorem mem_of_isComponentOf_of_mem_commutator {T : Type} [Group T] [Finite T] {C E : Subgroup T}
    (hq : CFSG.IsQuasisimple ↥(commutator ↥C)) (hE : IsComponentOf C E) {y : T} (hy : y ∈ C)
    (hyc : (⟨y, hy⟩ : ↥C) ∈ commutator ↥C) : y ∈ E := by
  have h := isComponentOf_subgroupOf_eq_commutator hq hE
  rw [← h] at hyc
  exact hyc


theorem isComponentOf_subgroupOf_eq_of_solvable_quotient {T : Type} [Group T] [Finite T]
    {C E : Subgroup T} {D : Subgroup ↥C} [D.Normal] (hq : CFSG.IsQuasisimple ↥D)
    (hsol : Group.IsSolvable (↥C ⧸ D)) (hE : IsComponentOf C E) : E.subgroupOf C = D := by
  have hC' : CFSG.IsComponent (E.subgroupOf C) := isComponent_subgroupOf_of_isComponentOf hE
  have hD : CFSG.IsComponent D := ⟨hq, (inferInstance : D.Normal).isSubnormal⟩
  have hperf : ⁅E.subgroupOf C, E.subgroupOf C⁆ = E.subgroupOf C := by
    have h1 : (commutator ↥(E.subgroupOf C)).map (E.subgroupOf C).subtype =
        ⁅E.subgroupOf C, E.subgroupOf C⁆ := by
      rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    have h2 : commutator ↥(E.subgroupOf C) = ⊤ := hC'.1.1.commutator_eq_top
    rw [h2, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
    exact h1.symm
  have hds : ∀ n : ℕ, E.subgroupOf C ≤ derivedSeries ↥C n := by
    intro n
    induction n with
    | zero => exact le_top
    | succ n ih =>
      rw [derivedSeries_succ]
      calc E.subgroupOf C = ⁅E.subgroupOf C, E.subgroupOf C⁆ := hperf.symm
        _ ≤ ⁅derivedSeries ↥C n, derivedSeries ↥C n⁆ := Subgroup.commutator_mono ih ih
  have hle : E.subgroupOf C ≤ D := by
    obtain ⟨n, hn⟩ := hsol.solvable
    refine (hds n).trans ?_
    have h1 := map_derivedSeries_le_derivedSeries (QuotientGroup.mk' D) n
    rw [hn] at h1
    intro g hg
    have : (QuotientGroup.mk' D) g = 1 := by
      have := h1 ⟨g, hg, rfl⟩
      simpa using this
    exact (QuotientGroup.eq_one_iff g).mp this
  rcases CFSG.LocalCores.distinct_components_commute hC' hD with h | h
  · exact h
  · exfalso
    have hbot : E.subgroupOf C = ⊥ := by
      refine le_bot_iff.mp ?_
      calc E.subgroupOf C = ⁅E.subgroupOf C, E.subgroupOf C⁆ := hperf.symm
        _ ≤ ⁅E.subgroupOf C, D⁆ := Subgroup.commutator_mono le_rfl hle
        _ = ⊥ := h
    have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hC'.1
    rw [hbot] at hnt
    exact not_nontrivial_iff_subsingleton.mpr
      (inferInstance : Subsingleton (⊥ : Subgroup ↥C)) hnt

theorem mem_of_isComponentOf_of_normal_simple {T : Type} [Group T] [Finite T]
    {N J E : Subgroup T} (hJN : J ≤ N) (hJn : (J.subgroupOf N).Normal) [IsSimpleGroup ↥J]
    (hnab : ∃ a b : ↥J, a * b ≠ b * a) (h2 : IsPGroup 2 (↥N ⧸ J.subgroupOf N))
    (hE : IsComponentOf N E) {x : T} (hxN : x ∈ N) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hxp : x ^ p = 1) : x ∈ E := by
  have : IsSimpleGroup ↥(J.subgroupOf N) :=
    (Subgroup.subgroupOfEquivOfLe hJN).isSimpleGroup
  have hnab' : ∃ a b : ↥(J.subgroupOf N), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨(Subgroup.subgroupOfEquivOfLe hJN).symm a, (Subgroup.subgroupOfEquivOfLe hJN).symm b,
      fun h => hab ?_⟩
    have := congrArg (Subgroup.subgroupOfEquivOfLe hJN) h
    simpa using this
  have hq := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab').1
  have : Group.IsNilpotent (↥N ⧸ J.subgroupOf N) := h2.isNilpotent
  have hsol : Group.IsSolvable (↥N ⧸ J.subgroupOf N) := inferInstance
  have heq := isComponentOf_subgroupOf_eq_of_solvable_quotient (D := J.subgroupOf N) hq hsol hE
  have hx : (⟨x, hxN⟩ : ↥N) ∈ J.subgroupOf N := by
    have h1 : orderOf (QuotientGroup.mk (⟨x, hxN⟩ : ↥N) : ↥N ⧸ J.subgroupOf N) ∣ p := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← QuotientGroup.mk_pow]
      have : (⟨x, hxN⟩ : ↥N) ^ p = 1 := Subtype.ext (by simpa using hxp)
      rw [this]
      rfl
    obtain ⟨k, hk⟩ := h2 (QuotientGroup.mk (⟨x, hxN⟩ : ↥N))
    have h3 : orderOf (QuotientGroup.mk (⟨x, hxN⟩ : ↥N) : ↥N ⧸ J.subgroupOf N) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one hk
    have hcop : Nat.Coprime p (2 ^ k) :=
      Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    have h4 : orderOf (QuotientGroup.mk (⟨x, hxN⟩ : ↥N) : ↥N ⧸ J.subgroupOf N) = 1 :=
      Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd h1 h3)
    exact (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp h4)
  rw [← heq] at hx
  exact hx

end CFSG.RankThree.PartOne.FOC
