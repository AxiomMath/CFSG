module

public import CFSG.Sporadic.SmallOddCore.Assembly
public import CFSG.RankThree.PartOne.KC.PlaneReduction

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory CFSG.Sporadic.SmallOddCore
open scoped Pointwise

theorem card_aschbacherCore_centralizer_mulEquiv {G G' : Type*} [Group G] [Group G']
    [Finite G] {p : ℕ} (hp : p.Prime) (ψ : G ≃* G') (g : G) :
    Nat.card (inSubgroup (aschbacherSolvableCore p) (centralizer ({g} : Set G))) =
      Nat.card (inSubgroup (aschbacherSolvableCore p) (centralizer ({ψ g} : Set G'))) := by
  have h := SteinbergBY.map_inSubgroup_aschbacherSolvableCore_mulEquiv hp ψ
    (centralizer ({g} : Set G))
  rw [map_centralizer_singleton_mulEquiv ψ g] at h
  rw [← h]
  exact (Subgroup.card_map_of_injective ψ.injective).symm

theorem card_aschbacherCore_subgroup_centralizer {M : Type*} [Group M] [Finite M] {p : ℕ}
    (hp : p.Prime) (B : Subgroup M) (b : B) :
    Nat.card (inSubgroup (aschbacherSolvableCore p) (centralizer ({b} : Set B))) =
      Nat.card (inSubgroup (aschbacherSolvableCore p) (B ⊓ centralizer ({(b : M)} : Set M))) := by
  rw [← map_subtype_theta_centralizer hp B b]
  exact (Subgroup.card_map_of_injective B.subtype_injective).symm

theorem card_core_centralizer_eq_of_model {M : Type*} [Group M] [Finite M]
    {P R : Subgroup M} (h : AutModel P R) (hidx : Nat.card R ≤ 2 * Nat.card P) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {X : Type*} [Group X] [Finite X] (S : Subgroup X) [S.Normal]
    (θ : S ≃* P) (hC : centralizer (S : Set X) = ⊥) (x : X) (hx : orderOf x = p) :
    h.embed S θ x ∈ P ∧ ∃ B : Subgroup M, P ≤ B ∧ B ≤ R ∧
      Nat.card (inSubgroup (aschbacherSolvableCore p) (centralizer ({x} : Set X))) =
        Nat.card (inSubgroup (aschbacherSolvableCore p)
          (B ⊓ centralizer ({h.embed S θ x} : Set M))) := by
  have hinj := h.embed_injective S θ hC
  set ι := h.embed S θ with hι
  set B : Subgroup M := ι.range with hB
  have hPB : P ≤ B := fun y hy => ⟨((θ.symm ⟨y, hy⟩ : S) : X), by
    rw [hι, h.embed_coe, MulEquiv.apply_symm_apply]⟩
  have hBR : B ≤ R := by
    rintro _ ⟨x', rfl⟩
    exact h.embed_mem S θ x'
  have hord : orderOf (ι x) = p := by rw [orderOf_injective _ hinj, hx]
  have hyR : ι x ∈ R := h.embed_mem S θ x
  have hPnorm : (P.subgroupOf R).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact h.conj_mem g g.2 n hn⟩
  have hRP : Nat.card R ≤ 2 * Nat.card (P.subgroupOf R) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le).toEquiv]
    exact hidx
  have hyP : ι x ∈ P := by
    have hodd : Odd (Nat.card (Subgroup.zpowers (⟨ι x, hyR⟩ : R))) := by
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, hord]
      exact hp.odd_of_ne_two hp2
    have hle := odd_card_map_le_of_index_le_two (P.subgroupOf R) hRP hodd
    exact hle (Subgroup.mem_zpowers _)
  refine ⟨hyP, B, hPB, hBR, ?_⟩
  let ψ : X ≃* B := MonoidHom.ofInjective hinj
  rw [card_aschbacherCore_centralizer_mulEquiv hp ψ x]
  exact card_aschbacherCore_subgroup_centralizer hp B (ψ x)

theorem aschbacherCore_centralizer_eq_bot_of_model {M : Type*} [Group M] [Finite M]
    {P R : Subgroup M} (h : AutModel P R) (hidx : Nat.card R ≤ 2 * Nat.card P) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hline : ∀ B : Subgroup M, P ≤ B → B ≤ R → ∀ y ∈ P, orderOf y = p →
      inSubgroup (aschbacherSolvableCore p) (B ⊓ centralizer ({y} : Set M)) = ⊥)
    {X : Type*} [Group X] [Finite X] (S : Subgroup X) [S.Normal] (θ : S ≃* P)
    (hC : centralizer (S : Set X) = ⊥) (x : X) (hx : orderOf x = p) :
    inSubgroup (aschbacherSolvableCore p) (centralizer ({x} : Set X)) = ⊥ := by
  obtain ⟨hyP, B, hPB, hBR, hcard⟩ :=
    card_core_centralizer_eq_of_model h hidx hp hp2 S θ hC x hx
  have hord : orderOf (h.embed S θ x) = p := by
    rw [orderOf_injective _ (h.embed_injective S θ hC), hx]
  rw [hline B hPB hBR _ hyP hord, Subgroup.card_bot] at hcard
  exact Subgroup.card_eq_one.mp hcard

theorem not_dvd_card_inSubgroup_aschbacherSolvableCore {M : Type*} [Group M] [Finite M] {p : ℕ}
    (hp : p.Prime) (C : Subgroup M) :
    ¬ p ∣ Nat.card (inSubgroup (aschbacherSolvableCore p) C) := by
  rw [inSubgroup, Subgroup.card_map_of_injective C.subtype_injective]
  exact (solvable_prime_complement_core_characterization (H := C) hp).2.2.1

theorem aschbacherCore_bot_of_normal_pgroup {C : Type*} [Group C] [Finite C] {p : ℕ}
    (hp : p.Prime) {Z : Subgroup C} [Z.Normal] (hZ : IsPGroup p Z)
    (hc : IsPGroup p (centralizer (Z : Set C))) : aschbacherSolvableCore p C = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hchar, hnd, -⟩ := solvable_prime_complement_core_characterization (H := C) hp
  have hnorm : (aschbacherSolvableCore p C).Normal := by
    have := hchar
    infer_instance
  have hAZ : aschbacherSolvableCore p C ⊓ Z = ⊥ := by
    rw [← Subgroup.card_eq_one]
    have h1 : Nat.card ↥(aschbacherSolvableCore p C ⊓ Z) ∣ Nat.card (aschbacherSolvableCore p C) :=
      Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card ↥(aschbacherSolvableCore p C ⊓ Z) ∣ Nat.card Z :=
      Subgroup.card_dvd_of_le inf_le_right
    rcases (hZ.to_le (inf_le_right : aschbacherSolvableCore p C ⊓ Z ≤ Z)).card_eq_or_dvd
      with h | h
    · exact h
    · exact absurd (h.trans h1) hnd
  have hcomm : ⁅aschbacherSolvableCore p C, Z⁆ = ⊥ := by
    rw [eq_bot_iff, ← hAZ]
    exact Subgroup.commutator_le_inf _ _
  have hle : aschbacherSolvableCore p C ≤ centralizer (Z : Set C) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  rcases (hc.to_le hle).card_eq_or_dvd with h | h
  · exact Subgroup.card_eq_one.mp h
  · exact absurd h hnd

theorem aschbacherCore_le_centralizer_of_normal_component {C : Type*} [Group C] [Finite C]
    {p : ℕ} (hp : p.Prime) {D : Subgroup C} [D.Normal] (hD : IsQuasisimple D) :
    aschbacherSolvableCore p C ≤ centralizer (D : Set C) := by
  obtain ⟨hsolv, hchar, -, -⟩ := solvable_prime_complement_core_characterization (H := C) hp
  have hnorm : (aschbacherSolvableCore p C).Normal := by
    have := hchar
    infer_instance
  have hcomp : IsComponent D := ⟨hD, (inferInstance : D.Normal).isSubnormal⟩
  have hcomm := (CFSG.LocalCores.component_solvable_centralizer hsolv
    hnorm.isSubnormal).1 D hcomp
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (by rw [Subgroup.commutator_comm]; exact hcomm)

theorem aschbacherCore_bot_of_normal_component {C : Type*} [Group C] [Finite C] {p : ℕ}
    (hp : p.Prime) {D : Subgroup C} [D.Normal] (hD : IsQuasisimple D)
    (hc : IsPGroup p (centralizer (D : Set C))) : aschbacherSolvableCore p C = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, -, hnd, -⟩ := solvable_prime_complement_core_characterization (H := C) hp
  have hle := aschbacherCore_le_centralizer_of_normal_component hp hD
  rcases (hc.to_le hle).card_eq_or_dvd with h | h
  · exact Subgroup.card_eq_one.mp h
  · exact absurd h hnd

end CFSG.RankThree.PartOne
