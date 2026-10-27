module

public import Mathlib.GroupTheory.Nilpotent
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.PGroups
import CFSG.GH74.GLS.Stage2.Bender.Thm1.Omega1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup

theorem uc22p22r_commutator_top_ne {S : Type*} [Group S] [Group.IsNilpotent S] {N : Subgroup S} (hN : N ≠ ⊥) :
    ⁅N, (⊤ : Subgroup S)⁆ ≠ N := by
  intro h
  have key : ∀ k, N ≤ Subgroup.upperCentralSeries S k → N = ⊥ := by
    intro k
    induction k with
    | zero =>
      intro hk
      rw [Subgroup.upperCentralSeries_zero] at hk
      exact le_bot_iff.1 hk
    | succ k ih =>
      intro hk
      apply ih
      rw [← h]
      exact (Subgroup.commutator_mono hk le_rfl).trans (Subgroup.commutator_upperCentralSeries_top_le S k)
  exact hN (key _ (by rw [Subgroup.upperCentralSeries_nilpotencyClass]; exact le_top))

theorem uc22p22r_le_upperCentralSeries_two {S : Type*} [Group S] [Finite S] {q : ℕ} [hq : Fact q.Prime]
    (hS : IsPGroup q S) {E : Subgroup S} [hEn : E.Normal] (hE : Nat.card ↥E = q ^ 2) :
    E ≤ Subgroup.upperCentralSeries S 2 := by
  haveI : Group.IsNilpotent S := hS.isNilpotent
  set F : Subgroup S := ⁅E, (⊤ : Subgroup S)⁆ with hF
  have hFE : F ≤ E := Subgroup.commutator_le_left E ⊤
  have hEne : E ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hE
    have := hq.out.two_le
    have h4 : 4 ≤ q ^ 2 := by nlinarith
    omega
  have hFcent : F ≤ Subgroup.center S := by
    by_cases hF1 : F = ⊥
    · rw [hF1]
      exact bot_le
    · have hFq : IsPGroup q ↥F := hS.to_subgroup F
      obtain ⟨k, hk⟩ := hFq.exists_card_eq
      have hdvd : q ^ k ∣ q ^ 2 := hk ▸ hE ▸ Subgroup.card_dvd_of_le hFE
      have hk2 : k ≤ 2 := (Nat.pow_dvd_pow_iff_le_right hq.out.one_lt).1 hdvd
      have hFne : F ≠ E := uc22p22r_commutator_top_ne hEne
      have hk1 : k = 1 := by
        interval_cases k
        · exact absurd (Subgroup.eq_bot_of_card_eq F (by simpa using hk)) hF1
        · rfl
        · exact absurd (Subgroup.eq_of_le_of_card_ge hFE (by rw [hE, hk])) hFne
      have hcenter : F ⊓ Subgroup.center S ≠ ⊥ := Group.IsNilpotent.inf_center_ne_bot_of_normal hF1
      have hdvd' : Nat.card ↥(F ⊓ Subgroup.center S) ∣ q := by
        rw [← pow_one q, ← hk1, ← hk]
        exact Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime hq.out).1 hdvd' with h1 | h1
      · exact absurd (Subgroup.eq_bot_of_card_eq _ h1) hcenter
      · have heq : F ⊓ Subgroup.center S = F :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, hk, hk1, pow_one])
        rw [← heq]
        exact inf_le_right
  intro e he
  rw [show (2 : ℕ) = 1 + 1 from rfl, Subgroup.mem_upperCentralSeries_succ_iff, Subgroup.upperCentralSeries_one]
  intro y
  exact hFcent (Subgroup.commutator_mem_commutator he (Subgroup.mem_top y))

theorem uc22p22r_exists_omega_two {X : Type} [Group X] [Finite X] {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (R : Subgroup X) [hRn : R.Normal] (hR : IsPGroup q ↥R) (hnc : ¬ IsCyclic ↥R) :
    ∃ P : Subgroup X, P ≤ R ∧ P.Normal ∧ (∀ x ∈ P, x ^ q = 1) ∧ ⁅⁅P, P⁆, P⁆ = ⊥ ∧ ¬ IsCyclic ↥P ∧
      ∀ x ∈ R, (∀ r ∈ R, x * r = r * x) → x ^ q = 1 → x ∈ P := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  set Z2 : Subgroup X := (Subgroup.upperCentralSeries ↥R 2).map R.subtype with hZ2
  have hZ2R : Z2 ≤ R := Subgroup.map_subtype_le _
  haveI hZ2n : Z2.Normal := inferInstance
  have hcl : ⁅⁅Z2, Z2⁆, Z2⁆ = ⊥ := by
    have h2 : ⁅Subgroup.upperCentralSeries ↥R 2, Subgroup.upperCentralSeries ↥R 2⁆ ≤ Subgroup.center ↥R := by
      rw [← Subgroup.upperCentralSeries_one]
      exact (Subgroup.commutator_mono le_rfl le_top).trans
        (Subgroup.commutator_upperCentralSeries_top_le ↥R 1)
    have h1 : ⁅⁅Subgroup.upperCentralSeries ↥R 2, Subgroup.upperCentralSeries ↥R 2⁆,
        Subgroup.upperCentralSeries ↥R 2⁆ = ⊥ := by
      rw [eq_bot_iff]
      refine (Subgroup.commutator_mono h2 le_top).trans ?_
      rw [(Subgroup.commutator_top_right_eq_bot_iff_le_center).2 le_rfl]
    rw [hZ2, ← Subgroup.map_commutator, ← Subgroup.map_commutator, h1, Subgroup.map_bot]
  obtain ⟨Ω, hΩ⟩ := CFSG.GH74.GLS.Stage2.Bender.Thm1.exists_omega1 hq hq2 hcl
  have hΩZ : Ω ≤ Z2 := fun x hx => ((hΩ x).1 hx).1
  refine ⟨Ω, hΩZ.trans hZ2R, ?_, fun x hx => ((hΩ x).1 hx).2, ?_, ?_, ?_⟩
  ·
    constructor
    intro x hx g
    obtain ⟨hxZ, hxq⟩ := (hΩ x).1 hx
    refine (hΩ _).2 ⟨hZ2n.conj_mem x hxZ g, ?_⟩
    rw [conj_pow, hxq]
    group
  ·
    rw [eq_bot_iff, ← hcl]
    exact Subgroup.commutator_mono (Subgroup.commutator_mono hΩZ hΩZ) hΩZ
  ·
    have hnc' : ¬ IsCyclic ↥(⊤ : Subgroup ↥R) := fun h =>
      hnc (isCyclic_of_surjective (Subgroup.topEquiv : ↥(⊤ : Subgroup ↥R) ≃* ↥R).toMonoidHom
        (MulEquiv.surjective _))
    obtain ⟨E, -, hEn, hEcard, hEexp, -⟩ :=
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.exists_normal_elementary_sq_of_not_isCyclic hq2 hR ⊤
        hnc'
    haveI := hEn
    have hEZ : E ≤ Subgroup.upperCentralSeries ↥R 2 := uc22p22r_le_upperCentralSeries_two hR hEcard
    have hE'Ω : E.map R.subtype ≤ Ω := by
      rintro _ ⟨e, he, rfl⟩
      refine (hΩ _).2 ⟨⟨e, hEZ he, rfl⟩, ?_⟩
      have h1 := hEexp e he
      have h2 := congrArg Subtype.val h1
      simpa using h2
    intro hcyc
    haveI := hcyc
    haveI : IsCyclic ↥(E.map R.subtype) := Subgroup.isCyclic_of_le hE'Ω
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥(E.map R.subtype))
    have hcard' : Nat.card ↥(E.map R.subtype) = q ^ 2 := by
      rw [Subgroup.card_map_of_injective R.subtype_injective]
      exact hEcard
    have hgq : g ^ q = 1 := Subtype.ext (by simpa using ((hΩ _).1 (hE'Ω g.2)).2)
    have hdvd : orderOf g ∣ q := orderOf_dvd_of_pow_eq_one hgq
    rw [hg, hcard'] at hdvd
    have h1 := Nat.le_of_dvd hq.pos hdvd
    nlinarith [hq.two_le]
  ·
    intro x hxR hxc hxq
    have hc : (⟨x, hxR⟩ : ↥R) ∈ Subgroup.center ↥R := by
      rw [Subgroup.mem_center_iff]
      intro r
      exact Subtype.ext (hxc r r.2).symm
    have hc2 : (⟨x, hxR⟩ : ↥R) ∈ Subgroup.upperCentralSeries ↥R 2 :=
      Subgroup.upperCentralSeries_mono ↥R (by norm_num : 1 ≤ 2) (by rw [Subgroup.upperCentralSeries_one]; exact hc)
    exact (hΩ x).2 ⟨⟨⟨x, hxR⟩, hc2, rfl⟩, hxq⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
