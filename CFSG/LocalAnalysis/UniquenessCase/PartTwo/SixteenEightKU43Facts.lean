module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKInputs
import CFSG.Quasithin.H13.A7SectionRank
import CFSG.GroupTheory.PRankBound
public import CFSG.GH74.Orders.LieType
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryModelOuterTwoPart
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

private theorem s16k_card_of_elemAbelianOfRank {A : Type} [Group A] {p r : ℕ}
    (hp : p.Prime) (h : IsElemAbelianOfRank p r A) : Nat.card A = p ^ r := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  simp [Nat.card_eq_fintype_card]

private theorem s16k_isPGroup_of_elemAbelianOfRank {A : Type} [Group A] {p r : ℕ}
    (hp : p.Prime) (h : IsElemAbelianOfRank p r A) : IsPGroup p A := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact IsPGroup.of_card (s16k_card_of_elemAbelianOfRank hp h)

private theorem s16k_not_isCyclic_of_elemAbelianOfRank {A : Type} [Group A] {p r : ℕ}
    (hp : p.Prime) (hr : 2 ≤ r) (h : IsElemAbelianOfRank p r A) : ¬ IsCyclic A := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := h
  intro hc
  have hc' : IsCyclic (Multiplicative (Fin r → ZMod p)) := e.isCyclic.1 hc
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Multiplicative (Fin r → ZMod p))
  have hord : orderOf g = p ^ r := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card]
    simp
  have hg1 : g ^ p = 1 := by
    have h0 : p • (Multiplicative.toAdd g) = 0 := by
      funext i
      simp [nsmul_eq_mul]
    calc g ^ p = Multiplicative.ofAdd (p • Multiplicative.toAdd g) := rfl
      _ = 1 := by rw [h0]; rfl
  have hdvd : p ^ r ∣ p := hord ▸ orderOf_dvd_of_pow_eq_one hg1
  have hle : p ^ r ≤ p := Nat.le_of_dvd hp.pos hdvd
  have h2 : p ^ 2 ≤ p ^ r := Nat.pow_le_pow_right hp.pos hr
  nlinarith [hp.two_le]

private theorem s16k_not_isCyclic_of_elemAbelian {A : Type} [Group A] [Finite A] {p : ℕ}
    (hp : p.Prime) {C : Subgroup A} (hC : IsElemAbelian p C) (hcard : p ^ 2 ≤ Nat.card C) :
    ¬ IsCyclic ↥C := by
  intro hcyc
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hord : orderOf g = Nat.card C := orderOf_eq_card_of_forall_mem_zpowers hg
  have hgp : g ^ p = 1 := Subtype.ext (by simpa using hC.2 g g.2)
  have hle : orderOf g ≤ p := Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hgp)
  rw [hord] at hle
  nlinarith [hp.two_le]

private theorem s16k_exists_nc_of_sub {W : Type} [Group W] {p : ℕ} {H X : Subgroup (MulAut W)}
    {w : W} (hXH : X ≤ H) (hXstab : X ≤ MulAction.stabilizer (MulAut W) w)
    {B₀ : Subgroup X} (hB₀p : IsPGroup p ↥B₀) (hB₀nc : ¬ IsCyclic ↥B₀) :
    ∃ B : Subgroup (MulAut W), B ≤ H ∧ IsPGroup p ↥B ∧ ¬ IsCyclic ↥B ∧
      ∀ b ∈ B, b w = w := by
  refine ⟨B₀.map X.subtype, ?_, ?_, ?_, ?_⟩
  · rintro b ⟨b₀, hb₀, rfl⟩
    exact hXH b₀.2
  · exact hB₀p.map X.subtype
  · intro hcyc
    exact hB₀nc
      ((Subgroup.equivMapOfInjective B₀ X.subtype X.subtype_injective).isCyclic.mpr hcyc)
  · rintro b ⟨b₀, hb₀, rfl⟩
    simpa using MulAction.mem_stabilizer_iff.mp (hXstab b₀.2)

theorem s16k_u43_noncyclic3_of_table (hT : S16kU43Table) {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {H : Subgroup (MulAut W)}
    (hS : ∃ S : Type, ∃ _ : Group S, CFSG.Blueprint.LieModel S .PSU 4 3 1 ∧ IsHat ↥H S)
    (hrk : rk ↥(⊤ : Subgroup W) = 12) (hirr : IsIrrOn H ⊤ ⊥) :
    ∀ w : W, w ≠ 1 → ∃ B : Subgroup (MulAut W), B ≤ H ∧ IsPGroup 3 ↥B ∧ ¬ IsCyclic ↥B ∧
      ∀ b ∈ B, b w = w := by
  intro w hw
  let X : Subgroup (MulAut W) := ptCent H w
  have hXH : X ≤ H := inf_le_left
  have hXstab : X ≤ MulAction.stabilizer (MulAut W) w := inf_le_right
  rcases hT W hW H hS hrk hirr w hw with hU42 | hA5 | hA6
  ·
    change CFSG.Blueprint.LieModel ↥X .PSU 4 2 1 at hU42
    have hrank : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
      obtain ⟨-, K, hKfield, hKfinite, hKcard, ⟨e⟩⟩ :=
        CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hU42
      letI : Field K := hKfield
      letI : Finite K := hKfinite
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hdiag := CFSG.SectionRank.OddCover.scalar_quotient_diagonal_torus_rank
        (K := K) (p := 2) (f := 1) (n := 4) (r := 3)
        Nat.prime_two (by norm_num) (by norm_num : (3 : ℕ) ≠ 2)
        (H := StatedSU 4 2 K)
        (Or.inr ⟨hKcard, rfl, by norm_num⟩)
        ((StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 2 K)) le_rfl
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (show 1 < 3 by norm_num) e]
      have h4 := hdiag.1
      norm_num at h4
      exact h4
    obtain ⟨E, -, hEab, hEcard⟩ :=
      CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (⊤ : Subgroup X)
    refine s16k_exists_nc_of_sub (p := 3) hXH hXstab (IsPGroup.of_card hEcard) ?_
    exact s16k_not_isCyclic_of_elemAbelian Nat.prime_three hEab
      (hEcard ▸ Nat.pow_le_pow_right (by norm_num) hrank)
  ·
    change IsE81A5 ↥X at hA5
    obtain ⟨N, -, hNab, -⟩ := hA5
    exact s16k_exists_nc_of_sub (p := 3) hXH hXstab
      (s16k_isPGroup_of_elemAbelianOfRank Nat.prime_three hNab)
      (s16k_not_isCyclic_of_elemAbelianOfRank Nat.prime_three (by norm_num) hNab)
  ·
    change IsE16A6 ↥X at hA6
    obtain ⟨N, hNnormal, hNab, halt⟩ := hA6
    have hNcard : Nat.card ↥N = 2 ^ 4 := s16k_card_of_elemAbelianOfRank Nat.prime_two hNab
    have hN3 : ¬ 3 ∣ Nat.card ↥N := by rw [hNcard]; norm_num
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    haveI : N.Normal := hNnormal
    have hquot := CFSG.SectionRank.pRank_quotient_eq (p := 3) N hN3
    have hA6rank : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (alternatingGroup (Fin 6))) := by
      have h : CFSG.Open.pRank 3 (⊤ : Subgroup (alternatingGroup (Fin 6))) = 2 :=
        (CFSG.Quasithin.H13.A7.section_rank_alternating_odd_prime_rank).2.1
      rw [h]
    have hrank : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
      rw [← hquot]
      obtain ⟨e⟩ := halt
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (show 1 < 3 by norm_num) e]
      exact hA6rank
    obtain ⟨E, -, hEab, hEcard⟩ :=
      CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (⊤ : Subgroup X)
    refine s16k_exists_nc_of_sub (p := 3) hXH hXstab (IsPGroup.of_card hEcard) ?_
    exact s16k_not_isCyclic_of_elemAbelian Nat.prime_three hEab
      (hEcard ▸ Nat.pow_le_pow_right (by norm_num) hrank)

theorem s16kU43Noncyclic3_of_table (hT : S16kU43Table) : S16kU43Noncyclic3 :=
  fun _ _ _ hW _ hS hrk hirr => s16k_u43_noncyclic3_of_table hT hW hS hrk hirr

theorem s16k_u43_noncyclic3 (hT : S16kU43Noncyclic3) {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {H : Subgroup (MulAut W)}
    (hS : ∃ S : Type, ∃ _ : Group S, CFSG.Blueprint.LieModel S .PSU 4 3 1 ∧ IsHat ↥H S)
    (hrk : rk ↥(⊤ : Subgroup W) = 12) (hirr : IsIrrOn H ⊤ ⊥) :
    ∀ w : W, w ≠ 1 → ∃ B : Subgroup (MulAut W), B ≤ H ∧ IsPGroup 3 ↥B ∧ ¬ IsCyclic ↥B ∧
      ∀ b ∈ B, b w = w :=
  hT W hW H hS hrk hirr

private theorem s16k_finite_of_lieModel_u43 {S : Type} [Group S]
    (h : CFSG.Blueprint.LieModel S .PSU 4 3 1) : Finite S := by
  obtain ⟨-, K, hKfield, hKfinite, -, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) h
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  exact Finite.of_injective e.toEquiv e.toEquiv.injective

private theorem s16k_card_outer_u43 {S : Type} [Group S]
    (h : CFSG.Blueprint.LieModel S .PSU 4 3 1) :
    Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) ∣ 2 ^ 3 := by
  have hcl : StatedClassicalModel S .PSU 4 3 1 := h.statedClassicalModel (by decide)
  have hcard :=
    (CFSG.LocalAnalysis.ComponentInitial.unitary_model_outer_two_part_bound S 4 3 1 hcl).2.2.1
  norm_num at hcard
  rw [hcard]
  norm_num

private theorem s16k_card_mulAut_dvd {S : Type} [Group S] [Finite S]
    (hout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) ∣ 2 ^ 3) :
    Nat.card (MulAut S) ∣ Nat.card S * 2 ^ 3 := by
  have hinner : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner S) ∣
      Nat.card S := by
    unfold CFSG.ComponentClassification.OuterAutomorphisms.inner
    exact Subgroup.card_range_dvd _
  rw [← Subgroup.card_mul_index
    (CFSG.ComponentClassification.OuterAutomorphisms.inner S), Subgroup.index_eq_card]
  exact mul_dvd_mul hinner hout

private theorem s16k_not_dvd_sq_u43 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ p ^ 2 ∣ (2 ^ 7 * 3 ^ 6 * 5 * 7) * 2 ^ 3 := by
  have heq : (2 ^ 7 * 3 ^ 6 * 5 * 7) * 2 ^ 3 = 2 ^ 10 * 3 ^ 6 * 5 * 7 := by norm_num
  rw [heq]
  intro h
  have hpdvd : p ∣ 2 ^ 10 * 3 ^ 6 * 5 * 7 := (dvd_pow_self p (by norm_num)).trans h
  rcases (Nat.Prime.dvd_mul hp).1 hpdvd with h1 | h7
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h23 | h5
    · rcases (Nat.Prime.dvd_mul hp).1 h23 with h2 | h3
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2)
        omega
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3)
        omega
    · have hp5' : p = 5 := le_antisymm (Nat.le_of_dvd (by norm_num) h5) hp5
      subst hp5'
      norm_num at h
  · have hp7 : p ≤ 7 := Nat.le_of_dvd (by norm_num) h7
    rcases (by omega : p = 5 ∨ p = 6 ∨ p = 7) with rfl | rfl | rfl
    · norm_num at h
    · norm_num at hp
    · norm_num at h

theorem s16k_pRank_aut_u43 {X : Type} [Group X] [Finite X] {S : Type} [Group S]
    (hS : CFSG.Blueprint.LieModel S .PSU 4 3 1) (hX : IsHat X S) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) : CFSG.Open.pRank p (⊤ : Subgroup (MulAut X)) ≤ 1 := by
  haveI : Finite S := s16k_finite_of_lieModel_u43 hS
  obtain ⟨hquasi, -, ⟨e⟩⟩ := hX
  haveI : Group.IsPerfect X := hquasi.1
  have hinj : Function.Injective
      ((MulAut.congr e).toMonoidHom.comp
        (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom X)) :=
    (MulAut.congr e).injective.comp
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective X)
  refine (CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt _ hinj).trans ?_
  have hcardS : Nat.card S = 2 ^ 7 * 3 ^ 6 * 5 * 7 := by
    rw [CFSG.GH74.card_of_lieModel_PSU (n := 4) (p := 3) (f := 1)
      (by norm_num) (by norm_num) hS]
    decide
  have hnot : ¬ p ^ (1 + 1) ∣ Nat.card (⊤ : Subgroup (MulAut S)) := by
    rw [Subgroup.card_top]
    intro hdiv
    refine s16k_not_dvd_sq_u43 hp hp5 (hcardS ▸ ?_)
    exact hdiv.trans (s16k_card_mulAut_dvd (s16k_card_outer_u43 hS))
  exact CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ hp hnot

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
