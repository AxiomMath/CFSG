module

public import CFSG.RankThree.PartOne.S11.FivePlusAction
public import CFSG.RankThree.GroupTheory.SteinbergCEThetaQuotientAction
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.RankThree.GroupTheory.SteinbergBMSimplePlaneFixedTwoCommutator

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Blueprint CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

@[expose] def CatalogPrimeTwoAutomorphismsInner : Prop :=
  ∀ (J : Type) [Group J] [Finite J], CFSG.IsQuasisimple J → Catalog (J ⧸ Subgroup.center J) →
    ∀ (p : ℕ) (P Q : Subgroup (MulAut J)), p.Prime → 3 < p → IsPGroup p P → IsPGroup 2 Q →
      P ≤ Subgroup.normalizer (Q : Set (MulAut J)) → ⁅Q, P⁆ = Q →
      Q ≤ (MulAut.conj : J →* MulAut J).range

variable {H : Type} [Group H] [Finite H]

theorem exists_two_commutator_in_thetaComponent {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hK : CatalogPrimeTwoAutomorphismsInner) {L A Q : Subgroup H}
    (hAL : A ≤ normalizer (L : Set H)) (hQL : Q ≤ normalizer (L : Set H)) (hA : IsPGroup p A)
    (hQ2 : IsPGroup 2 Q) (hAQ : A ≤ normalizer (Q : Set H)) (hQA : ⁅Q, A⁆ = Q)
    (hLq : CFSG.IsQuasisimple (L ⧸ aschbacherSolvableCore p L))
    (hcat : Catalog ((L ⧸ aschbacherSolvableCore p L) ⧸
      Subgroup.center (L ⧸ aschbacherSolvableCore p L)))
    (hmove : ∃ q : Q, thetaQuotientAction p hQL q ≠ 1) :
    ∃ T : Subgroup H, T ≤ L ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧ A ≤ normalizer (T : Set H) ∧
      ⁅T, A⁆ = T := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨-, hNchar, hNp, -⟩ := solvable_prime_complement_core_characterization (H := ↥L) hp
  set N := aschbacherSolvableCore p L with hN
  have : N.Normal := inferInstance
  let _ : MulDistribMulAction A L := conjActionOn hAL
  have hinv : CFSG.IsInvariant A L N := CFSG.isInvariant_of_characteristic N
  have h2A : ¬ 2 ∣ Nat.card A := by
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hA
    rw [hj]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
      (Nat.prime_two.dvd_of_dvd_pow h)).symm
  set Γ := normalizer (L : Set H) with hΓ
  set Φ := thetaQuotientConj p L with hΦ
  have hact : ∀ (a : A) (x : L ⧸ N),
      MulDistribMulAction.toMulAut A (L ⧸ N) a x = Φ ⟨a, hAL a.2⟩ x := by
    intro a x
    induction x using QuotientGroup.induction_on with
    | H l =>
      change a • ((l : L) : L ⧸ N) = _
      rw [MulAction.Quotient.smul_mk, hΦ, thetaQuotientConj_mk]
      rfl
  set Qa : Subgroup (MulAut (L ⧸ N)) := (Q.subgroupOf Γ).map Φ with hQa
  set P : Subgroup (MulAut (L ⧸ N)) := (A.subgroupOf Γ).map Φ with hP
  have hPrange : (MulDistribMulAction.toMulAut A (L ⧸ N)).range = P := by
    ext σ
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨⟨a, hAL a.2⟩, Subgroup.mem_subgroupOf.mpr a.2, ?_⟩
      ext x
      exact (hact a x).symm
    · rintro ⟨g, hg, rfl⟩
      refine ⟨⟨g, Subgroup.mem_subgroupOf.mp hg⟩, ?_⟩
      ext x
      exact hact ⟨g, Subgroup.mem_subgroupOf.mp hg⟩ x
  have hP' : IsPGroup p P := (hA.comap_subtype).map Φ
  have hQ2' : IsPGroup 2 Qa := (hQ2.comap_subtype).map Φ
  have hPQ : P ≤ normalizer (Qa : Set (MulAut (L ⧸ N))) := by
    have h1 : A.subgroupOf Γ ≤ normalizer (Q.subgroupOf Γ : Set Γ) := by
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro h
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_normalizer_iff.mp (hAQ (Subgroup.mem_subgroupOf.mp hx)) (h : H)
    exact (Subgroup.map_mono h1).trans (Subgroup.le_normalizer_map Φ)
  have hQA' : ⁅Q.subgroupOf Γ, A.subgroupOf Γ⁆ = Q.subgroupOf Γ := by
    apply Subgroup.map_injective Γ.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hQL,
      Subgroup.map_subgroupOf_eq_of_le hAL]
    exact hQA
  have hQP : ⁅Qa, P⁆ = Qa := by
    rw [hQa, hP, ← Subgroup.map_commutator, hQA']
  have hinn : Qa ≤ (MulAut.conj : (L ⧸ N) →* MulAut (L ⧸ N)).range :=
    hK (L ⧸ N) hLq hcat p P Qa hp hp3 hP' hQ2' hPQ hQP
  have hQa1 : Qa ≠ ⊥ := by
    obtain ⟨q, hq⟩ := hmove
    intro h
    have h1 : Φ ⟨q, hQL q.2⟩ ∈ Qa := Subgroup.mem_map_of_mem Φ (Subgroup.mem_subgroupOf.mpr q.2)
    rw [h, Subgroup.mem_bot] at h1
    exact hq h1
  obtain ⟨E, hE1, hE2, hEinv, hEE⟩ := exists_invariant_two_commutator_of_inner_action h2A hQ2'
    hQa1 hinn (hPrange ▸ hPQ) (hPrange ▸ hQP)
  obtain ⟨T', -, hT'1, hT'2, hT'inv, hT'A, -⟩ :=
    SteinbergBM.coprime_two_commutator_lifts_through_invariant_supplement hp hp2 hA N hNp ⊤
      (fun _ _ _ => Subgroup.mem_top _) (top_sup_eq N) E hE1 hE2 hEinv hEE
  set T := T'.map L.subtype with hT
  have hfwd : ∀ a ∈ A, ∀ g ∈ T, a * g * a⁻¹ ∈ T := by
    rintro a ha _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_map.mpr ⟨((⟨a, ha⟩ : A) • x), hT'inv ⟨a, ha⟩ x hx, rfl⟩
  refine ⟨T, Subgroup.map_subtype_le _, ?_, hT'2.map _, le_normalizer_of_conj_mem_forall hfwd, ?_⟩
  · intro h
    exact hT'1 ((Subgroup.map_eq_bot_iff_of_injective T' L.subtype_injective).mp h)
  · rw [← SteinbergBM.map_actionCommutator_conj hAL T', hT'A]

end CFSG.RankThree.PartOne
