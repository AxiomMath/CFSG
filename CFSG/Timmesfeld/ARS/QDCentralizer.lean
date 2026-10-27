module

public import CFSG.Timmesfeld.ARS.QDCenter

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.Timmesfeld.RankOne

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace QD

@[expose] def cmSet (R : Set (Subgroup G)) (D : Subgroup G) : Set (Subgroup G) :=
  {A | A ∈ R ∧ A ≠ D ∧ Commuting A (M R D)}

theorem mem_centralSet_of_mem_cmSet {D A : Subgroup G} (hA : A ∈ cmSet R D) :
    A ∈ centralSet R D :=
  ⟨hA.1, (hA.2.2.mono le_rfl le_M_self).symm⟩

theorem conjSub_mem_cmSet [Finite G] (hR : IsRootClass R) {D A : Subgroup G} (hD : D ∈ R)
    {g : G} (hg : g ∈ Subgroup.normalizer (D : Set G)) (hA : A ∈ cmSet R D) :
    conjSub A g ∈ cmSet R D := by
  refine ⟨hR.conjSub_mem hA.1 g, fun e => hA.2.1 ?_, ?_⟩
  · rw [← conjSub_eq_self_iff.2 hg] at e
    exact map_conj_inj.1 e
  · have := hA.2.2.conjSub g
    rwa [(isPGroup_M hR hD).2.2 g hg] at this

section Centralizer

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) (hnd : IsNondegenerate R)
  (hΩ : ∀ A ∈ R, ∀ B ∈ R, omegaSet R B = omegaSet R A → B = A) {D : Subgroup G} (hD : D ∈ R)
include hR hiso hnd hΩ hD

theorem eq_of_mem_isolatedSet_of_commuting_M {B : Subgroup G} (hB : B ∈ isolatedSet R D)
    (hBM : Commuting B (M R D)) : B = D := by
  by_contra hBD
  obtain ⟨B₁, ⟨hB₁I, hB₁D, hB₁M⟩, hmin⟩ := exists_forall_not_le_commutator (isPGroup_Q hR)
    (P := {B | B ∈ isolatedSet R D ∧ B ≠ D ∧ Commuting B (M R D)}) (fun X hX => le_Q hX.1)
    (fun X hX => hR.ne_bot X hX.1.1.1) ⟨hB, hBD, hBM⟩
  obtain ⟨C, hC, hBC⟩ : ∃ C ∈ isolatedSet R D, ¬ Commuting B₁ C := by
    by_contra! h
    exact hB₁D (eq_of_mem_isolatedSet_of_forall_commuting hR hiso hnd hΩ hD hB₁I h)
  obtain ⟨-, hBCI⟩ := special_of_mem_isolatedSet hR hB₁I hC hBC
  refine hmin _ ⟨hBCI, fun he => ?_, commuting_commutator hB₁M (le_normalizer_M hR hD hC.1)⟩
    (Subgroup.commutator_mono le_rfl (le_Q hC))
  obtain ⟨E', hE', hnc⟩ := exists_mem_lambdaSet_not_commuting hR hiso hD
    (mem_lambdaSet_of_commutator_eq hR hiso hD hB₁I.1.1 hC.1.1 he)
  exact hnc (hB₁M.mono le_rfl (le_M hE'))

theorem notMem_isolatedSet_of_mem_cmSet {A : Subgroup G} (hA : A ∈ cmSet R D) :
    A ∉ isolatedSet R D := fun hI =>
  hA.2.1 (eq_of_mem_isolatedSet_of_commuting_M hR hiso hnd hΩ hD hI hA.2.2)

theorem commutator_notMem_isolatedSet {B X : Subgroup G} (hB : B ∈ cmSet R D)
    (hX : X ∈ centralSet R D) : ⁅B, X⁆ ∉ isolatedSet R D := by
  intro hI
  have he := eq_of_mem_isolatedSet_of_commuting_M hR hiso hnd hΩ hD hI
    (commuting_commutator hB.2.2 (le_normalizer_M hR hD hX))
  obtain ⟨E', hE', hnc⟩ := exists_mem_lambdaSet_not_commuting hR hiso hD
    (mem_lambdaSet_of_commutator_eq hR hiso hD hB.1 hX.1 he)
  exact hnc (hB.2.2.mono le_rfl (le_M hE'))

theorem exists_opposite_of_mem_cmSet {A : Subgroup G} (hA : A ∈ cmSet R D) :
    ∃ B ∈ cmSet R D, B ∈ centralSet R D ∧ Opposite A B := by
  have hAc := mem_centralSet_of_mem_cmSet hA
  obtain ⟨C, hC, hAC⟩ := exists_opposite_of_notMem_isolatedSet hAc
    (notMem_isolatedSet_of_mem_cmSet hR hiso hnd hΩ hD hA)
  obtain ⟨y, hy, hyC⟩ := Sec3.exists_mem_sup_conjSub_eq hR hA.1 hAC
  have hyN : y ∈ Subgroup.normalizer (D : Set G) :=
    sup_le (le_normalizer_of_mem_centralSet hAc) (le_normalizer_of_mem_centralSet hC) hy
  exact ⟨C, hyC ▸ conjSub_mem_cmSet hR hD hyN hA, hC, hAC⟩

theorem notMem_lambdaSet_of_mem_cmSet {A C : Subgroup G} (hA : A ∈ cmSet R D)
    (hC : C ∈ isolatedSet R D) : C ∉ lambdaSet R A := by
  intro hCl
  obtain ⟨B, hB, hBc, hAB⟩ := exists_opposite_of_mem_cmSet hR hiso hnd hΩ hD hA
  have hnc : ¬ Commuting B C := not_commuting_of_opposite_of_mem_lambdaSet hR hB.1 hAB.symm hCl
  have hne : B ≠ C := fun e => hnc (e ▸ hR.commuting_self hB.1)
  have hs : Special R B C := by
    rcases hR.rel B hB.1 C hC.1.1 hne with h | h | h
    · exact absurd h hnc
    · exact absurd h.symm (hC.2 B hBc)
    · exact h
  exact commutator_notMem_isolatedSet hR hiso hnd hΩ hD hB hC.1 (mem_isolatedSet_of_le hR hs.1
    (commutator_le_Q hR (le_normalizer_of_mem_centralSet hBc) (le_Q hC)))

theorem conjSub_mem_cmSet_of_special {A C : Subgroup G} (hA : A ∈ cmSet R D) (hC : C ∈ R)
    (hDC : Special R D C) {c : G} (hc : c ∈ C) : conjSub A c ∈ cmSet R D := by
  by_cases hc1 : c = 1
  · rw [hc1, conjSub_one]
    exact hA
  have hAR := hA.1
  have hAc := mem_centralSet_of_mem_cmSet hA
  have hAC : A ≠ C := fun e => hDC.not_commuting hR (e ▸ hAc.2)
  rcases hR.rel A hAR C hC hAC with hcomm | hop | hs
  · rwa [conjSub_of_forall_commute fun a ha => (hcomm a ha c hc).symm]
  · exfalso
    have h1 := Sec3.commutator_mem_psiSet_of_commuting hR hiso hAR hC hop ⟨hD, hDC.symm⟩ hAc.2.symm
    have hl : ⁅C, D⁆ ∈ lambdaSet R D :=
      mem_lambdaSet_comm hDC.symm.1 (mem_lambdaSet_commutator hR hiso hC hD hDC.symm).2
    exact h1.2.not_commuting hR (hA.2.2.mono le_rfl (le_M hl))
  have hDc : conjSub D c ∈ lambdaSet R D :=
    conjSub_mem_lambdaSet_of_special hR hiso hC hD hDC.symm hc hc1
  have hAcR := hR.conjSub_mem hAR c
  have hAcc : conjSub A c ∈ centralSet R D := ⟨hAcR, commuting_conjSub_of_commuting hR hiso hD hC
    hDC hAc.2 hc hc1 (hA.2.2.mono le_rfl (le_M hDc)).symm⟩
  have hAcl : conjSub A c ∈ lambdaSet R A :=
    conjSub_mem_lambdaSet_of_special hR hiso hC hAR hs.symm hc hc1
  have hAcI : conjSub A c ∉ isolatedSet R D := fun hI =>
    notMem_lambdaSet_of_mem_cmSet hR hiso hnd hΩ hD hA hI hAcl
  by_contra hAcM
  obtain ⟨B, hB, hBc, hAB⟩ := exists_opposite_of_mem_cmSet hR hiso hnd hΩ hD hA
  have hnc : ¬ Commuting B (conjSub A c) :=
    not_commuting_of_opposite_of_mem_lambdaSet hR hB.1 hAB.symm hAcl
  have hΔR : centralSet R D ⊆ R := fun _ h => h.1
  have hΔN : (⨆ X ∈ centralSet R D, X) ≤ Subgroup.normalizer (D : Set G) :=
    iSup₂_le fun _ hY => le_normalizer_of_mem_centralSet hY
  have hΔnorm : ∀ g ∈ (⨆ X ∈ centralSet R D, X), ∀ X ∈ centralSet R D,
      conjSub X g ∈ centralSet R D := fun g hg X hX => conjSub_mem_centralSet hR (hΔN hg) hX
  have hΔcomm : ∀ X ∈ centralSet R D, ∀ Y ∈ centralSet R D, Special R X Y →
      ⁅X, Y⁆ ∈ centralSet R D := fun X hX Y hY hXY =>
    ⟨hXY.1, commuting_iff_le_centralizer.2 (commutator_le_of_le
      (commuting_iff_le_centralizer.1 hX.2) (commuting_iff_le_centralizer.1 hY.2))⟩
  have hBo := exists_opposite_of_notMem_isolatedSet hBc
    (notMem_isolatedSet_of_mem_cmSet hR hiso hnd hΩ hD hB)
  have hAco := exists_opposite_of_notMem_isolatedSet hAcc hAcI
  have hnr : ¬ Relation.ReflTransGen (oppGraph (centralSet R D)) B (conjSub A c) := by
    intro hrt
    obtain ⟨g, hg, hgB⟩ := Sec3.exists_conjSub_eq_of_reflTransGen hR hΔR hrt
    have hle : (⨆ X ∈ {X | Relation.ReflTransGen (oppGraph (centralSet R D)) B X}, X) ≤
        Subgroup.normalizer (D : Set G) := iSup₂_le fun X hX =>
      le_normalizer_of_mem_centralSet (Sec3.mem_and_exists_opposite_of_reflTransGen hBc hBo hX).1
    exact hAcM (hgB ▸ conjSub_mem_cmSet hR hD (hle hg) hB)
  rcases Sec3.commuting_or_commutator_mem_isolatedIn hR hiso hΔR hΔnorm hΔcomm hBc hAcc hBo hAco
    hnr with h | h
  · exact hnc h
  · exact commutator_notMem_isolatedSet hR hiso hnd hΩ hD hB hAcc h

end Centralizer

end QD

open QD

theorem setOf_commuting_M_eq_singleton [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    (hnd : IsNondegenerate R) (hΩ : ∀ A ∈ R, ∀ B ∈ R, omegaSet R B = omegaSet R A → B = A)
    {D : Subgroup G} (hD : D ∈ R) : {B | B ∈ R ∧ Commuting B (M R D)} = {D} := by
  ext B
  refine ⟨fun ⟨hB, hBM⟩ => ?_, fun h => ?_⟩
  swap
  · rw [Set.mem_singleton_iff] at h
    subst h
    exact ⟨hD, commuting_M hR hD⟩
  rw [Set.mem_singleton_iff]
  by_contra hBD
  set H := stabSet (cmSet R D) with hH
  have hNH : Subgroup.normalizer (D : Set G) ≤ H := fun g hg =>
    mem_stabSet_of_forall (fun A hA => conjSub_mem_cmSet hR hD hg hA)
      (fun A hA => conjSub_mem_cmSet hR hD (Subgroup.inv_mem _ hg) hA)
  have hΨH : ∀ C ∈ R, Special R D C → C ≤ H := fun C hC hDC c hc =>
    mem_stabSet_of_mul_self (hR.mul_self C hC c hc) fun A hA =>
      conjSub_mem_cmSet_of_special hR hiso hnd hΩ hD hA hC hDC hc
  obtain ⟨E₁, hE₁, F₁, hF₁, hs₁⟩ := id hnd
  obtain ⟨g, hg⟩ := hR.exists_conjSub_eq hE₁ hD
  have hFR := hR.conjSub_mem hF₁ g
  have hDF : Special R D (conjSub F₁ g) := by
    have := Sec3.special_conjSub hR hs₁ g
    rwa [hg] at this
  obtain ⟨f, hf, hf1⟩ := hR.exists_ne_one hFR
  have hfH : f ∈ H := hΨH _ hFR hDF hf
  have hD'l : conjSub D f ∈ lambdaSet R D :=
    conjSub_mem_lambdaSet_of_special hR hiso hFR hD hDF.symm hf hf1
  have hD'R : conjSub D f ∈ R := hR.conjSub_mem hD f
  obtain ⟨Y, hY, hYn⟩ := Set.not_subset.1
    (not_subset_centralSet_union_psiSet hR hiso hD'R (mem_lambdaSet_comm hD hD'l))
  have hYR : Y ∈ R := by rcases hY with h | h <;> exact h.1
  have hDY : Opposite D Y := by
    have hne : D ≠ Y := fun e => hYn (Or.inl ⟨hYR, e ▸ hR.commuting_self hD⟩)
    rcases hR.rel D hD Y hYR hne with h | h | h
    · exact absurd (Or.inl ⟨hYR, h⟩) hYn
    · exact h
    · exact absurd (Or.inr ⟨hYR, h⟩) hYn
  have hDff : conjSub (conjSub D f) f⁻¹ = D := by
    rw [← conjSub_mul, inv_mul_cancel, conjSub_one]
  have hY'H : conjSub Y f⁻¹ ≤ H := by
    rcases hY with hYc | hYs
    · have := hYc.2.conjSub f⁻¹
      rw [hDff] at this
      exact (commuting_iff_le_centralizer.1 this).trans
        ((Subgroup.centralizer_le_normalizer _).trans hNH)
    · have := Sec3.special_conjSub hR hYs.2 f⁻¹
      rw [hDff] at this
      exact hΨH _ (hR.conjSub_mem hYR _) this
  have hYH : Y ≤ H := by
    intro y hy
    have h1 := H.mul_mem (H.mul_mem hfH (hY'H (conj_mem_conjSub f⁻¹ hy))) (H.inv_mem hfH)
    rwa [show f * (f⁻¹ * y * f⁻¹⁻¹) * f⁻¹ = y by group] at h1
  have hle : gen (lambdaSet R D) ⊔ Y ≤ H :=
    sup_le (gen_le fun X hX => (le_normalizer_of_mem_centralSet ⟨hX.1.1, hX.1.2.2⟩).trans hNH) hYH
  rw [gen_lambdaSet_sup_eq_top_of hR hiso hnd hD ⟨hYR, hDY⟩] at hle
  obtain ⟨g', hg'⟩ := hR.exists_conjSub_eq hB hD
  have := conjSub_mem_of_mem_stabSet (hle (Subgroup.mem_top g')) (⟨hB, hBD, hBM⟩ : B ∈ cmSet R D)
  rw [hg'] at this
  exact this.2.1 rfl

end CFSG.Timmesfeld.ARS
