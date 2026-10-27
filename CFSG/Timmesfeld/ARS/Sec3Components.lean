module

public import CFSG.Timmesfeld.ARS.BasicLines
public import CFSG.Timmesfeld.ARS.Sec3Natural

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.Timmesfeld.RankOne

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

abbrev oppGraph (Δ : Set (Subgroup G)) (C D : Subgroup G) : Prop :=
  C ∈ Δ ∧ D ∈ Δ ∧ Opposite C D

@[expose] def isolatedIn (Δ : Set (Subgroup G)) : Set (Subgroup G) :=
  {B | B ∈ Δ ∧ ∀ C ∈ Δ, ¬ Opposite B C}

namespace Sec3

theorem oppGraph_symm {Δ : Set (Subgroup G)} {C D : Subgroup G} (h : oppGraph Δ C D) :
    oppGraph Δ D C :=
  ⟨h.2.1, h.1, h.2.2.symm⟩

theorem reflTransGen_oppGraph_symm {Δ : Set (Subgroup G)} {C D : Subgroup G}
    (h : Relation.ReflTransGen (oppGraph Δ) C D) : Relation.ReflTransGen (oppGraph Δ) D C := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (oppGraph_symm hbc) ih

theorem mem_and_exists_opposite_of_reflTransGen {Δ : Set (Subgroup G)} {A C : Subgroup G}
    (hA : A ∈ Δ) (hAo : ∃ D ∈ Δ, Opposite A D)
    (h : Relation.ReflTransGen (oppGraph Δ) A C) : C ∈ Δ ∧ ∃ D ∈ Δ, Opposite C D := by
  induction h with
  | refl => exact ⟨hA, hAo⟩
  | tail _ hbc _ => exact ⟨hbc.2.1, _, hbc.1, hbc.2.2.symm⟩

theorem exists_mem_sup_conjSub_eq (hR : IsRootClass R) {C D : Subgroup G} (hC : C ∈ R)
    (h : Opposite C D) : ∃ y ∈ C ⊔ D, conjSub C y = D := by
  obtain ⟨c, hc, hc1⟩ := hR.exists_ne_one hC
  obtain ⟨d, hd, -, hcd⟩ := h.2.1 c hc hc1
  refine ⟨c⁻¹ * d, Subgroup.mul_mem _ (Subgroup.mem_sup_left (C.inv_mem hc))
    (Subgroup.mem_sup_right hd), ?_⟩
  rw [conjSub_mul, hcd, ← conjSub_mul, inv_mul_cancel, conjSub_one]

theorem eq_one_of_conjSub_eq_of_mem_commutator [Finite G] (hR : IsRootClass R)
    (hiso : NoIsolated R) {A B C : Subgroup G} (hA : A ∈ R) (hB : B ∈ R) (hAB : Opposite A B)
    (hAC : C ∈ lambdaSet R A) (hBC : C ∈ psiSet R B) {d : G} (hd : d ∈ ⁅B, C⁆)
    (h : conjSub A d = A) : d = 1 := by
  have hCR : C ∈ R := hAC.1.1
  have hdN : d ∈ C ⊔ ⁅B, C⁆ := Subgroup.mem_sup_right hd
  have hcomm : ∀ a ∈ A, Commute a d := by
    intro a ha
    have h1 : ⁅a, d⁆ ∈ C := commutatorElement_mem_of_mem_sup hR hiso hA hB hAB hAC hBC ha hdN
    have h2 : ⁅a, d⁆ ∈ A := by
      have e : ⁅a, d⁆ = a * (d * a⁻¹ * d⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e]
      refine A.mul_mem ha ?_
      have := conj_mem_conjSub d (A.inv_mem ha)
      rwa [h] at this
    have h3 : ⁅a, d⁆ ∈ A ⊓ C := ⟨h2, h1⟩
    rw [inf_eq_bot hR hiso hA hCR hAC.1.2.1.symm, Subgroup.mem_bot,
      commutatorElement_eq_one_iff_mul_comm] at h3
    exact h3
  have hdC := mem_of_forall_commute_of_mem_sup hR hiso hA hB hAB hAC hBC hdN hcomm
  have hne : C ≠ ⁅B, C⁆ := by
    have := hBC.2.symm.ne_commutator hR
    rwa [Subgroup.commutator_comm] at this
  have hmem : d ∈ C ⊓ ⁅B, C⁆ := ⟨hdC, hd⟩
  rwa [inf_eq_bot hR hiso hCR hBC.2.1 hne, Subgroup.mem_bot] at hmem

theorem commutator_le_iSup {Δ : Set (Subgroup G)} {B C : Subgroup G} (hB : B ∈ Δ)
    (hC : C ∈ Δ) : ⁅B, C⁆ ≤ ⨆ X ∈ Δ, X := by
  have hBle : B ≤ ⨆ X ∈ Δ, X := le_iSup₂ (f := fun X (_ : X ∈ Δ) => X) B hB
  have hCle : C ≤ ⨆ X ∈ Δ, X := le_iSup₂ (f := fun X (_ : X ∈ Δ) => X) C hC
  rw [Subgroup.commutator_le]
  intro b hb c hc
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hBle hb) (hCle hc))
    (Subgroup.inv_mem _ (hBle hb))) (Subgroup.inv_mem _ (hCle hc))

section Components

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) {Δ : Set (Subgroup G)}
  (hΔR : Δ ⊆ R) (hΔnorm : ∀ g ∈ (⨆ B ∈ Δ, B), ∀ B ∈ Δ, conjSub B g ∈ Δ)

include hR hiso hΔR hΔnorm in
theorem reflTransGen_of_mem_lambdaSet {A B : Subgroup G} (hA : A ∈ Δ) (hB : B ∈ Δ)
    (hBl : B ∈ lambdaSet R A) (hAo : ∃ C ∈ Δ, Opposite A C) (hBo : ∃ D ∈ Δ, Opposite B D) :
    Relation.ReflTransGen (oppGraph Δ) A B := by
  by_contra hAB
  obtain ⟨C, hCΔ, hAC⟩ := hAo
  obtain ⟨D, hDΔ, hBD⟩ := hBo
  have hAR := hΔR hA
  have hBR := hΔR hB
  have hCR := hΔR hCΔ
  have hDR := hΔR hDΔ
  have hAl : A ∈ lambdaSet R B := mem_lambdaSet_comm hAR hBl
  have hBp : B ∈ psiSet R C := by
    refine ⟨hBR, ?_⟩
    have hnc : ¬ Commuting C B := not_commuting_of_opposite_of_mem_lambdaSet hR hCR hAC.symm hBl
    have hno : ¬ Opposite C B := fun h => hAB (Relation.ReflTransGen.tail
      (Relation.ReflTransGen.single ⟨hA, hCΔ, hAC⟩) ⟨hCΔ, hB, h⟩)
    have hne : C ≠ B := fun e => hAB (Relation.ReflTransGen.single ⟨hA, hB, e ▸ hAC⟩)
    rcases hR.rel C hCR B hBR hne with h | h | h
    · exact absurd h hnc
    · exact absurd h hno
    · exact h
  have hAp : A ∈ psiSet R D := by
    refine ⟨hAR, ?_⟩
    have hnc : ¬ Commuting D A := not_commuting_of_opposite_of_mem_lambdaSet hR hDR hBD.symm hAl
    have hno : ¬ Opposite D A := fun h => hAB (reflTransGen_oppGraph_symm
      (Relation.ReflTransGen.tail (Relation.ReflTransGen.single ⟨hB, hDΔ, hBD⟩) ⟨hDΔ, hA, h⟩))
    have hne : D ≠ A := fun e => hAB (reflTransGen_oppGraph_symm
      (Relation.ReflTransGen.single ⟨hB, hA, e ▸ hBD⟩))
    rcases hR.rel D hDR A hAR hne with h | h | h
    · exact absurd h hnc
    · exact absurd h hno
    · exact h
  obtain ⟨b', hb', hb'1⟩ := hR.exists_ne_one hBp.2.1
  have hb'Δ : b' ∈ ⨆ X ∈ Δ, X := commutator_le_iSup hCΔ hB hb'
  have hPΔ : conjSub A b' ∈ Δ := hΔnorm b' hb'Δ A hA
  have hAP : Relation.ReflTransGen (oppGraph Δ) A (conjSub A b') := by
    have hCb : conjSub C b' = C := conjSub_of_forall_commute fun c hc => hBp.2.2.1 b' hb' c hc
    have hop : Opposite (conjSub A b') C := by
      have := Opposite.conj hAC b'
      rwa [hCb] at this
    exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single ⟨hA, hCΔ, hAC⟩)
      ⟨hCΔ, hPΔ, hop.symm⟩
  have hS := setOf_mem_le_sup_eq hR hiso hAR hCR hAC hBl hBp
  have hPmem : conjSub A b' ∈ {E | E ∈ R ∧ E ≤ A ⊔ B} := by
    rw [hS]
    exact Or.inr ⟨⟨b', Subgroup.mem_sup_right hb'⟩, rfl⟩
  have hPA : conjSub A b' ≠ A := fun h =>
    hb'1 (eq_one_of_conjSub_eq_of_mem_commutator hR hiso hAR hCR hAC hBl hBp hb' h)
  have hS' := setOf_mem_le_sup_eq hR hiso hBR hDR hBD hAl hAp
  have hPmem' : conjSub A b' ∈ {E | E ∈ R ∧ E ≤ B ⊔ A} := ⟨hPmem.1, sup_comm A B ▸ hPmem.2⟩
  rw [hS'] at hPmem'
  rcases hPmem' with hPA' | ⟨⟨m, hm⟩, hPm⟩
  · exact hPA hPA'
  obtain ⟨a, ha, a'', ha'', rfl⟩ := (mem_sup_commutator_iff hAp).1 hm
  have hN := commuting_sup_commutator hR hAl hAp
  have hPm' : conjSub B a'' = conjSub A b' := by
    rw [← hPm]
    change conjSub B a'' = conjSub B (a * a'')
    rw [(hN a (Subgroup.mem_sup_left ha) a'' (Subgroup.mem_sup_right ha'')).eq, conjSub_mul,
      conjSub_of_forall_commute fun x hx => (hAl.1.2.2 x hx a ha).symm]
  have hBP : Relation.ReflTransGen (oppGraph Δ) B (conjSub A b') := by
    have hDa : conjSub D a'' = D := conjSub_of_forall_commute fun x hx => hAp.2.2.1 a'' ha'' x hx
    have hop : Opposite (conjSub A b') D := by
      have := Opposite.conj hBD a''
      rwa [hDa, hPm'] at this
    exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single ⟨hB, hDΔ, hBD⟩)
      ⟨hDΔ, hPΔ, hop.symm⟩
  exact hAB (hAP.trans (reflTransGen_oppGraph_symm hBP))

include hR hiso hΔR hΔnorm in
theorem reflTransGen_conjSub_of_mem {C X : Subgroup G} (hC : C ∈ Δ)
    (hCo : ∃ D ∈ Δ, Opposite C D) (hX : X ∈ Δ) {x : G} (hx : x ∈ X) :
    Relation.ReflTransGen (oppGraph Δ) C (conjSub C x) := by
  have hCR := hΔR hC
  have hXR := hΔR hX
  have hxΔ : x ∈ ⨆ B ∈ Δ, B := le_iSup₂ (f := fun B (_ : B ∈ Δ) => B) X hX hx
  have hCxΔ : conjSub C x ∈ Δ := hΔnorm x hxΔ C hC
  by_cases hCX : C = X
  · subst hCX
    rw [conjSub_of_mem hx]
  rcases hR.rel C hCR X hXR hCX with hc | hop | hsp
  · rw [conjSub_of_forall_commute fun c hc' => (hc c hc' x hx).symm]
  · have hop' : Opposite (conjSub C x) X := by
      have := Opposite.conj hop x
      rwa [conjSub_of_mem hx] at this
    exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single ⟨hC, hX, hop⟩)
      ⟨hX, hCxΔ, hop'.symm⟩
  · by_cases hCx : conjSub C x = C
    · rw [hCx]
    have hER : ⁅C, X⁆ ∈ R := hsp.1
    have hle : conjSub C x ≤ ⁅C, X⁆ ⊔ C := conjSub_le_commutator_sup hx
    have hcomm : Commuting (⁅C, X⁆ ⊔ C) (⁅C, X⁆ ⊔ C) :=
      Commuting.sup_left (Commuting.sup_right (hR.commuting_self hER) hsp.2.1)
        (Commuting.sup_right hsp.2.1.symm (hR.commuting_self hCR))
    have hsup : C ⊔ conjSub C x = ⁅C, X⁆ ⊔ C := sup_eq_of_le_of_commuting hR hiso hER hCR hCR
      (hR.conjSub_mem hCR x) hsp.2.1 le_sup_right hle (Ne.symm hCx)
    have hl : conjSub C x ∈ lambdaSet R C := by
      refine ⟨⟨hR.conjSub_mem hCR x, hCx, hcomm.mono le_sup_right hle⟩, ?_⟩
      rw [hsup]
      exact (mem_lambdaSet_commutator hR hiso hCR hXR hsp).1.2
    obtain ⟨D, hD, hCD⟩ := hCo
    exact reflTransGen_of_mem_lambdaSet hR hiso hΔR hΔnorm hC hCxΔ hl ⟨D, hD, hCD⟩
      ⟨conjSub D x, hΔnorm x hxΔ D hD, Opposite.conj hCD x⟩

include hR hiso hΔR hΔnorm in
theorem reflTransGen_conjSub {A C : Subgroup G} (hA : A ∈ Δ) (hAo : ∃ D ∈ Δ, Opposite A D)
    (hAC : Relation.ReflTransGen (oppGraph Δ) A C) {g : G} (hg : g ∈ ⨆ B ∈ Δ, B) :
    Relation.ReflTransGen (oppGraph Δ) A (conjSub C g) := by
  rw [iSup_subtype'] at hg
  refine Subgroup.iSup_induction (fun X : Δ => (X : Subgroup G))
    (C := fun g => ∀ C, Relation.ReflTransGen (oppGraph Δ) A C →
      Relation.ReflTransGen (oppGraph Δ) A (conjSub C g)) hg ?_ ?_ ?_ C hAC
  · intro X x hx C hAC
    obtain ⟨hCΔ, hCo⟩ := mem_and_exists_opposite_of_reflTransGen hA hAo hAC
    exact hAC.trans (reflTransGen_conjSub_of_mem hR hiso hΔR hΔnorm hCΔ hCo X.2 hx)
  · intro C hAC
    rwa [conjSub_one]
  · intro x y hx hy C hAC
    rw [conjSub_mul]
    exact hx _ (hy C hAC)

omit [Finite G] in
include hR hΔR in
theorem exists_conjSub_eq_of_reflTransGen {A C : Subgroup G}
    (hAC : Relation.ReflTransGen (oppGraph Δ) A C) :
    ∃ g ∈ ⨆ D ∈ {D | Relation.ReflTransGen (oppGraph Δ) A D}, D, conjSub A g = C := by
  induction hAC with
  | refl => exact ⟨1, one_mem _, conjSub_one A⟩
  | tail hab hbc ih =>
    obtain ⟨g, hg, hgb⟩ := ih
    rename_i b c
    obtain ⟨y, hy, hyc⟩ := exists_mem_sup_conjSub_eq hR (hΔR hbc.1) hbc.2.2
    have hble : b ≤ ⨆ D ∈ {D | Relation.ReflTransGen (oppGraph Δ) A D}, D :=
      le_iSup₂ (f := fun D (_ : D ∈ {D | Relation.ReflTransGen (oppGraph Δ) A D}) => D) b hab
    have hcle : c ≤ ⨆ D ∈ {D | Relation.ReflTransGen (oppGraph Δ) A D}, D :=
      le_iSup₂ (f := fun D (_ : D ∈ {D | Relation.ReflTransGen (oppGraph Δ) A D}) => D) c
        (hab.tail hbc)
    refine ⟨y * g, Subgroup.mul_mem _ (sup_le hble hcle hy) hg, ?_⟩
    rw [conjSub_mul, hgb, hyc]

omit [Finite G] in
include hΔnorm in
theorem conjSub_mem_isolatedIn {E : Subgroup G} (hE : E ∈ isolatedIn Δ) {g : G}
    (hg : g ∈ ⨆ B ∈ Δ, B) : conjSub E g ∈ isolatedIn Δ := by
  refine ⟨hΔnorm g hg E hE.1, fun C hC hop => ?_⟩
  have hg' : g⁻¹ ∈ ⨆ B ∈ Δ, B := Subgroup.inv_mem _ hg
  have := Opposite.conj hop g⁻¹
  rw [← conjSub_mul, inv_mul_cancel, conjSub_one] at this
  exact hE.2 _ (hΔnorm g⁻¹ hg' C hC) this

include hR hΔR hΔnorm in
theorem isPGroup_iSup_isolatedIn : IsPGroup 2 ↥(⨆ B ∈ isolatedIn Δ, B) := by
  have hle : (⨆ B ∈ isolatedIn Δ, B) ≤ ⨆ B ∈ Δ, B :=
    iSup₂_le fun B hB => le_iSup₂ (f := fun B (_ : B ∈ Δ) => B) B hB.1
  refine isPGroup_of_forall_isPGroup_sup (fun E hE => le_iSup₂ (f := fun B
    (_ : B ∈ isolatedIn Δ) => B) E hE) le_rfl (fun E hE m hm =>
      conjSub_mem_isolatedIn hΔnorm hE (hle hm)) fun E hE F hF => ?_
  exact isPGroup_sup_of_not_opposite hR (hΔR hE.1) (hΔR hF.1) (hE.2 F hF.1)

omit [Finite G] in
theorem conjSub_iSup_isolatedIn_eq {g : G} (hg : ∀ B ∈ Δ, conjSub B g ∈ Δ)
    (hg' : ∀ B ∈ Δ, conjSub B g⁻¹ ∈ Δ) :
    conjSub (⨆ B ∈ isolatedIn Δ, B) g = ⨆ B ∈ isolatedIn Δ, B := by
  have hiso' : ∀ {h : G}, (∀ B ∈ Δ, conjSub B h ∈ Δ) → (∀ B ∈ Δ, conjSub B h⁻¹ ∈ Δ) →
      ∀ E ∈ isolatedIn Δ, conjSub E h ∈ isolatedIn Δ := by
    intro h hh hh' E hE
    refine ⟨hh E hE.1, fun C hC hop => ?_⟩
    have := Opposite.conj hop h⁻¹
    rw [← conjSub_mul, inv_mul_cancel, conjSub_one] at this
    exact hE.2 _ (hh' C hC) this
  have hginv : ∀ B ∈ Δ, conjSub B g⁻¹⁻¹ ∈ Δ := by simpa using hg
  apply le_antisymm
  · rw [conjSub, Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun E hE => ?_
    rw [← Subgroup.map_le_iff_le_comap, ← conjSub]
    exact le_iSup₂ (f := fun B (_ : B ∈ isolatedIn Δ) => B) _ (hiso' hg hg' E hE)
  · refine iSup₂_le fun E hE => ?_
    have hE' := hiso' hg' hginv E hE
    have : E = conjSub (conjSub E g⁻¹) g := by
      rw [← conjSub_mul, mul_inv_cancel, conjSub_one]
    rw [this]
    exact Subgroup.map_mono (le_iSup₂ (f := fun B (_ : B ∈ isolatedIn Δ) => B) _ hE')

include hR hiso hΔR hΔnorm in
theorem commuting_or_commutator_mem_isolatedIn
    (hΔcomm : ∀ A ∈ Δ, ∀ B ∈ Δ, Special R A B → ⁅A, B⁆ ∈ Δ) {A B : Subgroup G} (hA : A ∈ Δ)
    (hB : B ∈ Δ) (hAo : ∃ C ∈ Δ, Opposite A C) (hBo : ∃ D ∈ Δ, Opposite B D)
    (hAB : ¬ Relation.ReflTransGen (oppGraph Δ) A B) :
    Commuting A B ∨ ⁅A, B⁆ ∈ isolatedIn Δ := by
  have hAR := hΔR hA
  have hBR := hΔR hB
  have hne : A ≠ B := fun e => hAB (e ▸ Relation.ReflTransGen.refl)
  rcases hR.rel A hAR B hBR hne with h | h | h
  · exact Or.inl h
  · exact absurd (Relation.ReflTransGen.single ⟨hA, hB, h⟩) hAB
  · right
    have hEΔ := hΔcomm A hA B hB h
    refine ⟨hEΔ, fun C hC hEC => ?_⟩
    have hl := mem_lambdaSet_commutator hR hiso hAR hBR h
    have h1 := reflTransGen_of_mem_lambdaSet hR hiso hΔR hΔnorm hA hEΔ
      (mem_lambdaSet_comm h.1 hl.1) hAo ⟨C, hC, hEC⟩
    have h2 := reflTransGen_of_mem_lambdaSet hR hiso hΔR hΔnorm hB hEΔ
      (mem_lambdaSet_comm h.1 hl.2) hBo ⟨C, hC, hEC⟩
    exact hAB (h1.trans (reflTransGen_oppGraph_symm h2))

end Components

end Sec3

open Sec3

theorem component_decomposition [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    (Δ : Set (Subgroup G)) (hΔR : Δ ⊆ R)
    (hΔnorm : ∀ g ∈ (⨆ B ∈ Δ, B), ∀ B ∈ Δ, conjSub B g ∈ Δ)
    (hΔcomm : ∀ A ∈ Δ, ∀ B ∈ Δ, Special R A B → ⁅A, B⁆ ∈ Δ) :
    (IsPGroup 2 ↥(⨆ B ∈ isolatedIn Δ, B) ∧
      ∀ g : G, (∀ B ∈ Δ, conjSub B g ∈ Δ) → (∀ B ∈ Δ, conjSub B g⁻¹ ∈ Δ) →
        conjSub (⨆ B ∈ isolatedIn Δ, B) g = ⨆ B ∈ isolatedIn Δ, B) ∧
    (∀ A ∈ Δ, (∃ C ∈ Δ, Opposite A C) → ∀ C, Relation.ReflTransGen (oppGraph Δ) A C →
      (∃ g ∈ ⨆ D ∈ {D | Relation.ReflTransGen (oppGraph Δ) A D}, D, conjSub A g = C) ∧
      ∀ g ∈ ⨆ B ∈ Δ, B, Relation.ReflTransGen (oppGraph Δ) A (conjSub C g)) ∧
    (∀ A ∈ Δ, ∀ B ∈ Δ, (∃ C ∈ Δ, Opposite A C) → (∃ D ∈ Δ, Opposite B D) →
      B ∈ lambdaSet R A → Relation.ReflTransGen (oppGraph Δ) A B) ∧
    (∀ A ∈ Δ, ∀ B ∈ Δ, (∃ C ∈ Δ, Opposite A C) → (∃ D ∈ Δ, Opposite B D) →
      ¬ Relation.ReflTransGen (oppGraph Δ) A B → Commuting A B ∨ ⁅A, B⁆ ∈ isolatedIn Δ) :=
  ⟨⟨isPGroup_iSup_isolatedIn hR hΔR hΔnorm, fun _ hg hg' => conjSub_iSup_isolatedIn_eq hg hg'⟩,
    fun _ hA hAo _ hAC => ⟨exists_conjSub_eq_of_reflTransGen hR hΔR hAC,
      fun _ hg => reflTransGen_conjSub hR hiso hΔR hΔnorm hA hAo hAC hg⟩,
    fun _ hA _ hB hAo hBo hBl => reflTransGen_of_mem_lambdaSet hR hiso hΔR hΔnorm hA hB hBl hAo hBo,
    fun _ hA _ hB hAo hBo hAB =>
      commuting_or_commutator_mem_isolatedIn hR hiso hΔR hΔnorm hΔcomm hA hB hAo hBo hAB⟩

end CFSG.Timmesfeld.ARS
