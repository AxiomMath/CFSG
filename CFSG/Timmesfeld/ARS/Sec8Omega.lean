module

public import CFSG.Timmesfeld.ARS.Sec8Regular

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

theorem exists_conjSub_eq_of_le_sup_of_mem_psiSet [Finite G] (hR : IsRootClass R)
    (hiso : NoIsolated R) {A B E X : Subgroup G} (hA : A ∈ R) (hB : B ∈ R) (hAB : Opposite A B)
    (hEl : E ∈ lambdaSet R B) (hEψ : E ∈ psiSet R A) (hX : X ∈ R) (hXle : X ≤ B ⊔ E)
    (hXE : X ≠ E) : ∃ f ∈ ⁅A, E⁆, conjSub B f = X := by
  have hset := Sec3.setOf_mem_le_sup_eq hR hiso hB hA hAB.symm hEl hEψ
  have hmem : X ∈ {D | D ∈ R ∧ D ≤ B ⊔ E} := ⟨hX, hXle⟩
  rw [hset] at hmem
  rcases hmem with h1 | ⟨⟨n, hn⟩, rfl⟩
  · exact absurd h1 hXE
  obtain ⟨e, he, f, hf, rfl⟩ := (Sec3.mem_sup_commutator_iff hEψ).1 hn
  refine ⟨f, hf, ?_⟩
  change conjSub B f = conjSub B (e * f)
  rw [← (hEψ.2.2.2 f hf e he).eq, conjSub_mul,
    conjSub_of_forall_commute fun b hb => (hEl.1.2.2 b hb e he).symm]

namespace OmegaGraph

abbrev omegaAdj (R : Set (Subgroup G)) (A E F : Subgroup G) : Prop :=
  E ∈ omegaSet R A ∧ F ∈ omegaSet R A ∧ F ∈ lambdaSet R E

abbrev component (R : Set (Subgroup G)) (A B₀ : Subgroup G) : Set (Subgroup G) :=
  {E | Relation.ReflTransGen (omegaAdj R A) B₀ E}

theorem omegaAdj_symm {A E F : Subgroup G} (h : omegaAdj R A E F) : omegaAdj R A F E :=
  ⟨h.2.1, h.1, mem_lambdaSet_comm h.1.1 h.2.2⟩

theorem reflTransGen_symm {A E F : Subgroup G}
    (h : Relation.ReflTransGen (omegaAdj R A) E F) :
    Relation.ReflTransGen (omegaAdj R A) F E := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hEF ih => exact Relation.ReflTransGen.head (omegaAdj_symm hEF) ih

theorem mem_omegaSet_of_reflTransGen {A B E : Subgroup G} (hB : B ∈ omegaSet R A)
    (h : Relation.ReflTransGen (omegaAdj R A) B E) : E ∈ omegaSet R A := by
  induction h with
  | refl => exact hB
  | tail _ hEF _ => exact hEF.2.1

theorem omegaAdj_conj (hR : IsRootClass R) {A E F : Subgroup G} {g : G} (hg : conjSub A g = A)
    (h : omegaAdj R A E F) : omegaAdj R A (conjSub E g) (conjSub F g) := by
  have hconj : ∀ {X : Subgroup G}, X ∈ omegaSet R A → conjSub X g ∈ omegaSet R A := fun hX =>
    ⟨hR.conjSub_mem hX.1 g, hg ▸ Opposite.conj hX.2 g⟩
  exact ⟨hconj h.1, hconj h.2.1, conjSub_mem_lambdaSet hR h.2.2 g⟩

theorem reflTransGen_conj (hR : IsRootClass R) {A E F : Subgroup G} {g : G}
    (hg : conjSub A g = A) (h : Relation.ReflTransGen (omegaAdj R A) E F) :
    Relation.ReflTransGen (omegaAdj R A) (conjSub E g) (conjSub F g) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hEF ih => exact Relation.ReflTransGen.tail ih (omegaAdj_conj hR hg hEF)

theorem conjSub_mem_component (hR : IsRootClass R) {A B₀ B E : Subgroup G} {g : G}
    (hg : conjSub A g = A) (hB : B ∈ component R A B₀) (hBg : conjSub B g ∈ component R A B₀)
    (hE : E ∈ component R A B₀) : conjSub E g ∈ component R A B₀ :=
  Relation.ReflTransGen.trans hBg
    (reflTransGen_conj hR hg (Relation.ReflTransGen.trans (reflTransGen_symm hB) hE))

variable (h : Hyp G R)
include h

theorem exists_mem_M_conjSub_eq {A E F : Subgroup G} (hA : A ∈ R) (hEF : omegaAdj R A E F) :
    ∃ m ∈ M R A, conjSub E m = F := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  obtain ⟨⟨hER, hAE⟩, ⟨hFR, hAF⟩, hFl⟩ := hEF
  obtain ⟨D, ⟨hDR, hDle, hDψ⟩, -⟩ := existsUnique_mem_psiSet_of_le hR hiso hER hA hAE.symm hFl
  have hDE : E ≠ D := fun e => Special.not_opposite hR hA hDψ.2 (e ▸ hAE)
  have hFD : F ≠ D := fun e => Special.not_opposite hR hA hDψ.2 (e ▸ hAF)
  obtain ⟨hDl, hsup⟩ := mem_lambdaSet_of_le_sup hR hiso hER hFl hER le_sup_left hDR hDle hDE
  obtain ⟨f, hf, hEf⟩ := exists_conjSub_eq_of_le_sup_of_mem_psiSet hR hiso hA hER hAE hDl hDψ
    hFR (hsup ▸ le_sup_right) hFD
  have hTl : ⁅A, D⁆ ∈ lambdaSet R A :=
    mem_lambdaSet_comm hDψ.2.1 (mem_lambdaSet_commutator hR hiso hA hDR hDψ.2).1
  exact ⟨f, QD.le_M hTl hf, hEf⟩

theorem exists_mem_M_conjSub_eq_of_reflTransGen {A B E : Subgroup G} (hA : A ∈ R)
    (hBE : Relation.ReflTransGen (omegaAdj R A) B E) : ∃ m ∈ M R A, conjSub B m = E := by
  induction hBE with
  | refl => exact ⟨1, one_mem _, conjSub_one _⟩
  | tail _ hEF ih =>
    obtain ⟨m₁, hm₁, rfl⟩ := ih
    obtain ⟨m₂, hm₂, rfl⟩ := exists_mem_M_conjSub_eq h hA hEF
    exact ⟨m₂ * m₁, Subgroup.mul_mem _ hm₂ hm₁, conjSub_mul _ _ _⟩

theorem M_le_stabSet {A B₀ : Subgroup G} (hA : A ∈ R) (hB₀ : B₀ ∈ omegaSet R A) :
    M R A ≤ stabSet (component R A B₀) := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  rw [M_eq_gen_lambdaStar h hA hB₀]
  refine gen_le fun C hC c hc => ?_
  have hCR : C ∈ R := hC.1.1.1
  have hcA : conjSub A c = A := conjSub_of_forall_commute fun a ha => (hC.1.1.2.2 a ha c hc).symm
  refine mem_stabSet_of_mul_self (hR.mul_self C hCR c hc) fun E hE => ?_
  refine conjSub_mem_component hR hcA Relation.ReflTransGen.refl ?_ hE
  rcases eq_or_ne c 1 with rfl | hc1
  · rw [conjSub_one]
    exact Relation.ReflTransGen.refl
  · refine Relation.ReflTransGen.single ⟨hB₀, ⟨hR.conjSub_mem hB₀.1 c, ?_⟩, ?_⟩
    · rw [← hcA]
      exact Opposite.conj hB₀.2 c
    · exact QD.conjSub_mem_lambdaSet_of_special hR hiso hCR hB₀.1 hC.2.2.symm hc hc1

theorem mem_component_iff {A B₀ E : Subgroup G} (hA : A ∈ R) (hB₀ : B₀ ∈ omegaSet R A) :
    E ∈ component R A B₀ ↔ ∃ m ∈ M R A, conjSub B₀ m = E := by
  refine ⟨exists_mem_M_conjSub_eq_of_reflTransGen h hA, ?_⟩
  rintro ⟨m, hm, rfl⟩
  exact conjSub_mem_of_mem_stabSet (M_le_stabSet h hA hB₀ hm) Relation.ReflTransGen.refl

theorem mem_component_of_subset {A C B₀ B E : Subgroup G} (hA : A ∈ R) (hC : C ∈ R)
    (hB₀ : B₀ ∈ omegaSet R A) (hsub : component R A B₀ ⊆ omegaSet R C)
    (hB : B ∈ component R A B₀) (hE : E ∈ omegaSet R C) (hBE : E ∈ lambdaSet R B) :
    E ∈ component R A B₀ := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hBΩ : B ∈ omegaSet R A := mem_omegaSet_of_reflTransGen hB₀ hB
  by_cases hEA : E ∈ omegaSet R A
  · exact Relation.ReflTransGen.tail hB ⟨hBΩ, hEA, hBE⟩
  exfalso
  have hER : E ∈ R := hE.1
  have hAE : Special R A E := by
    have hnc := not_commuting_of_opposite_of_mem_lambdaSet hR hA hBΩ.2 hBE
    have hne : A ≠ E := fun e => hnc (e ▸ hR.commuting_self hA)
    rcases hR.rel A hA E hER hne with hc | ho | hs
    · exact absurd hc hnc
    · exact absurd ⟨hER, ho⟩ hEA
    · exact hs
  have hBC : B ∈ omegaSet R C := hsub hB
  obtain ⟨D, ⟨hDR, hDle, hDψ⟩, -⟩ := existsUnique_mem_psiSet_of_le hR hiso hBΩ.1 hC hBC.2.symm hBE
  have hDE : D ≠ E := fun e => Special.not_opposite hR hC hDψ.2 (e ▸ hE.2)
  have hDB : D ≠ B := fun e => Special.not_opposite hR hC hDψ.2 (e ▸ hBC.2)
  obtain ⟨f, hf, hBf⟩ := exists_conjSub_eq_of_le_sup_of_mem_psiSet hR hiso hA hBΩ.1 hBΩ.2 hBE
    ⟨hER, hAE⟩ hDR hDle hDE
  have hfA : conjSub A f = A := conjSub_of_forall_commute fun a ha => hAE.2.1 f hf a ha
  have hDA : D ∈ omegaSet R A := ⟨hDR, by rw [← hfA, ← hBf]; exact Opposite.conj hBΩ.2 f⟩
  have hDl : D ∈ lambdaSet R B :=
    (mem_lambdaSet_of_le_sup hR hiso hBΩ.1 hBE hBΩ.1 le_sup_left hDR hDle hDB.symm).1
  exact Special.not_opposite hR hC hDψ.2 (hsub (Relation.ReflTransGen.tail hB ⟨hBΩ, hDA, hDl⟩)).2

theorem component_eq_of_subset {A C B₀ : Subgroup G} (hA : A ∈ R) (hC : C ∈ R)
    (hB₀ : B₀ ∈ omegaSet R A) (hsub : component R A B₀ ⊆ omegaSet R C) :
    component R C B₀ = component R A B₀ := by
  ext E
  constructor
  · intro hE
    induction hE with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hEF ih => exact mem_component_of_subset h hA hC hB₀ hsub ih hEF.2.1 hEF.2.2
  · intro hE
    induction hE with
    | refl => exact Relation.ReflTransGen.refl
    | tail hpath hEF ih =>
      exact Relation.ReflTransGen.tail ih ⟨hsub hpath, hsub (hpath.tail hEF), hEF.2.2⟩

theorem centralSet_le_stabSet {A B₀ C : Subgroup G} (hA : A ∈ R) (hB₀ : B₀ ∈ omegaSet R A)
    (hC : C ∈ centralSet R A) : C ≤ stabSet (component R A B₀) := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  intro c hc
  have hcA : conjSub A c = A := conjSub_of_forall_commute fun a ha => (hC.2 a ha c hc).symm
  refine mem_stabSet_of_mul_self (hR.mul_self C hC.1 c hc) fun E hE => ?_
  by_contra hEc
  have hout : ∀ B ∈ component R A B₀, conjSub B c ∉ component R A B₀ := fun B hB hBc =>
    hEc (conjSub_mem_component hR hcA hB hBc hE)
  have hc1 : c ≠ 1 := by
    rintro rfl
    exact hEc (by rwa [conjSub_one])
  have hsub : component R A B₀ ⊆ omegaSet R C := by
    intro B hB
    have hBΩ := mem_omegaSet_of_reflTransGen hB₀ hB
    have hBC : B ≠ C := fun e => hBΩ.2.not_commuting (hR.ne_bot A hA) (e ▸ hC.2)
    rcases hR.rel B hBΩ.1 C hC.1 hBC with hcm | ho | hs
    · exact absurd (by rwa [conjSub_of_forall_commute fun b hb => (hcm b hb c hc).symm]) (hout B hB)
    · exact ⟨hBΩ.1, ho.symm⟩
    · refine absurd (Relation.ReflTransGen.tail hB ⟨hBΩ, ⟨hR.conjSub_mem hBΩ.1 c, ?_⟩, ?_⟩)
        (hout B hB)
      · rw [← hcA]
        exact Opposite.conj hBΩ.2 c
      · exact QD.conjSub_mem_lambdaSet_of_special hR hiso hC.1 hBΩ.1 hs.symm hc hc1
  have hB₀C : B₀ ∈ omegaSet R C := hsub Relation.ReflTransGen.refl
  have hstab := M_le_stabSet h hC.1 hB₀C (QD.le_M_self hc)
  rw [component_eq_of_subset h hA hC.1 hB₀ hsub] at hstab
  exact hEc (conjSub_mem_of_mem_stabSet hstab hE)

theorem mem_component_of_commuting {A B₀ B C : Subgroup G} (hA : A ∈ R)
    (hB₀ : B₀ ∈ omegaSet R A) (hB : B ∈ component R A B₀) (hC : C ∈ omegaSet R A)
    (hBC : Commuting B C) : C ∈ component R A B₀ := by
  have hR := h.root
  have hBΩ := mem_omegaSet_of_reflTransGen hB₀ hB
  obtain ⟨E, hE, -, hAE, e, he, a, ha, hae⟩ :=
    exists_conjSub_eq_of_opposite_opposite hR hBΩ.1 hA hC.1 hBΩ.2.symm hC.2 hBC
  rw [← hae, conjSub_mul]
  have h1 := conjSub_mem_of_mem_stabSet (centralSet_le_stabSet h hA hB₀ ⟨hE, hAE⟩ he) hB
  exact conjSub_mem_of_mem_stabSet (M_le_stabSet h hA hB₀ (QD.le_M_self ha)) h1

end OmegaGraph

end CFSG.Timmesfeld.ARS
