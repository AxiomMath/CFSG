module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S20

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Levi

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD

open Matrix

theorem nonempty_bar2_hinf_equiv_of_leviHom_of_equiv {G A : Type} [Group G] [Finite G] [Group A]
    (P : Subgroup G) (β : ↥P →* A) (hker : IsPGroup 2 ↥β.ker) (S : Subgroup A)
    (hSR : S ≤ β.range) (hcomm : ⁅β.range, β.range⁆ ≤ S) {T : Type} [Group T] (eS : ↥S ≃* T)
    (hperf : Group.IsPerfect T) (hT : CFSG.pCore 2 T = ⊥) : Nonempty (Bar2 (Hinf P) ≃* T) := by
  haveI : Group.IsPerfect T := hperf
  haveI : Group.IsPerfect ↥S :=
    Group.IsPerfect.ofSurjective (f := eS.symm.toMonoidHom) eS.symm.surjective
  have hSperf : ⁅S, S⁆ = S := Subgroup.commutator_eq_self (H := S)
  have hSO2 : CFSG.pCore 2 ↥S = ⊥ := by
    have hmap : (CFSG.pCore 2 ↥S).map eS.toMonoidHom = ⊥ := by
      rw [CFSG.pCore_map_iso 2 eS]
      exact hT
    exact (Subgroup.map_eq_bot_iff_of_injective (H := CFSG.pCore 2 ↥S)
      (f := eS.toMonoidHom) eS.injective).mp hmap
  obtain ⟨e⟩ := nonempty_bar2_hinf_equiv_of_leviHom
    (P := P) (β := β) (hker := hker) (S := S) (hSR := hSR) (hcomm := hcomm)
    (hperf := hSperf) (hO2 := hSO2)
  exact ⟨e.trans eS⟩

theorem subgroup_pi_eq_map_mulSingle {ι : Type} [DecidableEq ι] {M : ι → Type}
    [∀ i, Group (M i)] (B : ∀ i, Subgroup (M i)) (j₀ : ι) (hB : ∀ j, j ≠ j₀ → B j = ⊥) :
    Subgroup.pi Set.univ B = (B j₀).map (MonoidHom.mulSingle M j₀) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [Subgroup.mem_map]
    refine ⟨x j₀, (Subgroup.mem_pi Set.univ).mp hx j₀ (Set.mem_univ _), ?_⟩
    funext j
    by_cases hj : j = j₀
    · subst hj
      rw [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
    · have hxj : x j = 1 := by
        have hmem := (Subgroup.mem_pi Set.univ).mp hx j (Set.mem_univ _)
        rw [hB j hj] at hmem
        simpa using hmem
      rw [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hj, hxj]
  · rintro x ⟨y, hy, rfl⟩
    change Pi.mulSingle j₀ y ∈ Subgroup.pi Set.univ B
    rw [Subgroup.mulSingle_mem_pi]
    intro _
    exact hy

theorem range_toGL_eq_bot_of_eq_one {K : Type} [Field K] {k : ℕ} (hk : k = 1) :
    (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin k) K →* GL (Fin k) K).range =
      ⊥ := by
  subst hk
  rw [Subgroup.eq_bot_iff_forall]
  rintro _ ⟨A, rfl⟩
  haveI : Subsingleton (Matrix.SpecialLinearGroup (Fin 1) K) := inferInstance
  rw [Subsingleton.elim A 1]
  simp

theorem nonempty_bar2_hinf_equiv_of_leviHom_mulSingle {G : Type} [Group G] [Finite G]
    {ι : Type} [DecidableEq ι] {M : ι → Type} [∀ i, Group (M i)] (P : Subgroup G)
    (β : ↥P →* ∀ i, M i) (hker : IsPGroup 2 ↥β.ker) (j₀ : ι) (B : ∀ i, Subgroup (M i))
    (hB : ∀ j, j ≠ j₀ → B j = ⊥) (hSR : ∀ y ∈ B j₀, Pi.mulSingle j₀ y ∈ β.range)
    (hcomm : ⁅β.range, β.range⁆ ≤ Subgroup.pi Set.univ B) {T : Type} [Group T]
    (eS : ↥(B j₀) ≃* T) (hperf : Group.IsPerfect T) (hT : CFSG.pCore 2 T = ⊥) :
    Nonempty (Bar2 (Hinf P) ≃* T) := by
  classical
  let f : M j₀ →* (∀ i, M i) := MonoidHom.mulSingle M j₀
  let S : Subgroup (∀ i, M i) := (B j₀).map f
  have hSeq : Subgroup.pi Set.univ B = S := subgroup_pi_eq_map_mulSingle B j₀ hB
  have hcommS : ⁅β.range, β.range⁆ ≤ S := by
    rw [← hSeq]
    exact hcomm
  have hSR' : S ≤ β.range := by
    rintro x ⟨y, hy, rfl⟩
    exact hSR y hy
  have hinj : Function.Injective f := Pi.mulSingle_injective j₀
  let eB : ↥S ≃* ↥(B j₀) := ((B j₀).equivMapOfInjective f hinj).symm
  let eS' : ↥S ≃* T := eB.trans eS
  exact nonempty_bar2_hinf_equiv_of_leviHom_of_equiv P β hker S hSR' hcommS eS' hperf hT

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD
