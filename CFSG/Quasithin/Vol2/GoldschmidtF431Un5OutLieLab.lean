module

public import CFSG.Quasithin.Vol2.GoldschmidtF431AGLie
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpLift
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieF
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModU5

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL5

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.Quasithin.H13.Sec53F.Unit CFSG.Quasithin.H13.F431.Un
  CFSG.Quasithin.H13.F431 CFSG.Quasithin CFSG.QuasithinUnique

theorem lab5_isCoatom_map {Y : Type*} [Group Y] (e : Y ≃* Y) {B : Subgroup Y} (hB : IsCoatom B) :
    IsCoatom (B.map e.toMonoidHom) := by
  have c1 : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id Y := by ext x; simp
  have c2 : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id Y := by ext x; simp
  refine ⟨fun htop => hB.1 ?_, fun C hC => ?_⟩
  · have := congrArg (Subgroup.map e.symm.toMonoidHom) htop
    rwa [Subgroup.map_map, c1, Subgroup.map_id,
      Subgroup.map_top_of_surjective _ e.symm.surjective] at this
  · have h1 : B < C.map e.symm.toMonoidHom := by
      refine lt_of_le_of_ne ?_ fun hEq => hC.ne ?_
      · have := Subgroup.map_mono (f := e.symm.toMonoidHom) hC.le
        rwa [Subgroup.map_map, c1, Subgroup.map_id] at this
      · rw [hEq, Subgroup.map_map, c2, Subgroup.map_id]
    have h2 := hB.2 _ h1
    have := congrArg (Subgroup.map e.toMonoidHom) h2
    rwa [Subgroup.map_map, c2, Subgroup.map_id,
      Subgroup.map_top_of_surjective _ e.surjective] at this

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

include h in
theorem lab5_map_eq {g : MulAut (hypPSU h 2 1)} (hg : g ∈ autStab (hypProjUnitriangular h 2 1))
    {B : Subgroup (hypPSU h 2 1)} (hB : IsCoatom B)
    (hBN : Subgroup.normalizer (hypProjUnitriangular h 2 1 : Set (hypPSU h 2 1)) ≤ B) :
    B.map g.toMonoidHom = u5PtP h ∨ B.map g.toMonoidHom = u5LnP h := by
  have hY := u5_yamStd (h := h)
  have hU : (hypProjUnitriangular h 2 1).map g.toMonoidHom = hypProjUnitriangular h 2 1 :=
    (AG.mem_autStab_iff_map_eq g _).1 hg
  have hNB : Subgroup.normalizer (hypProjUnitriangular h 2 1 : Set (hypPSU h 2 1)) ≤
      B.map g.toMonoidHom := by
    intro x hx
    have hx' : g⁻¹ x ∈ Subgroup.normalizer
        ((hypProjUnitriangular h 2 1 : Subgroup (hypPSU h 2 1)) : Set (hypPSU h 2 1)) := by
      rw [← hU, ← Subgroup.map_equiv_normalizer_eq] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      simpa [hU] using hy
    exact ⟨g⁻¹ x, hBN hx', by simp⟩
  have hco := lab5_isCoatom_map g hB
  rcases hY.above _ hNB hco.1 with h1 | h1
  · rcases hco.le_iff.1 h1 with h2 | h2
    · exact absurd h2 hY.coatom₀.1
    · exact Or.inl h2.symm
  · rcases hco.le_iff.1 h1 with h2 | h2
    · exact absurd h2 hY.coatom₁.1
    · exact Or.inr h2.symm

include h in
theorem autStab_U_le_Pt (hf : 2 ≤ f) {g : MulAut (hypPSU h 2 1)}
    (hg : g ∈ autStab (hypProjUnitriangular h 2 1)) : g ∈ autStab (u5PtP h) := by
  have := h.finite
  have : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  have hY := u5_yamStd (h := h)
  refine (AG.mem_autStab_iff_map_eq g _).2 ?_
  rcases lab5_map_eq h hg hY.coatom₀ hY.le₀ with h1 | h1
  · exact h1
  · exfalso
    have hz := z5Y_mem_centerOf (h := h) hf
    have h2 : g (z5Y h) ∈ centerOf (perfectCore (u5LnP h)) := by
      rw [← h1, perfectCore_map_of_injective g.toMonoidHom g.injective,
        centerOf_map_of_injective g.toMonoidHom g.injective]
      exact Subgroup.mem_map_of_mem _ hz
    rw [centerOf_u5LnP_eq_bot hf, Subgroup.mem_bot] at h2
    exact z5Y_ne_one (g.injective (h2.trans (map_one g).symm))

include h in
theorem autStab_U_le_Ln (hf : 2 ≤ f) {g : MulAut (hypPSU h 2 1)}
    (hg : g ∈ autStab (hypProjUnitriangular h 2 1)) : g ∈ autStab (u5LnP h) := by
  have := h.finite
  have hY := u5_yamStd (h := h)
  refine (AG.mem_autStab_iff_map_eq g _).2 ?_
  rcases lab5_map_eq h hg hY.coatom₁ hY.le₁ with h1 | h1
  · exfalso
    have hgi := (autStab_U_le_Pt h hf ((autStab _).inv_mem hg))
    have h3 : (u5PtP h).map (g⁻¹).toMonoidHom = u5PtP h := (AG.mem_autStab_iff_map_eq _ _).1 hgi
    have h4 : ((u5LnP h).map g.toMonoidHom).map (g⁻¹).toMonoidHom = u5LnP h := by
      rw [Subgroup.map_map]
      have : (g⁻¹).toMonoidHom.comp g.toMonoidHom = MonoidHom.id _ := by
        ext x; simp
      rw [this, Subgroup.map_id]
    rw [h1, h3] at h4
    exact hY.ne h4
  · exact h1

end CFSG.Quasithin.H13.F431.Un.OL5
